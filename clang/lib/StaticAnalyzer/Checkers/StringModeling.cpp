// StringModeling.cpp - Model std::basic_string behavior - C++ ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines a checker that creates custom symbolic values for the
// inner pointers of a std::basic_string. This allows us to obtain the same
// symbolic value for all c_str() or data() calls on the same string (default
// behavior gives different symbols), making the analysis more precise.
//
//===----------------------------------------------------------------------===//

#include "InnerPtr.h"

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SValBuilder.h"

using namespace clang;
using namespace ento;

REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(ViewSet, SymbolRef)
REGISTER_MAP_WITH_PROGRAMSTATE(ViewMap, const MemRegion *, ViewSet)

namespace {

class StringModeling
  : public Checker<eval::Call, check::PostCall, check::DeadSymbols> {
  CallDescription CStrFn, DataFn;

public:
  StringModeling()
    : CStrFn({"std", "basic_string", "c_str"}),
      DataFn({"std", "basic_string", "data"}) {}

  bool evalCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;
};

} // end of anonymous namespace

static QualType getInnerPointerType(const CallEvent &Call, CheckerContext &C) {
  const auto *MethodDecl = dyn_cast_or_null<CXXMethodDecl>(Call.getDecl());
  if (!MethodDecl || !MethodDecl->getParent())
    return {};

  const auto *RecordDecl = MethodDecl->getParent();
  if (!RecordDecl || !RecordDecl->isInStdNamespace())
    return {};

  const auto *TSD = dyn_cast<ClassTemplateSpecializationDecl>(RecordDecl);
  if (!TSD)
    return {};

  auto TemplateArgs = TSD->getTemplateArgs().asArray();
  assert(TemplateArgs.size() >= 1 && "Invalid number of template arguments");

  auto InnerValueType = TemplateArgs[0].getAsType();
  return C.getASTContext().getPointerType(InnerValueType.getCanonicalType());
}

bool StringModeling::evalCall(const CallEvent &Call, CheckerContext &C) const {
  if (!Call.isCalled(CStrFn) && !Call.isCalled(DataFn))
    return false;

  const auto *MemCall = dyn_cast<CXXMemberCall>(&Call);
  assert(MemCall && "Call is not MemberCall after c_str/data");
  const MemRegion *String = MemCall->getCXXThisVal().getAsRegion();
  if (!String)
    return false;

  ProgramStateRef State = C.getState();
  const LocationContext *LC = C.getLocationContext();
  SValBuilder &SVB = C.getSValBuilder();

  const auto *CallExpr = Call.getOriginExpr();
  SVal Ptr;

  if (innerptr::hasSymbolFor(State, String)) {
    SymbolRef Sym = innerptr::getSymbolFor(State, String);
    MemRegionManager &MemMgr = SVB.getRegionManager();
    Ptr = loc::MemRegionVal(MemMgr.getSymbolicRegion(Sym));
    C.addTransition(State->BindExpr(CallExpr, LC, Ptr));
    return true;
  }

  QualType InnerPtrTy = getInnerPointerType(Call, C);
  Ptr = SVB.conjureSymbolVal(CallExpr, LC, InnerPtrTy, C.blockCount());
  C.addTransition(State->BindExpr(CallExpr, LC, Ptr));
  return true;
}

static bool isStringViewConversion(const CallEvent &Call) {
  const auto *CD = dyn_cast<CXXConversionDecl>(Call.getDecl());
  if (!CD || !CD->getParent())
    return false;

  const auto *RD = CD->getParent();
  if (!RD || !RD->isInStdNamespace() || RD->getName() != "basic_string")
    return false;

  const auto *II = CD->getConversionType().getBaseTypeIdentifier();
  if (!II || II->getName() != "basic_string_view")
    return false;

  return true;
}

void
StringModeling::checkPostCall(const CallEvent &Call, CheckerContext &C) const {
  if (!isStringViewConversion(Call))
    return;

  SymbolRef View = Call.getReturnValue().getAsSymbol();
  if (!View)
    return;

  const auto *ICall = dyn_cast<CXXInstanceCall>(&Call);
  if (!ICall)
    return;

  const MemRegion *String = ICall->getCXXThisVal().getAsRegion();
  if (!String)
    return;

  ProgramStateRef State = C.getState();

  ViewSet::Factory &F = State->getStateManager().get_context<ViewSet>();
  const ViewSet *OldSet = State->get<ViewMap>(String);
  ViewSet NewSet = OldSet ? *OldSet : F.getEmptySet();

  // FIXME: what does this ensure again?
  assert(C.wasInlined || !NewSet.contains(View));
  NewSet = F.add(NewSet, View);

  C.addTransition(State->set<ViewMap>(String, NewSet));
}

void StringModeling::checkDeadSymbols(SymbolReaper &SymReaper,
                                      CheckerContext &C) const {
  ProgramStateRef State = C.getState();

  ViewSet::Factory &F = State->getStateManager().get_context<ViewSet>();
  ViewMapTy Map = State->get<ViewMap>();

  for (const auto &Entry : Map) {
    if (!SymReaper.isLiveRegion(Entry.first)) {
      // Due to incomplete destructor support, some dead regions might
      // remain in the program state map. Clean them up.
      State = State->remove<ViewMap>(Entry.first);
    }
    if (const ViewSet *OldSet = State->get<ViewMap>(Entry.first)) {
      ViewSet CleanedUpSet = *OldSet;
      for (const auto Symbol : Entry.second) {
        if (!SymReaper.isLive(Symbol))
          CleanedUpSet = F.remove(CleanedUpSet, Symbol);
      }
      State = CleanedUpSet.isEmpty()
                  ? State->remove<ViewMap>(Entry.first)
                  : State->set<ViewMap>(Entry.first, CleanedUpSet);
    }
  }

  C.addTransition(State);
}

namespace clang {
namespace ento {
namespace innerptr {

void markViewsReleased(ProgramStateRef State, const MemRegion *String,
                       CheckerContext &C) {
  if (const ViewSet *Set = State->get<ViewMap>(String)) {
    for (const SymbolRef View : *Set) {
      // FIXME: send View to StringViewChecker as released
    }
    C.addTransition(State->remove<ViewMap>(String));
    return;
  }
}

} // end namespace innerptr
} // end namespace ento
} // end namespace clang

void ento::registerStringModeling(CheckerManager &Mgr) {
  // FIXME: InnerPtrChecker is a dependency?
  Mgr.registerChecker<StringModeling>();
}

bool ento::shouldRegisterStringModeling(const CheckerManager &mgr) {
  const LangOptions &LO = mgr.getLangOpts();
  return LO.CPlusPlus;
}
