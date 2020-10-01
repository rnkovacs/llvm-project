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

#include "AllocationState.h"
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
    : public Checker<eval::Call, check::PostStmt<DeclStmt>, check::PostCall,
                     check::LiveSymbols, check::DeadSymbols> {
  CallDescription StringCStr, StringData, ViewData;

public:
  StringModeling()
      : StringCStr({"std", "basic_string", "c_str"}),
        StringData({"std", "basic_string", "data"}),
        ViewData({"std", "basic_string_view", "data"}) {}

  bool evalCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostStmt(const DeclStmt *DS, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  void checkLiveSymbols(ProgramStateRef State, SymbolReaper &SymReaper) const;
  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;
  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const;
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

static const MemRegion *getStringFor(ProgramStateRef State, SymbolRef Target) {
  ViewMapTy Map = State->get<ViewMap>();
  for (const auto &Entry : Map) {
    for (const SymbolRef View : Entry.second) {
      if (View == Target)
        return Entry.first;
    }
  }
  return nullptr;
}

static void getPointerAndBindToCall(const CallEvent &Call,
                                    const MemRegion *String,
                                    CheckerContext &C) {
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
    return;
  }

  QualType InnerPtrTy = getInnerPointerType(Call, C);
  Ptr = SVB.conjureSymbolVal(CallExpr, LC, InnerPtrTy, C.blockCount());
  State = innerptr::setSymbolFor(C, String, Ptr.getAsSymbol());
  C.addTransition(State->BindExpr(CallExpr, LC, Ptr));
}

bool StringModeling::evalCall(const CallEvent &Call, CheckerContext &C) const {
  if (Call.isCalled(StringCStr) || Call.isCalled(StringData)) {
    const auto *MemCall = dyn_cast<CXXMemberCall>(&Call);
    const MemRegion *String = MemCall->getCXXThisVal().getAsRegion();
    if (!String)
      return false;

    getPointerAndBindToCall(Call, String, C);
    return true;
  }

  if (Call.isCalled(ViewData)) {
    // Step 1: See if there is a string associated with this view.
    // For this, get the symbol of the view and look it up in ViewMap.
    const auto *ICall = dyn_cast<CXXInstanceCall>(&Call);
    const MemRegion *ViewRegion = ICall->getCXXThisVal().getAsRegion();
    if (!ViewRegion)
      return false;

    ProgramStateRef State = C.getState();
    StoreManager &StoreMgr = C.getStoreManager();
    auto ViewVal = StoreMgr.getDefaultBinding(State->getStore(), ViewRegion);
    if (!ViewVal)
      return false;

    // This should be a symbol that we saved in ViewMap if the view was
    // created from a string. FIXME: Is includeBaseRegions=true needed?
    SymbolRef View = ViewVal.getValue().getAsSymbol(true);
    assert(View && "View is not a symbol!");
    const MemRegion *String = getStringFor(State, View);
    if (!String)
      return false;

    // Step 2: Create or find an existing pointer symbol for this string
    // and bind it to the call expression.
    getPointerAndBindToCall(Call, String, C);
    return true;
  }

  return false;
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
/*
static bool isViewDeclFromString(const VarDecl *VD, CheckerContext &C) {
  if (!VD || !VD->hasInit())
    return false;

  CXXRecordDecl *RD = VD->getType()->getAsCXXRecordDecl();
  if (!RD || !RD->isInStdNamespace() || RD->getName() != "basic_string_view")
    return false;

  const auto *Init =
dyn_cast<CXXMemberCallExpr>(VD->getInit()->IgnoreImpCasts()); if (!Init) return
false;

  CXXRecordDecl *InitRD = Init->getRecordDecl();
  if (!InitRD || !InitRD->isInStdNamespace() || InitRD->getName() !=
"basic_string") return false;

  return true;
}*/

void StringModeling::checkPostStmt(const DeclStmt *DS,
                                   CheckerContext &C) const {
  /*
    // FIXME: Support multiple decls.
    if (!DS->isSingleDecl())
      return;

    const auto *VD = dyn_cast<VarDecl>(DS->getSingleDecl());
    if (!isViewDeclFromString(VD, C))
      return;

    ProgramStateRef State = C.getState();
    const LocationContext *LC = C.getLocationContext();

    State->dump();
    llvm::errs() << "\n\n";

    const auto *Init =
    dyn_cast<CXXMemberCallExpr>(VD->getInit()->IgnoreImpCasts());
    //llvm::errs() << Init->getNumArgs();
    State->getSVal(Init, LC).dump();

    const MemRegion *View = State->getLValue(VD, LC).getAsRegion();
  */
}

void StringModeling::checkPostCall(const CallEvent &Call,
                                   CheckerContext &C) const {
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

void StringModeling::printState(raw_ostream &Out, ProgramStateRef State,
                                const char *NL, const char *Sep) const {
  ViewMapTy Map = State->get<ViewMap>();
  if (!Map.isEmpty()) {
    Out << Sep << "View symbols:" << NL;
    for (const auto &Entry : Map) {
      Entry.first->dumpToStream(Out);
      Out << ": {";
      for (const SymbolRef View : Entry.second) {
        View->dumpToStream(Out);
        Out << ", ";
      }
      Out << "}" << NL;
    }
  }
}

void StringModeling::checkLiveSymbols(ProgramStateRef State,
                                      SymbolReaper &SymReaper) const {
  // While a view is live, make sure that the corresponding string
  // pointer symbols are also live.
  ViewMapTy Map = State->get<ViewMap>();
  for (const auto &Entry : Map) {
    for (const SymbolRef View : Entry.second) {
      if (SymReaper.isLive(View)) {
        SymReaper.markLive(innerptr::getSymbolFor(State, Entry.first));
        break;
      }
    }
  }
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
    for (const SymbolRef View : *Set)
      State = allocation_state::markViewReleased(State, View);

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
