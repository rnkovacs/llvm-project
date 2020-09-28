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

namespace {

class StringModeling : public Checker<eval::Call> {
  CallDescription CStrFn, DataFn;

public:
  StringModeling()
    : CStrFn({"std", "basic_string", "c_str"}),
      DataFn({"std", "basic_string", "data"}) {}

  bool evalCall(const CallEvent &Call, CheckerContext &C) const;
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
  assert(TemplateArgs.size() >= 1 && "Invalid number of template parameters");

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

void ento::registerStringModeling(CheckerManager &Mgr) {
  // FIXME: InnerPtrChecker is a dependency!
  Mgr.registerChecker<StringModeling>();
}

bool ento::shouldRegisterStringModeling(const CheckerManager &mgr) {
  const LangOptions &LO = mgr.getLangOpts();
  return LO.CPlusPlus;
}
