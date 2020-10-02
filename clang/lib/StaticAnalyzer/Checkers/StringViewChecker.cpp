// StringViewChecker.cpp - C++ --------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// FIXME: Add docs.
//
//===----------------------------------------------------------------------===//

#include "AllocationState.h"
#include "InnerPtr.h"

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

REGISTER_SET_WITH_PROGRAMSTATE(ReleasedViews, SymbolRef)

namespace {

class StringViewChecker
    : public Checker<check::Location, check::PostCall,
                     check::PreStmt<ReturnStmt>, check::EndFunction,
                     check::PointerEscape, check::DeadSymbols> {

  void reportUseAfterFree(CheckerContext &C, SymbolRef Sym) const;
  void checkEscapeOnReturn(const ReturnStmt *S, CheckerContext &C) const;

public:
  BugType DanglingViewBugTy{this, "Dangling string view", "C++ std::string_view"};

  void checkLocation(SVal V, bool isLoad, const Stmt *S,
                     CheckerContext &C) const;
  void checkPreStmt(const ReturnStmt *S, CheckerContext &C) const;
  void checkEndFunction(const ReturnStmt *S, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;
  ProgramStateRef checkPointerEscape(ProgramStateRef State,
                                     const InvalidatedSymbols &Escaped,
                                     const CallEvent *Call,
                                     PointerEscapeKind Kind) const;
  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const;
};

} // end of anonymous namespace

void StringViewChecker::printState(raw_ostream &Out, ProgramStateRef State,
                                   const char *NL, const char *Sep) const {
  const ReleasedViewsTy &Set = State->get<ReleasedViews>();
  if (!Set.isEmpty()) {
    Out << Sep << "Released views:" << NL;
    for (const SymbolRef Sym : Set) {
      Sym->dumpToStream(Out);
      Out << ", ";
    }
  }
}

void StringViewChecker::checkLocation(SVal V, bool isLoad, const Stmt *S,
                                      CheckerContext &C) const {
  if (auto Sym = V.getAs<nonloc::SymbolVal>()) {
    SymbolRef View = Sym->getSymbol();
    if (C.getState()->contains<ReleasedViews>(View))
      reportUseAfterFree(C, View);
  }
}

void StringViewChecker::reportUseAfterFree(CheckerContext &C, SymbolRef Sym) const {
  ExplodedNode *N = C.generateErrorNode();
  if (!N)
    return;

  llvm::SmallString<128> Str;
  llvm::raw_svector_ostream OS(Str);
  OS << "Inner pointer of container used after re/deallocation";

  auto R = std::make_unique<PathSensitiveBugReport>(DanglingViewBugTy, OS.str(), N);
  R->addVisitor(innerptr::getStringModelingBRVisitor(Sym));
  C.emitReport(std::move(R));
}

void StringViewChecker::checkPreStmt(const ReturnStmt *S,
                                     CheckerContext &C) const {
  checkEscapeOnReturn(S, C);
}

void StringViewChecker::checkEndFunction(const ReturnStmt *S,
                                         CheckerContext &C) const {
  checkEscapeOnReturn(S, C);
}

void StringViewChecker::checkEscapeOnReturn(const ReturnStmt *S,
                                            CheckerContext &C) const {
  if (!S)
    return;

  const Expr *RetExpr = S->getRetValue();
  if (!RetExpr)
    return;

  SVal RetVal = C.getSVal(RetExpr);

  if (auto Sym = RetVal.getAs<nonloc::SymbolVal>()) {
    SymbolRef View = Sym->getSymbol();
    if (C.getState()->contains<ReleasedViews>(View)) {
      reportUseAfterFree(C, View);
    }
  }
}

void StringViewChecker::checkPostCall(const CallEvent &Call,
                                      CheckerContext &C) const {
  if (const auto *MemOp = dyn_cast<CXXMemberOperatorCall>(&Call)) {
    const auto *MD = dyn_cast<CXXMethodDecl>(Call.getDecl());
    if (!MD || MD->getNameAsString() != "operator[]")
      return;

    // if this is a [] call, and the this symbol is in the set, bug
    const MemRegion *ViewRegion = MemOp->getCXXThisVal().getAsRegion();
    if (!ViewRegion)
      return;

    ProgramStateRef State = C.getState();
    StoreManager &StoreMgr = C.getStoreManager();
    auto ViewVal = StoreMgr.getDefaultBinding(State->getStore(), ViewRegion);
    if (!ViewVal)
      return;

    SymbolRef View = ViewVal.getValue().getAsSymbol(true);
    if (State->contains<ReleasedViews>(View))
      reportUseAfterFree(C, View);
  }
}

void StringViewChecker::checkDeadSymbols(SymbolReaper &SymReaper,
                                         CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  const ReleasedViewsTy &Set = State->get<ReleasedViews>();

  for (const SymbolRef Sym : Set) {
    if (!SymReaper.isLive(Sym))
      State = State->remove<ReleasedViews>(Sym);
  }

  C.addTransition(State);
}


ProgramStateRef StringViewChecker::checkPointerEscape(
    ProgramStateRef State, const InvalidatedSymbols &Escaped,
    const CallEvent *Call, PointerEscapeKind Kind) const {
  return State;
}

namespace clang {
namespace ento {
namespace allocation_state {

ProgramStateRef markViewReleased(ProgramStateRef State, SymbolRef View) {
  return State->add<ReleasedViews>(View);
}

} // end namespace allocation_state
} // end namespace ento
} // end namespace clang

void ento::registerStringViewChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<StringViewChecker>();
}

bool ento::shouldRegisterStringViewChecker(const CheckerManager &mgr) {
  const LangOptions &LO = mgr.getLangOpts();
  return LO.CPlusPlus;
}
