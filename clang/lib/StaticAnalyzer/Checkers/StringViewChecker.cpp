// StringViewChecker.cpp - C++ --------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// FIXME: Add docs.
// TODO: Support returning the view object itself.
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

REGISTER_SET_WITH_PROGRAMSTATE(ReleasedViews, const MemRegion *)

namespace {

class StringViewChecker
    : public Checker<check::Location, check::PreCall,
                     check::PreStmt<ReturnStmt>, check::EndFunction,
                     check::PointerEscape, check::DeadSymbols> {

  using HandlerFn = void (StringViewChecker::*)(const CXXInstanceCall *,
                                                CheckerContext &) const;

  // FIXME: Should using capacity checking methods be considered an error
  // after a view is released?
  CallDescriptionMap<HandlerFn> ViewHandlers{
      // Iterators
      {{{"std", "basic_string_view", "begin"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "cbegin"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "end"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "cend"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "rbegin"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "crbegin"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "rend"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "crend"}}, &StringViewChecker::checkUse},

      // Element access
      {{{"std", "basic_string_view", "at"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "front"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "back"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "data"}}, &StringViewChecker::checkUse},

      // Modifiers
      {{{"std", "basic_string_view", "remove_prefix"}},
       &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "remove_suffix"}},
       &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "swap"}}, &StringViewChecker::checkUse},

      // Operations
      {{{"std", "basic_string_view", "copy"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "substr"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "compare"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "starts_with"}},
       &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "ends_with"}},
       &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "find"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "rfind"}}, &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "find_first_of"}},
       &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "find_last_of"}},
       &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "find_first_not_of"}},
       &StringViewChecker::checkUse},
      {{{"std", "basic_string_view", "find_last_not_of"}},
       &StringViewChecker::checkUse},
  };

  void reportUseAfterFree(CheckerContext &C, const MemRegion *View) const;
  void checkEscapeOnReturn(const ReturnStmt *S, CheckerContext &C) const;
  void checkUse(const CXXInstanceCall *ICall, CheckerContext &C) const;

public:
  class StringViewBRVisitor : public BugReporterVisitor {
    const MemRegion *Sym;

  public:
    StringViewBRVisitor(const MemRegion *Sym) : Sym(Sym) {}

    static void *getTag() {
      static int Tag = 0;
      return &Tag;
    }

    void Profile(llvm::FoldingSetNodeID &ID) const override {
      ID.AddPointer(getTag());
    }

    virtual PathDiagnosticPieceRef
    VisitNode(const ExplodedNode *N, BugReporterContext &BRC,
              PathSensitiveBugReport &BR) override;
  };

  BugType DanglingViewBugTy{this, "Dangling string view",
                            "C++ std::string_view"};

  void checkLocation(SVal V, bool isLoad, const Stmt *S,
                     CheckerContext &C) const;
  void checkPreStmt(const ReturnStmt *S, CheckerContext &C) const;
  void checkEndFunction(const ReturnStmt *S, CheckerContext &C) const;
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;
  ProgramStateRef checkPointerEscape(ProgramStateRef State,
                                     const InvalidatedSymbols &Escaped,
                                     const CallEvent *Call,
                                     PointerEscapeKind Kind) const;
  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const override;
};

} // end of anonymous namespace

void StringViewChecker::printState(raw_ostream &Out, ProgramStateRef State,
                                   const char *NL, const char *Sep) const {
  const ReleasedViewsTy &Set = State->get<ReleasedViews>();
  if (!Set.isEmpty()) {
    Out << Sep << "Released views:" << NL;
    for (const MemRegion *View : Set) {
      View->dumpToStream(Out);
      Out << ", ";
    }
  }
}

void StringViewChecker::checkLocation(SVal V, bool isLoad, const Stmt *S,
                                      CheckerContext &C) const {
  if (const MemRegion *Region = V.getAsRegion()) {
    if (C.getState()->contains<ReleasedViews>(Region))
      reportUseAfterFree(C, Region);
  }
  /*
  if (auto Sym = V.getAs<nonloc::SymbolVal>()) {
    SymbolRef View = Sym->getSymbol();
    if (C.getState()->contains<ReleasedViews>(View))
      reportUseAfterFree(C, View);
  }*/
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
  /*
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
  }*/
}

void StringViewChecker::checkPreCall(const CallEvent &Call,
                                     CheckerContext &C) const {
  const auto *ICall = dyn_cast<CXXInstanceCall>(&Call);
  if (!ICall)
    return;

  const auto *MD = dyn_cast<CXXMethodDecl>(Call.getDecl());
  if (MD && MD->getNameAsString() == "operator[]") {
    checkUse(ICall, C);
    return;
  }

  const auto *Handler = ViewHandlers.lookup(Call);
  if (!Handler)
    return;

  (this->**Handler)(ICall, C);
}

void StringViewChecker::checkUse(const CXXInstanceCall *Call,
                                 CheckerContext &C) const {
  const MemRegion *View = Call->getCXXThisVal().getAsRegion();
  if (!View)
    return;

  ProgramStateRef State = C.getState();

  /*
  StoreManager &StoreMgr = C.getStoreManager();

  auto ViewVal = StoreMgr.getDefaultBinding(State->getStore(), ViewRegion);
  if (!ViewVal)
    return;

  SymbolRef View = ViewVal.getValue().getAsSymbol(true);
  */
  if (State->contains<ReleasedViews>(View)) {
    reportUseAfterFree(C, View);
  }
}

void StringViewChecker::checkDeadSymbols(SymbolReaper &SymReaper,
                                         CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  const ReleasedViewsTy &Set = State->get<ReleasedViews>();

  for (const MemRegion *View : Set) {
    if (!SymReaper.isLiveRegion(View))
      State = State->remove<ReleasedViews>(View);
  }

  C.addTransition(State);
}

ProgramStateRef StringViewChecker::checkPointerEscape(
    ProgramStateRef State, const InvalidatedSymbols &Escaped,
    const CallEvent *Call, PointerEscapeKind Kind) const {
  return State;
}

void StringViewChecker::reportUseAfterFree(CheckerContext &C,
                                           const MemRegion *View) const {
  ExplodedNode *N = C.generateErrorNode();
  if (!N)
    return;

  llvm::SmallString<128> Str;
  llvm::raw_svector_ostream OS(Str);
  OS << "Inner pointer of container used after re/deallocation";

  auto R =
      std::make_unique<PathSensitiveBugReport>(DanglingViewBugTy, OS.str(), N);
  R->addVisitor(std::make_unique<StringViewBRVisitor>(View));
  R->addVisitor(innerptr::getStringModelingBRVisitor(View));
  C.emitReport(std::move(R));
}

PathDiagnosticPieceRef
StringViewChecker::StringViewBRVisitor::VisitNode(const ExplodedNode *N,
                                                  BugReporterContext &BRC,
                                                  PathSensitiveBugReport &BR) {
  ProgramStateRef State = N->getState();
  ProgramStateRef PrevState = N->getFirstPred()->getState();

  if (!State->contains<ReleasedViews>(Sym) ||
      PrevState->contains<ReleasedViews>(Sym))
    return nullptr;

  const Stmt *S = N->getStmtForDiagnostics();
  const LocationContext *LC = N->getLocationContext();

  const MemRegion *String = innerptr::getStringForRegion(PrevState, Sym);
  assert(String && "String not found in ViewMap");
  QualType StringTy = dyn_cast<TypedValueRegion>(String)->getValueType();

  std::unique_ptr<StackHintGeneratorForSymbol> StackHint = nullptr;
  SmallString<256> Buf;
  llvm::raw_svector_ostream OS(Buf);
  OS << "Inner buffer of '" << StringTy.getAsString() << "' ";

  if (N->getLocation().getKind() == ProgramPoint::PostImplicitCallKind) {
    OS << "deallocated by call to destructor";
    //StackHint = std::make_unique<StackHintGeneratorForSymbol>(
    //    Sym, "Returning; inner buffer was deallocated");
  } else {
    OS << "reallocated by call to '";
    if (const auto *MemCallE = dyn_cast<CXXMemberCallExpr>(S)) {
      OS << MemCallE->getMethodDecl()->getDeclName();
    } else if (const auto *OpCallE = dyn_cast<CXXOperatorCallExpr>(S)) {
      OS << OpCallE->getDirectCallee()->getDeclName();
    } else if (const auto *CallE = dyn_cast<CallExpr>(S)) {
      auto &CEMgr = BRC.getStateManager().getCallEventManager();
      CallEventRef<> Call = CEMgr.getSimpleCall(CallE, State, LC);
      if (const auto *D = dyn_cast_or_null<NamedDecl>(Call->getDecl()))
        OS << D->getDeclName();
      else
        OS << "unknown";
    }
    OS << "'";
    //StackHint = std::make_unique<StackHintGeneratorForSymbol>(
    //    Sym, "Returning; inner buffer was reallocated");
  }

  PathDiagnosticLocation Pos;
  if (!S) {
    auto PIC = N->getLocation().getAs<PostImplicitCall>();
    if (!PIC)
      return nullptr;
    Pos = PathDiagnosticLocation(PIC->getLocation(), BRC.getSourceManager());
  } else {
    Pos = PathDiagnosticLocation(S, BRC.getSourceManager(), LC);
  }

  auto P = std::make_shared<PathDiagnosticEventPiece>(Pos, OS.str(), true);
  BR.addCallStackHint(P, std::move(StackHint));
  return P;
}

namespace clang {
namespace ento {
namespace allocation_state {

ProgramStateRef markViewReleased(ProgramStateRef State, const MemRegion *View) {
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
