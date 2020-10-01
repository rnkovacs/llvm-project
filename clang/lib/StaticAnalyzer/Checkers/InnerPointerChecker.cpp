//=== InnerPointerChecker.cpp -------------------------------------*- C++ -*--//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines a check that marks a raw pointer to a C++ container's
// inner buffer released when the object is destroyed. This information can
// be used by MallocChecker to detect use-after-free problems.
//
//===----------------------------------------------------------------------===//

#include "AllocationState.h"
#include "InnerPtr.h"
#include "InterCheckerAPI.h"

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/BugReporter/CommonBugCategories.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

// Associate container objects with a set of raw pointer symbols.
REGISTER_MAP_WITH_PROGRAMSTATE(RawPtrMap, const MemRegion *, SymbolRef)

namespace {

class InnerPointerChecker
    : public Checker<check::DeadSymbols, check::PostCall> {

  CallDescription AppendFn, AssignFn, ClearFn, CStrFn, DataFn, EraseFn,
      InsertFn, PopBackFn, PushBackFn, ReplaceFn, ReserveFn, ResizeFn,
      ShrinkToFitFn, SwapFn;

public:
  class InnerPointerBRVisitor : public BugReporterVisitor {
    SymbolRef Sym;

  public:
    InnerPointerBRVisitor(SymbolRef Sym) : Sym(Sym) {}

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

    // FIXME: Scan the map once in the visitor's constructor and do a direct
    // lookup by region.
    bool isSymbolTracked(ProgramStateRef State, SymbolRef Sym) {
      RawPtrMapTy Map = State->get<RawPtrMap>();
      for (const auto &Entry : Map) {
        if (Entry.second == Sym)
          return true;
      }
      return false;
    }
  };

  InnerPointerChecker()
      : AppendFn({"std", "basic_string", "append"}),
        AssignFn({"std", "basic_string", "assign"}),
        ClearFn({"std", "basic_string", "clear"}),
        CStrFn({"std", "basic_string", "c_str"}),
        DataFn({"std", "basic_string", "data"}),
        EraseFn({"std", "basic_string", "erase"}),
        InsertFn({"std", "basic_string", "insert"}),
        PopBackFn({"std", "basic_string", "pop_back"}),
        PushBackFn({"std", "basic_string", "push_back"}),
        ReplaceFn({"std", "basic_string", "replace"}),
        ReserveFn({"std", "basic_string", "reserve"}),
        ResizeFn({"std", "basic_string", "resize"}),
        ShrinkToFitFn({"std", "basic_string", "shrink_to_fit"}),
        SwapFn({"std", "basic_string", "swap"}) {}

  /// Check whether the called member function potentially invalidates
  /// pointers referring to the container object's inner buffer.
  bool isInvalidatingMemberFunction(const CallEvent &Call) const;

  /// Mark pointer symbols associated with the given memory region released
  /// in the program state.
  void markPtrSymbolReleased(const CallEvent &Call, ProgramStateRef State,
                             const MemRegion *ObjRegion,
                             CheckerContext &C) const;

  /// Standard library functions that take a non-const `basic_string` argument
  /// by reference may invalidate its inner pointers. Check for these cases and
  /// mark the pointers released.
  void checkFunctionArguments(const CallEvent &Call, ProgramStateRef State,
                              CheckerContext &C) const;

  /// Record the connection between raw pointers referring to a container
  /// object's inner buffer and the object's memory region in the program state.
  /// Mark potentially invalidated pointers released.
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;

  /// Clean up the program state map.
  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;

  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const;
};

} // end anonymous namespace

void InnerPointerChecker::printState(raw_ostream &Out, ProgramStateRef State,
                                     const char *NL, const char *Sep) const {
  RawPtrMapTy RPM = State->get<RawPtrMap>();
  if (!RPM.isEmpty()) {
    Out << Sep << "Inner pointers:" << NL;
    for (const auto &Entry : RPM) {
      Entry.first->dumpToStream(Out);
      Out << " : ";
      Entry.second->dumpToStream(Out);
      Out << NL;
    }
  }
}

bool InnerPointerChecker::isInvalidatingMemberFunction(
    const CallEvent &Call) const {
  if (const auto *MemOpCall = dyn_cast<CXXMemberOperatorCall>(&Call)) {
    OverloadedOperatorKind Opc = MemOpCall->getOverloadedOperator();
    return Opc == OO_Equal || Opc == OO_PlusEqual;
  }
  return (isa<CXXDestructorCall>(Call) || Call.isCalled(AppendFn) ||
          Call.isCalled(AssignFn) || Call.isCalled(ClearFn) ||
          Call.isCalled(EraseFn) || Call.isCalled(InsertFn) ||
          Call.isCalled(PopBackFn) || Call.isCalled(PushBackFn) ||
          Call.isCalled(ReplaceFn) || Call.isCalled(ReserveFn) ||
          Call.isCalled(ResizeFn) || Call.isCalled(ShrinkToFitFn) ||
          Call.isCalled(SwapFn));
}

void InnerPointerChecker::markPtrSymbolReleased(const CallEvent &Call,
                                                ProgramStateRef State,
                                                const MemRegion *String,
                                                CheckerContext &C) const {
  // innerptr::markViewsReleased(State, String, C);

  if (const SymbolRef *Sym = State->get<RawPtrMap>(String)) {
    const auto *CallExpr = Call.getOriginExpr();
    // CallExpr may be null and will be stored so in MallocChecker's GDM.
    State = allocation_state::markReleased(State, *Sym, CallExpr);
    C.addTransition(State);
    //C.addTransition(State->remove<RawPtrMap>(String));
    return;
  }
}

void InnerPointerChecker::checkFunctionArguments(const CallEvent &Call,
                                                 ProgramStateRef State,
                                                 CheckerContext &C) const {
  if (const auto *FC = dyn_cast<AnyFunctionCall>(&Call)) {
    const FunctionDecl *FD = FC->getDecl();
    if (!FD || !FD->isInStdNamespace())
      return;

    for (unsigned I = 0, E = FD->getNumParams(); I != E; ++I) {
      QualType ParamTy = FD->getParamDecl(I)->getType();
      if (!ParamTy->isReferenceType() ||
          ParamTy->getPointeeType().isConstQualified())
        continue;

      // In case of member operator calls, `this` is counted as an
      // argument but not as a parameter.
      bool isaMemberOpCall = isa<CXXMemberOperatorCall>(FC);
      unsigned ArgI = isaMemberOpCall ? I + 1 : I;

      SVal Arg = FC->getArgSVal(ArgI);
      const auto *ArgRegion =
          dyn_cast_or_null<TypedValueRegion>(Arg.getAsRegion());
      if (!ArgRegion)
        continue;

      markPtrSymbolReleased(Call, State, ArgRegion, C);
    }
  }
}

// [string.require]
//
// "References, pointers, and iterators referring to the elements of a
// basic_string sequence may be invalidated by the following uses of that
// basic_string object:
//
// -- As an argument to any standard library function taking a reference
// to non-const basic_string as an argument. For example, as an argument to
// non-member functions swap(), operator>>(), and getline(), or as an argument
// to basic_string::swap().
//
// -- Calling non-const member functions, except operator[], at, front, back,
// begin, rbegin, end, and rend."

void InnerPointerChecker::checkPostCall(const CallEvent &Call,
                                        CheckerContext &C) const {
  ProgramStateRef State = C.getState();

  if (const auto *ICall = dyn_cast<CXXInstanceCall>(&Call)) {
    // TODO: Do we need these to be typed?
    const auto *ObjRegion = dyn_cast_or_null<TypedValueRegion>(
        ICall->getCXXThisVal().getAsRegion());
    if (!ObjRegion)
      return;

    // Check [string.require] / second point.
    if (isInvalidatingMemberFunction(Call)) {
      markPtrSymbolReleased(Call, State, ObjRegion, C);
      return;
    }
  }

  // Check [string.require] / first point.
  checkFunctionArguments(Call, State, C);
}

void InnerPointerChecker::checkDeadSymbols(SymbolReaper &SymReaper,
                                           CheckerContext &C) const {
  /*
  ProgramStateRef State = C.getState();
  RawPtrMapTy PtrMap = State->get<RawPtrMap>();

  for (const auto &Entry : PtrMap) {
    if (!SymReaper.isLiveRegion(Entry.first)) {
      // Due to incomplete destructor support, some dead regions might
      // remain in the program state map. Clean them up.
      State = State->remove<RawPtrMap>(Entry.first);
      continue;
    }

    const SymbolRef *Sym = State->get<RawPtrMap>(Entry.first);
    if (!SymReaper.isLive(*Sym)) {
      llvm::errs() << "Removing:\n";
      Entry.first->dump();
      llvm::errs() << "\n";
      (*Sym)->dump();
      llvm::errs() << "\nfrom RawPtrMap\n\n";
      State = State->remove<RawPtrMap>(Entry.first);
    }
  }

  C.addTransition(State);*/
}

namespace clang {
namespace ento {

namespace allocation_state {

std::unique_ptr<BugReporterVisitor> getInnerPointerBRVisitor(SymbolRef Sym) {
  return std::make_unique<InnerPointerChecker::InnerPointerBRVisitor>(Sym);
}

const MemRegion *getContainerRegion(ProgramStateRef State, SymbolRef Sym) {
  RawPtrMapTy Map = State->get<RawPtrMap>();
  for (const auto &Entry : Map) {
    if (Entry.second == Sym) {
      return Entry.first;
    }
  }
  return nullptr;
}

} // end namespace allocation_state

namespace innerptr {

bool hasSymbolFor(ProgramStateRef State, const MemRegion *String) {
  return State->get<RawPtrMap>(String);
}

SymbolRef getSymbolFor(ProgramStateRef State, const MemRegion *String) {
  const SymbolRef *Ptr = State->get<RawPtrMap>(String);
  assert(Ptr && "Region not present in RawPtrMap");
  return *Ptr;
}

ProgramStateRef setSymbolFor(CheckerContext &C, const MemRegion *String,
                             SymbolRef Sym) {
  ProgramStateRef State = C.getState();
  assert(!State->contains<RawPtrMap>(String));
  return State->set<RawPtrMap>(String, Sym);
}

} // end namespace innerptr

} // end namespace ento
} // end namespace clang

PathDiagnosticPieceRef InnerPointerChecker::InnerPointerBRVisitor::VisitNode(
    const ExplodedNode *N, BugReporterContext &BRC, PathSensitiveBugReport &) {
  if (!isSymbolTracked(N->getState(), Sym) ||
      isSymbolTracked(N->getFirstPred()->getState(), Sym))
    return nullptr;

  const Stmt *S = N->getStmtForDiagnostics();
  if (!S)
    return nullptr;

  const MemRegion *ObjRegion =
      allocation_state::getContainerRegion(N->getState(), Sym);
  const auto *TypedRegion = cast<TypedValueRegion>(ObjRegion);
  QualType ObjTy = TypedRegion->getValueType();

  SmallString<256> Buf;
  llvm::raw_svector_ostream OS(Buf);
  OS << "Pointer to inner buffer of '" << ObjTy.getAsString()
     << "' obtained here";
  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return std::make_shared<PathDiagnosticEventPiece>(Pos, OS.str(), true);
}

void ento::registerInnerPointerChecker(CheckerManager &Mgr) {
  registerInnerPointerCheckerAux(Mgr);
  Mgr.registerChecker<InnerPointerChecker>();
}

bool ento::shouldRegisterInnerPointerChecker(const CheckerManager &mgr) {
  return true;
}
