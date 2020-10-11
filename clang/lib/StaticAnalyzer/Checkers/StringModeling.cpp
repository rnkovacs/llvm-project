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
// TODO: Support the assignment of a string to a view.
// TODO: Add notes to the view-view copy cases.
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

REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(SymbolSet, SymbolRef)
REGISTER_MAP_WITH_PROGRAMSTATE(CastSymbols, const MemRegion *, SymbolSet)

REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(RegionSet, const MemRegion *)
REGISTER_MAP_WITH_PROGRAMSTATE(ViewRegions, const MemRegion *, RegionSet)

namespace {

class StringModeling : public Checker<eval::Call, check::PostCall, check::Bind,
                                      check::LiveSymbols, check::DeadSymbols> {

  using HandlerFn = bool (StringModeling::*)(const CallEvent &,
                                             CheckerContext &) const;

  CallDescriptionMap<HandlerFn> StringHandlers{
      {{{"std", "basic_string", "c_str"}},
       &StringModeling::handleStringCStrData},
      {{{"std", "basic_string", "data"}},
       &StringModeling::handleStringCStrData},
      {{{"std", "basic_string_view", "data"}},
       &StringModeling::handleViewData}};

  bool handleStringCStrData(const CallEvent &Call, CheckerContext &C) const;
  bool handleViewData(const CallEvent &Call, CheckerContext &C) const;

public:
  /// Create a unique symbol for the buffer pointer of a string. Use this
  /// symbol as a result for all the relevant methods in StringHandlers.
  bool evalCall(const CallEvent &Call, CheckerContext &C) const;

  /// Step 1 of recording a view in CastSymbols: on operator string_view,
  /// save the return symbol of the cast.
  ///
  /// Store at this point:
  ///   s |-> return symbol of s.operator string_view
  ///
  /// Result: s |-> { symbol }
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;

  /// Step 2 of recording a view in CastSymbols: after the declaration, look up
  /// the symbol of Step 1 in the Store. Associate its region with the string.
  ///
  /// Store at this point:
  ///   v |-> return symbol of s.operator string_view
  ///
  /// Result: s |-> { v }
  void checkBind(SVal Loc, SVal Val, const Stmt *S, CheckerContext &C) const;

  void checkLiveSymbols(ProgramStateRef State, SymbolReaper &SymReaper) const;
  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;

  /// Show the contents of CastSymbols in the exploded graph dump.
  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const override;

  class StringModelingBRVisitor : public BugReporterVisitor {
    const MemRegion *Reg;

  public:
    StringModelingBRVisitor(const MemRegion *Reg) : Reg(Reg) {}

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

    bool isSymbolTracked(ProgramStateRef State, const MemRegion *Target) {
      ViewRegionsTy Map = State->get<ViewRegions>();
      for (const auto &Entry : Map) {
        for (const MemRegion *View : Entry.second) {
          if (View == Target)
            return true;
        }
      }
      return false;
    }
  };
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

bool StringModeling::handleStringCStrData(const CallEvent &Call,
                                          CheckerContext &C) const {
  const auto *MemCall = dyn_cast<CXXMemberCall>(&Call);
  const MemRegion *String = MemCall->getCXXThisVal().getAsRegion();
  if (!String)
    return false;

  getPointerAndBindToCall(Call, String, C);
  return true;
}

bool StringModeling::handleViewData(const CallEvent &Call,
                                    CheckerContext &C) const {
  // Step 1: See if there is a string associated with this view.
  // For this, get the symbol of the view and look it up in CastSymbols.
  const auto *ICall = dyn_cast<CXXInstanceCall>(&Call);
  const MemRegion *ViewRegion = ICall->getCXXThisVal().getAsRegion();
  if (!ViewRegion)
    return false;

  ProgramStateRef State = C.getState();
  StoreManager &StoreMgr = C.getStoreManager();
  auto ViewVal = StoreMgr.getDefaultBinding(State->getStore(), ViewRegion);
  if (!ViewVal)
    return false;

  // This should be a symbol that we saved in CastSymbols if the view was
  // created from a string. FIXME: Is includeBaseRegions=true needed?
  SymbolRef View = ViewVal.getValue().getAsSymbol(true);
  assert(View && "View is not a symbol!");
  const MemRegion *String = innerptr::getStringForSymbol(State, View);
  if (!String)
    return false;

  // Step 2: Create or find an existing pointer symbol for this string
  // and bind it to the call expression.
  getPointerAndBindToCall(Call, String, C);
  return true;
}

bool StringModeling::evalCall(const CallEvent &Call, CheckerContext &C) const {
  const auto *Handler = StringHandlers.lookup(Call);
  if (!Handler)
    return false;

  return (this->**Handler)(Call, C);
}

static bool isStringViewConversion(const CallEvent &Call) {
  const auto *CD = dyn_cast_or_null<CXXConversionDecl>(Call.getDecl());
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

void StringModeling::checkBind(SVal Loc, SVal Val, const Stmt *S,
                               CheckerContext &C) const {
  // Step 2: view is created from a string, end of construction.
  // Associate the view with the string in ViewRegions.
  if (SymbolRef Sym = Val.getAsSymbol(true)) {
    const MemRegion *String = innerptr::getStringForSymbol(C.getState(), Sym);
    if (!String)
      return;

    // The symbol is in the CastSymbols map.
    // Add (String, Loc) to the ViewRegions map.
    ProgramStateRef State = C.getState();
    const MemRegion *View = Loc.getAsRegion();
    if (!View)
      return;

    RegionSet::Factory &F = State->getStateManager().get_context<RegionSet>();
    const RegionSet *OldSet = State->get<ViewRegions>(String);
    RegionSet NewSet = OldSet ? *OldSet : F.getEmptySet();

    // FIXME: what does this ensure again?
    assert(C.wasInlined || !NewSet.contains(View));
    NewSet = F.add(NewSet, View);
    C.addTransition(State->set<ViewRegions>(String, NewSet));
    return;
  }
}

void StringModeling::checkPostCall(const CallEvent &Call,
                                   CheckerContext &C) const {
  ProgramStateRef State = C.getState();

  // Step 1: view is created from a string, start of construction.
  // Track the return symbol of the conversion operator call.
  if (isStringViewConversion(Call)) {
    SymbolRef View = Call.getReturnValue().getAsSymbol();
    if (!View)
      return;

    const auto *ICall = dyn_cast<CXXInstanceCall>(&Call);
    if (!ICall)
      return;

    const MemRegion *String = ICall->getCXXThisVal().getAsRegion();
    if (!String)
      return;

    SymbolSet::Factory &F = State->getStateManager().get_context<SymbolSet>();
    const SymbolSet *OldSet = State->get<CastSymbols>(String);
    SymbolSet NewSet = OldSet ? *OldSet : F.getEmptySet();

    // FIXME: what does this ensure again?
    assert(C.wasInlined || !NewSet.contains(View));
    NewSet = F.add(NewSet, View);

    C.addTransition(State->set<CastSymbols>(String, NewSet));
    return;
  }

  // (Optional) Step 3: view is created from another view.
  // Add the new view to the same ViewRegions entry the copied view is in.
  if (const auto *CC = dyn_cast<CXXConstructorCall>(&Call)) {
    const auto *CD = dyn_cast<CXXConstructorDecl>(Call.getDecl());
    if (!CD || !CD->isCopyConstructor())
      return;

    const MemRegion *CopiedView = CC->getArgSVal(0).getAsRegion();
    if (!CopiedView)
      return;

    const MemRegion *String = innerptr::getStringForRegion(State, CopiedView);
    if (!String)
      return;

    // CopiedView is in ViewRegions.
    const MemRegion *CreatedView = CC->getCXXThisVal().getAsRegion();
    if (!CreatedView)
      return;

    RegionSet::Factory &F = State->getStateManager().get_context<RegionSet>();
    const RegionSet *OldSet = State->get<ViewRegions>(String);
    RegionSet NewSet = OldSet ? *OldSet : F.getEmptySet();

    // FIXME: what does this ensure again?
    assert(C.wasInlined || !NewSet.contains(CreatedView));
    NewSet = F.add(NewSet, CreatedView);
    C.addTransition(State->set<ViewRegions>(String, NewSet));
    return;
  }

  if (const auto *MOC = dyn_cast<CXXMemberOperatorCall>(&Call)) {
    if (MOC->getOverloadedOperator() != OO_Equal)
      return;

    // FIXME: Do I need an is-this-a-view check here?

    SVal CopiedVal = State->getSVal(MOC->getArgExpr(0), C.getLocationContext());
    const MemRegion *Copied = CopiedVal.getAsRegion();
    if (!Copied)
      return;

    const MemRegion *CreatedView = MOC->getCXXThisVal().getAsRegion();
    if (!CreatedView)
      return;

    if (const MemRegion *String = innerptr::getStringForRegion(State, Copied)) {
      // The copied object is a view that we track!
      // Add the newly created view to the ViewRegions map.
      RegionSet::Factory &F = State->getStateManager().get_context<RegionSet>();
      const RegionSet *OldSet = State->get<ViewRegions>(String);
      RegionSet NewSet = OldSet ? *OldSet : F.getEmptySet();

      // FIXME: what does this ensure again?
      assert(C.wasInlined || !NewSet.contains(CreatedView));
      NewSet = F.add(NewSet, CreatedView);
      C.addTransition(State->set<ViewRegions>(String, NewSet));
      return;
    }

    // The other possibility is that we call the assign op with a string.
    // Look it up in the store and see if the symbol is among CastSymbols.
    StoreManager &StoreMgr = C.getStoreManager();
    auto SymOpt = StoreMgr.getDefaultBinding(State->getStore(), Copied);
    if (!SymOpt)
      return;

    // FIXME: Still no idea what includebaseregions mean.
    SymbolRef Sym = SymOpt.getValue().getAsSymbol(true);
    if (!Sym)
      return;

    const MemRegion *String = innerptr::getStringForSymbol(State, Sym);
    if (!String)
      return;

    // The symbol is among CastSymbols!
    RegionSet::Factory &F = State->getStateManager().get_context<RegionSet>();
    const RegionSet *OldSet = State->get<ViewRegions>(String);
    RegionSet NewSet = OldSet ? *OldSet : F.getEmptySet();

    // FIXME: what does this ensure again?
    assert(C.wasInlined || !NewSet.contains(CreatedView));
    NewSet = F.add(NewSet, CreatedView);
    C.addTransition(State->set<ViewRegions>(String, NewSet));
    return;
  }
}

void StringModeling::printState(raw_ostream &Out, ProgramStateRef State,
                                const char *NL, const char *Sep) const {
  CastSymbolsTy CSMap = State->get<CastSymbols>();
  if (!CSMap.isEmpty()) {
    Out << Sep << "Cast symbols:" << NL;
    for (const auto &Entry : CSMap) {
      Entry.first->dumpToStream(Out);
      Out << ": {";
      for (const SymbolRef Sym : Entry.second) {
        Sym->dumpToStream(Out);
        Out << ", ";
      }
      Out << "}" << NL;
    }
  }

  ViewRegionsTy VRMap = State->get<ViewRegions>();
  if (!VRMap.isEmpty()) {
    Out << Sep << "View regions:" << NL;
    for (const auto &Entry : VRMap) {
      Entry.first->dumpToStream(Out);
      Out << ": {";
      for (const MemRegion *View : Entry.second) {
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
  CastSymbolsTy Map = State->get<CastSymbols>();
  for (const auto &Entry : Map) {
    for (const SymbolRef View : Entry.second) {
      if (SymReaper.isLive(View)) {
        SymReaper.markLive(innerptr::getSymbolFor(State, Entry.first));
        break;
      }
    }
  }
}

// FIXME: ViewRegions
void StringModeling::checkDeadSymbols(SymbolReaper &SymReaper,
                                      CheckerContext &C) const {
  ProgramStateRef State = C.getState();

  SymbolSet::Factory &F = State->getStateManager().get_context<SymbolSet>();
  CastSymbolsTy Map = State->get<CastSymbols>();

  for (const auto &Entry : Map) {
    if (!SymReaper.isLiveRegion(Entry.first)) {
      // Due to incomplete destructor support, some dead regions might
      // remain in the program state map. Clean them up.
      State = State->remove<CastSymbols>(Entry.first);
    }
    if (const SymbolSet *OldSet = State->get<CastSymbols>(Entry.first)) {
      SymbolSet CleanedUpSet = *OldSet;
      for (const auto Symbol : Entry.second) {
        if (!SymReaper.isLive(Symbol))
          CleanedUpSet = F.remove(CleanedUpSet, Symbol);
      }
      State = CleanedUpSet.isEmpty()
                  ? State->remove<CastSymbols>(Entry.first)
                  : State->set<CastSymbols>(Entry.first, CleanedUpSet);
    }
  }

  C.addTransition(State);
}

PathDiagnosticPieceRef StringModeling::StringModelingBRVisitor::VisitNode(
    const ExplodedNode *N, BugReporterContext &BRC, PathSensitiveBugReport &) {
  if (!isSymbolTracked(N->getState(), Reg) ||
      isSymbolTracked(N->getFirstPred()->getState(), Reg))
    return nullptr;

  const Stmt *S = N->getStmtForDiagnostics();
  if (!S)
    return nullptr;

  const MemRegion *String = innerptr::getStringForRegion(N->getState(), Reg);
  if (!String)
    return nullptr;

  const auto *TypedRegion = cast<TypedValueRegion>(String);
  QualType ObjTy = TypedRegion->getValueType();

  SmallString<256> Buf;
  llvm::raw_svector_ostream OS(Buf);
  OS << "Pointer to inner buffer of '" << ObjTy.getAsString()
     << "' obtained here";

  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return std::make_shared<PathDiagnosticEventPiece>(Pos, OS.str(), true);
}

namespace clang {
namespace ento {
namespace innerptr {

std::unique_ptr<BugReporterVisitor>
getStringModelingBRVisitor(const MemRegion *Reg) {
  return std::make_unique<StringModeling::StringModelingBRVisitor>(Reg);
}

const MemRegion *getStringForSymbol(ProgramStateRef State, SymbolRef Target) {
  CastSymbolsTy Map = State->get<CastSymbols>();
  for (const auto &Entry : Map) {
    for (const SymbolRef View : Entry.second) {
      if (View == Target)
        return Entry.first;
    }
  }
  return nullptr;
}

const MemRegion *getStringForRegion(ProgramStateRef State,
                                    const MemRegion *Target) {
  ViewRegionsTy Map = State->get<ViewRegions>();
  for (const auto &Entry : Map) {
    for (const MemRegion *View : Entry.second) {
      if (View == Target)
        return Entry.first;
    }
  }
  return nullptr;
}

void markViewsReleased(ProgramStateRef State, const MemRegion *String,
                       CheckerContext &C) {
  if (const RegionSet *Set = State->get<ViewRegions>(String)) {
    for (const MemRegion *View : *Set)
      State = allocation_state::markViewReleased(State, View);

    C.addTransition(State->remove<ViewRegions>(String));
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
