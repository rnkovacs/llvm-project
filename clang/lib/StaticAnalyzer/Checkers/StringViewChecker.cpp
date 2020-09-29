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

#include "InnerPtr.h"

#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

namespace {

class StringViewChecker : public Checker<check::DeadSymbols> {

public:
  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;
};

} // end of anonymous namespace

void StringViewChecker::checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const {}

void ento::registerStringViewChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<StringViewChecker>();
}

bool ento::shouldRegisterStringViewChecker(const CheckerManager &mgr) {
  const LangOptions &LO = mgr.getLangOpts();
  return LO.CPlusPlus;
}
