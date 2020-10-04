//=== InnerPtr.h ---------------------------------------------------*- C++ -*-//
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

#ifndef LLVM_CLANG_LIB_STATICANALYZER_CHECKERS_INNERPTR_H
#define LLVM_CLANG_LIB_STATICANALYZER_CHECKERS_INNERPTR_H

#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/MemRegion.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SymExpr.h"

namespace clang {
namespace ento {
namespace innerptr {

bool hasSymbolFor(ProgramStateRef State, const MemRegion *String);
SymbolRef getSymbolFor(ProgramStateRef State, const MemRegion *String);
ProgramStateRef setSymbolFor(CheckerContext &C, const MemRegion *String,
                             SymbolRef Sym);

void markViewsReleased(ProgramStateRef State, const MemRegion *String,
                       CheckerContext &C);

std::unique_ptr<BugReporterVisitor> getStringModelingBRVisitor(SymbolRef Sym);
const MemRegion *getStringFor(ProgramStateRef State, SymbolRef Target);

} // namespace innerptr
} // namespace ento
} // namespace clang

#endif // LLVM_CLANG_LIB_STATICANALYZER_CHECKERS_INNERPTR_H
