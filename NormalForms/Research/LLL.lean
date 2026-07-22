/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Parameters
public import NormalForms.Research.LLL.GramSchmidt
public import NormalForms.Research.LLL.Predicate
public import NormalForms.Research.LLL.Result
public import NormalForms.Research.LLL.Cost
public import NormalForms.Research.LLL.FullRank
public import NormalForms.Research.LLL.Total

/-!
# Exact rational row-basis LLL research facade

This independently imported facade fixes `delta = 3/4`, `eta = 1/2`, and the
row-basis convention.  It exposes both the independent-row kernel and the
total rank-deficient row/column entries; algorithm internals remain hidden.
-/
