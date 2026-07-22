/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.Representation
public import NormalForms.Research.BitCost.Addition
public import NormalForms.Research.BitCost.Multiplication
public import NormalForms.Research.BitCost.Division
public import NormalForms.Research.BitCost.XGCD
public import NormalForms.Research.BitCost.NormalizedXGCD
public import NormalForms.Research.BitCost.EuclideanIterations
public import NormalForms.Research.BitCost.BoundedXGCD
public import NormalForms.Research.BitCost.BoundedXGCDCost

/-!
# Verified Binary Bit-Cost Reference Model

Independent research facade for explicit sign-magnitude arithmetic and its
kernel-checked bit-operation budgets. It is intentionally not imported by the
stable `NormalForms` core facade.
-/

public section
