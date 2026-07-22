/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Contracts
public import NormalForms.Research.ModularHNF.Algorithm
public import NormalForms.Research.ModularHNF.Lattice
public import NormalForms.Research.ModularHNF.Determinant
public import NormalForms.Research.ModularHNF.Transition
public import NormalForms.Research.ModularHNF.Below
public import NormalForms.Research.ModularHNF.Above
public import NormalForms.Research.ModularHNF.Pivot
public import NormalForms.Research.ModularHNF.Stage
public import NormalForms.Research.ModularHNF.Run
public import NormalForms.Research.ModularHNF.Coordinate
public import NormalForms.Research.ModularHNF.Shape
public import NormalForms.Research.ModularHNF.Reference
public import NormalForms.Research.ModularHNF.Semantic
public import NormalForms.Research.ModularHNF.Correctness
public import NormalForms.Research.ModularHNF.RankProfile
public import NormalForms.Research.ModularHNF.ProfileSearch
public import NormalForms.Research.ModularHNF.OperationBound
public import NormalForms.Research.ModularHNF.CoefficientSize
public import NormalForms.Research.ModularHNF.StandardXGCD
public import NormalForms.Research.ModularHNF.BitComplexity

/-!
# Modular-HNF research facade

This independent facade is intentionally absent from `NormalForms`.  It
exposes the raw full-column kernel, its semantic proof, checked fraction-free
rank profiles, the total strong wrapper for general integer matrices, the
closed scalar-operation bound, and intermediate/final coefficient bounds.
It also exposes an exact mirror of Lean's standard integer XGCD path and a
closed schoolbook bit-operation budget for the modular value kernel.
-/

public section
