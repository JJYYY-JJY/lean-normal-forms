/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.Trace
public import NormalForms.Research.KannanBachem.Hermite.Semantics
public import NormalForms.Research.KannanBachem.Hermite.Primitive
public import NormalForms.Research.KannanBachem.Hermite.OperationBound
public import NormalForms.Research.KannanBachem.Hermite.Principal
public import NormalForms.Research.KannanBachem.Hermite.PrincipalChecker
public import NormalForms.Research.KannanBachem.Hermite.PrincipalOperationBound
public import NormalForms.Research.KannanBachem.Hermite.CoefficientSize
public import NormalForms.Research.KannanBachem.Hermite.IntermediateSize
public import NormalForms.Research.KannanBachem.Hermite.PrincipalFinalSize
public import NormalForms.Research.KannanBachem.Hermite.PrincipalOperandBound
public import NormalForms.Research.KannanBachem.Hermite.BoundedXGCD
public import NormalForms.Research.KannanBachem.Hermite.PrincipalIntermediateBound
public import NormalForms.Research.KannanBachem.Hermite.PrincipalTraceBound
public import NormalForms.Research.KannanBachem.Hermite.PrincipalPolynomialBound
public import NormalForms.Research.KannanBachem.Hermite.PrincipalMultiplierBound
public import NormalForms.Research.KannanBachem.Hermite.PrincipalBitComplexity
public import NormalForms.Research.KannanBachem.Hermite.PrincipalPreparation
public import NormalForms.Research.KannanBachem.Hermite.PreparedBitComplexity
public import NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminant
public import NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminantCorrectness
public import NormalForms.Research.KannanBachem.Hermite.DivisionFreeDeterminantCost
public import NormalForms.Research.KannanBachem.Hermite.DeterminantScan
public import NormalForms.Research.KannanBachem.Smith.BitComplexity
public import NormalForms.Research.KannanBachem.Bounds

/-!
# Kannan--Bachem Research Facade

Independent research surface for the staged verified integer HNF/SNF and
complexity development.  It is intentionally absent from the stable core
facade.
-/

public section
