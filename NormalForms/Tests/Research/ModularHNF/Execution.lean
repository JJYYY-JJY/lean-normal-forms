/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Research.ModularHNF
import NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.Hermite.Algorithm
meta import NormalForms.Research.ModularHNF
meta import NormalForms.Matrix.Hermite.Algorithm

set_option linter.privateModule false
set_option linter.hashCommand false

/-! Deterministic execution guards for the raw modular value kernel. -/

namespace NormalForms.Tests.Research.ModularHNF.Execution

open scoped Matrix
open NormalForms.Matrix.Hermite
open NormalForms.Research.ModularHNF

private def matrixEqb {m n : Nat}
    (left right : Matrix (Fin m) (Fin n) Int) : Bool :=
  (List.finRange m).all fun i =>
    (List.finRange n).all fun j => decide (left i j = right i j)

private def squareInput : Matrix (Fin 2) (Fin 2) Int :=
  !![2, 4;
     6, 8]

private def squareFullRank : FullColumnRankWitness squareInput :=
  { rows := Function.Embedding.refl _
    det_ne_zero := by decide }

private def squareModulus :
    DeterminantModulusWitness squareInput squareFullRank :=
  { modulus := 8
    positive := by decide
    selectedMinor_dvd := by decide }

#guard matrixEqb
  (runWithDeterminantWitness squareInput squareFullRank squareModulus).candidate
  (hermiteNormalFormFin squareInput).H

#guard matrixEqb
  ((modularHNFFullRank squareInput squareFullRank squareModulus).U * squareInput)
  (modularHNFFullRank squareInput squareFullRank squareModulus).H

#guard matrixEqb
  ((modularHNFFullRank squareInput squareFullRank squareModulus).U_cert.inverse *
    (modularHNFFullRank squareInput squareFullRank squareModulus).U)
  (1 : Matrix (Fin 2) (Fin 2) Int)

#guard matrixEqb
  ((modularHNFFullRank squareInput squareFullRank squareModulus).U *
    (modularHNFFullRank squareInput squareFullRank squareModulus).U_cert.inverse)
  (1 : Matrix (Fin 2) (Fin 2) Int)

#guard
  (runWithDeterminantWitness squareInput squareFullRank squareModulus).stages =
    [{ column := 0, modulusBefore := 8, gcdWithPivot := 2, modulusAfter := 4 },
     { column := 1, modulusBefore := 4, gcdWithPivot := 4, modulusAfter := 1 }]

private def tallInput : Matrix (Fin 3) (Fin 2) Int :=
  !![2, 4;
     6, 8;
     10, 14]

private def tallFullRank : FullColumnRankWitness tallInput :=
  { rows := Fin.castLEEmb (by omega)
    det_ne_zero := by decide }

private def tallModulus :
    DeterminantModulusWitness tallInput tallFullRank :=
  { modulus := 8
    positive := by decide
    selectedMinor_dvd := by decide }

#guard matrixEqb
  (runWithDeterminantWitness tallInput tallFullRank tallModulus).candidate
  (hermiteNormalFormFin tallInput).H

#guard matrixEqb
  ((modularHNFFullRank tallInput tallFullRank tallModulus).U * tallInput)
  (modularHNFFullRank tallInput tallFullRank tallModulus).H

#guard matrixEqb
  (integerHermiteNormalFormModular tallInput).H
  (hermiteNormalFormFin tallInput).H

private def denseInput : Matrix (Fin 3) (Fin 3) Int :=
  !![2, 4, 6;
     0, 3, 9;
     4, 1, 5]

private def denseFullRank : FullColumnRankWitness denseInput :=
  { rows := Function.Embedding.refl _
    det_ne_zero := by decide }

private def denseModulus :
    DeterminantModulusWitness denseInput denseFullRank :=
  { modulus := 84
    positive := by decide
    selectedMinor_dvd := by decide }

#guard matrixEqb
  (runWithDeterminantWitness denseInput denseFullRank denseModulus).candidate
  (hermiteNormalFormFin denseInput).H

#guard matrixEqb
  ((modularHNFFullRank denseInput denseFullRank denseModulus).U_cert.inverse *
    (modularHNFFullRank denseInput denseFullRank denseModulus).H)
  denseInput

#guard matrixEqb
  (integerHermiteNormalFormModular denseInput).H
  (hermiteNormalFormFin denseInput).H

#guard
  (runWithDeterminantWitness denseInput denseFullRank denseModulus).operations.total ≤
    modularOperationBound 3 3

#guard
  matrixHeight
      (runRawPrefix denseInput denseFullRank.columns_le_rows
        denseModulus.modulus 1).candidate ≤
    modularIntermediateHeightBound 3 3 1
      (matrixHeight denseInput) denseModulus.modulus.natAbs

#guard
  matrixBitLength
      (runRawPrefix denseInput denseFullRank.columns_le_rows
        denseModulus.modulus 2).candidate ≤
    Nat.size (modularIntermediateHeightBound 3 3 2
      (matrixHeight denseInput) denseModulus.modulus.natAbs)

#guard
  matrixHeight
      (runWithDeterminantWitness denseInput denseFullRank denseModulus).candidate ≤
    denseModulus.modulus.natAbs

#guard
  let actual := (StandardXGCD.standardIntXGCDWithCost 84 30).value
  let expected := ComputableEuclideanOps.xgcd 84 30
  actual.gcd == expected.gcd &&
    actual.leftCoeff == expected.leftCoeff &&
    actual.rightCoeff == expected.rightCoeff

#guard
  (StandardXGCD.standardIntXGCDWithCost 84 30).cost ≤
    StandardXGCD.standardIntXGCDUniformBitOperationBound 84

private def bitCostInput : Matrix (Fin 1) (Fin 1) Int := !![2]

private def bitCostFullRank : FullColumnRankWitness bitCostInput :=
  { rows := Function.Embedding.refl _
    det_ne_zero := by decide }

private def bitCostModulus :
    DeterminantModulusWitness bitCostInput bitCostFullRank :=
  { modulus := 2
    positive := by decide
    selectedMinor_dvd := by decide }

#guard
  (runWithDeterminantWitness bitCostInput bitCostFullRank
      bitCostModulus).operations.bitOperationCost
        (modularKernelHeightBound bitCostInput bitCostModulus.modulus) ≤
    modularKernelBitOperationBound bitCostInput bitCostModulus.modulus

/- The same transition system is observably wrong when its modulus contract is violated. -/
#guard !matrixEqb
  (runRaw denseInput (by omega) 18).candidate
  (hermiteNormalFormFin denseInput).H

/-
An elementary-divisor modulus is legal for FLINT's separate strong-echelon
kernel, not for the determinant-modulus DKT transition system above.  For
`diag(2,2)`, the largest elementary divisor is `2`, while running DKT with
modulus `2` gives the wrong second pivot.  This guards the API separation.
-/
private def elementaryInput : Matrix (Fin 2) (Fin 2) Int :=
  !![2, 0;
     0, 2]

#guard !matrixEqb
  (runRaw elementaryInput (by omega) 2).candidate
  (hermiteNormalFormFin elementaryInput).H

private def zeroWidth : Matrix (Fin 3) (Fin 0) Int := 0

private def zeroWidthFullRank : FullColumnRankWitness zeroWidth :=
  { rows := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    det_ne_zero := by simp [selectedSquareMinor] }

private def zeroWidthModulus :
    DeterminantModulusWitness zeroWidth zeroWidthFullRank :=
  { modulus := 1
    positive := by decide
    selectedMinor_dvd := by decide }

#guard matrixEqb
  (runWithDeterminantWitness zeroWidth zeroWidthFullRank
    zeroWidthModulus).candidate
  zeroWidth

#guard
  (runWithDeterminantWitness zeroWidth zeroWidthFullRank
    zeroWidthModulus).stages = []

#guard matrixEqb
  (integerHermiteNormalFormModular zeroWidth).H
  zeroWidth

private def rankDeficientInput : Matrix (Fin 3) (Fin 3) Int :=
  !![2, 4, 6;
     6, 8, 14;
     4, 4, 8]

private def rankDeficientProfile :
    FractionFreeRankProfile rankDeficientInput :=
  { rank := 2
    rank_le_rows := by omega
    rank_le_columns := by omega
    pivotColumns := Fin.castLEEmb (by omega)
    pivotColumns_strictMono := by
      intro left right before
      exact before
    pivotRows := Fin.castLEEmb (by omega)
    minor_ne_zero := by decide
    coefficients := !![-8, 0; 0, -8; -8, -8]
    column_identity := by decide
    coefficients_zero_of_before := by decide }

#guard matrixEqb
  (integerHermiteNormalFormModularWithProfile rankDeficientInput
    rankDeficientProfile).H
  (hermiteNormalFormFin rankDeficientInput).H

#guard matrixEqb
  ((integerHermiteNormalFormModularWithProfile rankDeficientInput
      rankDeficientProfile).U * rankDeficientInput)
  (integerHermiteNormalFormModularWithProfile rankDeficientInput
    rankDeficientProfile).H

#guard matrixEqb
  ((integerHermiteNormalFormModularWithProfile rankDeficientInput
      rankDeficientProfile).U_cert.inverse *
    (integerHermiteNormalFormModularWithProfile rankDeficientInput
      rankDeficientProfile).H)
  rankDeficientInput

#guard matrixEqb
  (integerHermiteNormalFormModular rankDeficientInput).H
  (hermiteNormalFormFin rankDeficientInput).H

#guard matrixEqb
  ((integerHermiteNormalFormModular rankDeficientInput).U_cert.inverse *
    (integerHermiteNormalFormModular rankDeficientInput).H)
  rankDeficientInput

private def wideRankOneInput : Matrix (Fin 2) (Fin 3) Int :=
  !![2, 4, 6;
     4, 8, 12]

private def wideRankOneProfile :
    FractionFreeRankProfile wideRankOneInput :=
  { rank := 1
    rank_le_rows := by omega
    rank_le_columns := by omega
    pivotColumns := Fin.castLEEmb (by omega)
    pivotColumns_strictMono := by
      intro left right before
      exact before
    pivotRows := Fin.castLEEmb (by omega)
    minor_ne_zero := by decide
    coefficients := !![2; 4; 6]
    column_identity := by decide
    coefficients_zero_of_before := by decide }

#guard matrixEqb
  (integerHermiteNormalFormModularWithProfile wideRankOneInput
    wideRankOneProfile).H
  (hermiteNormalFormFin wideRankOneInput).H

#guard matrixEqb
  (integerHermiteNormalFormModular wideRankOneInput).H
  (hermiteNormalFormFin wideRankOneInput).H

private def zeroGeneral : Matrix (Fin 2) (Fin 3) Int := 0

private def zeroGeneralProfile : FractionFreeRankProfile zeroGeneral :=
  { rank := 0
    rank_le_rows := by omega
    rank_le_columns := by omega
    pivotColumns := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    pivotColumns_strictMono := by
      intro i
      exact Fin.elim0 i
    pivotRows := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    minor_ne_zero := by decide
    coefficients := fun _ i => Fin.elim0 i
    column_identity := by decide
    coefficients_zero_of_before := by decide }

#guard matrixEqb
  (integerHermiteNormalFormModularWithProfile zeroGeneral
    zeroGeneralProfile).H
  zeroGeneral

#guard matrixEqb
  (integerHermiteNormalFormModular zeroGeneral).H
  zeroGeneral

private def pivotGapInput : Matrix (Fin 2) (Fin 3) Int :=
  !![0, 2, 4;
     0, 4, 8]

#guard (searchRankProfile? pivotGapInput).map
  (fun selection => (selection.rank.val,
    List.ofFn selection.pivotColumns,
    List.ofFn selection.pivotRows)) = some (1, [1], [0])

#guard matrixEqb
  (integerHermiteNormalFormModular pivotGapInput).H
  (hermiteNormalFormFin pivotGapInput).H

#guard matrixEqb
  ((integerHermiteNormalFormModular pivotGapInput).U * pivotGapInput)
  (integerHermiteNormalFormModular pivotGapInput).H

#guard matrixEqb
  ((integerHermiteNormalFormModular pivotGapInput).U_cert.inverse *
    (integerHermiteNormalFormModular pivotGapInput).U)
  (1 : Matrix (Fin 2) (Fin 2) Int)

end NormalForms.Tests.Research.ModularHNF.Execution
