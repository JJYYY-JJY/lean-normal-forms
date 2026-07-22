/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Research.LLL
import all NormalForms.Research.LLL.Diagnostics
meta import all NormalForms.Research.LLL
meta import all NormalForms.Research.LLL.Diagnostics

set_option linter.privateModule false
set_option linter.hashCommand false

/-! Deterministic exact-rational LLL execution guards. -/

namespace NormalForms.Tests.Research.LLL.Execution

open NormalForms.Research.LLL

private def gaussInput : Matrix (Fin 2) (Fin 2) Int :=
  !![1, 1; 1, 0]

private def gaussRun := fullRankLLLWithFuel gaussInput 32

private def identityInput : Matrix (Fin 2) (Fin 2) Int :=
  ofDense (Hex.Matrix.identity (R := Int) 2)

private theorem identityFullRank : FullRowRankWitness identityInput :=
  { independent := by
      simpa [identityInput] using
        (Hex.Matrix.identity_independent (n := 2)) }

private def gaussTotal := integerLLL gaussInput

private def identityProfile :=
  fullRankLLLProfilePositive identityInput (by decide) identityFullRank

private def dependentInput : Matrix (Fin 3) (Fin 3) Int :=
  !![1, 1, 0; 2, 2, 0; 0, 0, 0]

private def dependentTotal := integerLLL dependentInput

private def zeroInput : Matrix (Fin 2) (Fin 3) Int :=
  !![0, 0, 0; 0, 0, 0]

private def zeroTotal := integerLLL zeroInput

private def columnTotal := integerColumnLLL dependentInput.transpose

private def matrixEqb {m n : Nat}
    (left right : Matrix (Fin m) (Fin n) Int) : Bool :=
  (List.finRange m).all fun row =>
    (List.finRange n).all fun column => left row column == right row column

#guard gaussRun.complete
#guard gaussRun.operations.sizeReductions == 2
#guard gaussRun.operations.swaps == 1
#guard gaussRun.operations.gramSchmidtRefreshes == 3
#guard gaussRun.candidate 0 0 == 0
#guard gaussRun.candidate 0 1 == -1
#guard gaussRun.candidate 1 0 == 1
#guard gaussRun.candidate 1 1 == 0
#guard gaussRun.certified.isSome
#guard gaussTotal.rank == 2
#guard matrixEqb (gaussTotal.U * gaussInput) gaussTotal.reducedBasis
#guard matrixEqb (gaussTotal.U_cert.inverse * gaussTotal.U) 1
#guard matrixEqb (gaussTotal.U * gaussTotal.U_cert.inverse) 1
#guard isLLLReducedB (rowPrefix gaussTotal.rank_le_rows gaussTotal.reducedBasis)
#guard identityProfile.operations.total <=
  lllTrackedEventBound 2 identityProfile.fuel
#guard basisBitLength identityProfile.result.reducedBasis <=
  identityProfile.intermediateCoefficientBitLength
#guard identityProfile.bitOperationCost <=
  lllKernelBitOperationBound 2 2 identityProfile.fuel
    identityProfile.intermediateCoefficientHeight
#guard dependentTotal.rank == 1
#guard matrixEqb (dependentTotal.U * dependentInput) dependentTotal.reducedBasis
#guard matrixEqb (dependentTotal.U_cert.inverse * dependentTotal.U) 1
#guard matrixEqb (dependentTotal.U * dependentTotal.U_cert.inverse) 1
#guard isLLLReducedB (rowPrefix dependentTotal.rank_le_rows dependentTotal.reducedBasis)
#guard dependentTotal.reducedBasis 1 0 == 0
#guard dependentTotal.reducedBasis 1 1 == 0
#guard dependentTotal.reducedBasis 2 0 == 0
#guard dependentTotal.reducedBasis 2 1 == 0
#guard zeroTotal.rank == 0
#guard matrixEqb (zeroTotal.U * zeroInput) zeroTotal.reducedBasis
#guard matrixEqb (zeroTotal.U_cert.inverse * zeroTotal.U) 1
#guard matrixEqb (zeroTotal.U * zeroTotal.U_cert.inverse) 1
#guard columnTotal.rank == 1
#guard matrixEqb (dependentInput.transpose * columnTotal.V) columnTotal.reducedBasis
#guard matrixEqb (columnTotal.V_cert.inverse * columnTotal.V) 1
#guard matrixEqb (columnTotal.V * columnTotal.V_cert.inverse) 1

end NormalForms.Tests.Research.LLL.Execution
