/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Principal
public import NormalForms.Research.KannanBachem.Execution.Preparation
public import NormalForms.Research.KannanBachem.Smith.BoundedColumn

/-!
# Prepared Principal and Bounded-column Executions
-/

public section

namespace NormalForms.Research.KannanBachem

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- Instrumented strong HNF result. -/
public structure HNFExecution {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Int) where
  value : HNFResultFin A
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges

public theorem hnfResult_ext_data {m n : Nat}
    {A : Matrix (Fin m) (Fin n) Int}
    (left right : HNFResultFin A)
    (u_eq : left.U = right.U)
    (uinv_eq : left.U_cert.inverse = right.U_cert.inverse)
    (h_eq : left.H = right.H) :
    left = right := by
  cases left with
  | mk leftU leftUCert leftH leftEquation leftHermite =>
      cases right with
      | mk rightU rightUCert rightH rightEquation rightHermite =>
          dsimp only at u_eq uinv_eq h_eq
          subst rightU
          subst rightH
          have ucert_eq : leftUCert = rightUCert := by
            cases leftUCert
            cases rightUCert
            simp_all
          subst rightUCert
          rfl

/-- Prepared principal execution, including the two transform products. -/
@[expose] public def preparedPrincipalExecution {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    HNFExecution A := by
  let preparationRun := preparationExecution A hdet
  let preparation := preparationRun.value
  let core := principalExecution preparation.matrix
  let coreCertificate : MatrixInverseCertificate core.U :=
    { inverse := core.Uinv
      left_inv := core.inverse_identities.1
      right_inv := core.inverse_identities.2 }
  let forwardRun := matrixProductExecution core.U preparation.transform
  let inverseRun := matrixProductExecution
    preparation.transformCertificate.inverse core.Uinv
  have forwardValue :
      forwardRun.value = core.U * preparation.transform :=
    matrixProductExecution_value _ _
  have inverseValue :
      inverseRun.value =
        preparation.transformCertificate.inverse * core.Uinv :=
    matrixProductExecution_value _ _
  let finalCertificate : MatrixInverseCertificate forwardRun.value :=
    { inverse := inverseRun.value
      left_inv := by
        rw [forwardValue, inverseValue]
        exact (coreCertificate.mul preparation.transformCertificate).left_inv
      right_inv := by
        rw [forwardValue, inverseValue]
        exact (coreCertificate.mul preparation.transformCertificate).right_inv }
  have coreHermite : IsHermiteNormalFormFin core.B := by
    rw [core.value_refinement.1]
    exact principalRun_isHermite_of_det_ne_zero preparation.matrix
      (preparation.det_ne hdet)
  let value : HNFResultFin A :=
    { U := forwardRun.value
      U_cert := finalCertificate
      H := core.B
      equation := by
        rw [forwardValue, Matrix.mul_assoc, preparation.equation,
          core.equation]
      isHermite := coreHermite }
  let charges := preparationRun.charges ++
    (core.charges ++ (forwardRun.charges ++ inverseRun.charges))
  have chargesWellFormed : ArithmeticChargeListWellFormed charges := by
    apply preparationRun.trace_wellFormed.append
    apply core.trace_wellFormed.append
    exact forwardRun.trace_wellFormed.append inverseRun.trace_wellFormed
  exact
    { value
      charges
      trace_wellFormed := chargesWellFormed }

public theorem preparedPrincipalExecution_value {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (preparedPrincipalExecution A hdet).value =
      Hermite.Principal.preparedPrincipalHermiteNormalForm A hdet := by
  apply hnfResult_ext_data
  · change
      (matrixProductExecution
          (principalExecution
            (preparationExecution A hdet).value.matrix).U
          (preparationExecution A hdet).value.transform).value =
        (Hermite.principalHermiteNormalForm
            (Hermite.Principal.prepare A hdet).matrix
            ((Hermite.Principal.prepare A hdet).det_ne hdet)).U *
          (Hermite.Principal.prepare A hdet).transform
    rw [preparationExecution_value, matrixProductExecution_value,
      (principalExecution _).value_refinement.2.1]
    rfl
  · change
      (matrixProductExecution
          (preparationExecution A hdet).value.transformCertificate.inverse
          (principalExecution
            (preparationExecution A hdet).value.matrix).Uinv).value =
        (Hermite.Principal.prepare A hdet).transformCertificate.inverse *
          (Hermite.principalHermiteNormalForm
            (Hermite.Principal.prepare A hdet).matrix
            ((Hermite.Principal.prepare A hdet).det_ne hdet)).U_cert.inverse
    rw [preparationExecution_value, matrixProductExecution_value,
      (principalExecution _).value_refinement.2.2]
    simp [Hermite.principalHermiteNormalForm,
      RowTrace.accumulatorCertificate_inverse]
  · change
      (principalExecution
          (preparationExecution A hdet).value.matrix).B =
        (Hermite.principalHermiteNormalForm
          (Hermite.Principal.prepare A hdet).matrix
          ((Hermite.Principal.prepare A hdet).det_ne hdet)).H
    rw [preparationExecution_value]
    exact (principalExecution
      (Hermite.Principal.prepare A hdet).matrix).value_refinement.1

/-- Bounded-column execution with its full transformed square matrix. -/
public structure BoundedColumnExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) where
  value : HNFResultFin (firstColumn A)
  matrix : Matrix (Fin (n + 1)) (Fin (n + 1)) Int
  fullEquation : value.U * A = matrix
  transitions : List (PrincipalTransitionExecution (n + 1))
  charges : List KannanBachemArithmeticCharge
  trace_wellFormed : ArithmeticChargeListWellFormed charges
  coverage :
    PrincipalExecutionCoverage { B := A, U := 1, Uinv := 1 }
      { B := matrix, U := value.U, Uinv := value.U_cert.inverse }
      transitions charges

/-- Execute the one-column schedule from its public primitive trace. -/
@[expose] public def boundedColumnExecution {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    BoundedColumnExecution A := by
  let sequence := boundedColumnTransitionSequence A
  have refinement := boundedColumnTransitionSequence_value A
  let reference := boundedColumnHermiteNormalForm A
  have uValue : sequence.state.U = reference.U := by
    rw [sequence.U_eq_accumulator, refinement.1,
      boundedColumnTrace_accumulator_eq]
  have uinvValue : sequence.state.Uinv = reference.U_cert.inverse := by
    rw [sequence.Uinv_eq_inverseAccumulator, refinement.1,
      boundedColumnTrace_inverseAccumulator_eq]
  let certificate : MatrixInverseCertificate sequence.state.U :=
    { inverse := sequence.state.Uinv
      left_inv := sequence.inverse_identities.1
      right_inv := sequence.inverse_identities.2 }
  let result : Matrix (Fin (n + 1)) (Fin 1) Int :=
    fun row _ => sequence.state.B row 0
  have resultValue : result = reference.H := by
    ext row column
    fin_cases column
    have replayEntry := congrFun (congrFun sequence.equation row) 0
    have referenceEntry := congrFun (congrFun reference.equation row) 0
    rw [uValue] at replayEntry
    change sequence.state.B row 0 = reference.H row 0
    calc
      sequence.state.B row 0 = (reference.U * A) row 0 := replayEntry.symm
      _ = (reference.U * firstColumn A) row 0 := by
        simp [firstColumn, Matrix.mul_apply]
      _ = reference.H row 0 := referenceEntry
  let value : HNFResultFin (firstColumn A) :=
    { U := sequence.state.U
      U_cert := certificate
      H := result
      equation := by
        ext row column
        fin_cases column
        calc
          (sequence.state.U * firstColumn A) row 0 =
              (sequence.state.U * A) row 0 := by
            simp [firstColumn, Matrix.mul_apply]
          _ = sequence.state.B row 0 :=
            congrFun (congrFun sequence.equation row) 0
      isHermite := by
        rw [resultValue]
        exact reference.isHermite }
  exact
    { value
      matrix := sequence.state.B
      fullEquation := sequence.equation
      transitions := sequence.transitions
      charges := sequence.charges
      trace_wellFormed := sequence.trace_wellFormed
      coverage := by
        simpa [value, certificate] using sequence.coverage }

public theorem boundedColumnExecution_value {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (boundedColumnExecution A).value =
      boundedColumnHermiteNormalForm A := by
  apply hnfResult_ext_data
  · change
      (boundedColumnTransitionSequence A).state.U =
        (boundedColumnHermiteNormalForm A).U
    rw [(boundedColumnTransitionSequence A).U_eq_accumulator,
      (boundedColumnTransitionSequence_value A).1,
      boundedColumnTrace_accumulator_eq]
  · change
      (boundedColumnTransitionSequence A).state.Uinv =
        (boundedColumnHermiteNormalForm A).U_cert.inverse
    rw [(boundedColumnTransitionSequence A).Uinv_eq_inverseAccumulator,
      (boundedColumnTransitionSequence_value A).1,
      boundedColumnTrace_inverseAccumulator_eq]
  · change
      (fun row (_ : Fin 1) =>
        (boundedColumnTransitionSequence A).state.B row 0) =
          (boundedColumnHermiteNormalForm A).H
    ext row column
    fin_cases column
    have replayEntry := congrFun
      (congrFun (boundedColumnTransitionSequence A).equation row) 0
    have referenceEntry := congrFun
      (congrFun (boundedColumnHermiteNormalForm A).equation row) 0
    rw [(boundedColumnTransitionSequence A).U_eq_accumulator,
      (boundedColumnTransitionSequence_value A).1,
      boundedColumnTrace_accumulator_eq] at replayEntry
    change
      (boundedColumnTransitionSequence A).state.B row 0 =
        (boundedColumnHermiteNormalForm A).H row 0
    calc
      (boundedColumnTransitionSequence A).state.B row 0 =
          ((boundedColumnHermiteNormalForm A).U * A) row 0 :=
        replayEntry.symm
      _ = ((boundedColumnHermiteNormalForm A).U * firstColumn A) row 0 := by
        simp [firstColumn, Matrix.mul_apply]
      _ = (boundedColumnHermiteNormalForm A).H row 0 :=
        referenceEntry

public theorem boundedColumnExecution_chargeComplete {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (boundedColumnExecution A).charges =
      (boundedColumnExecution A).transitions.flatMap
        PrincipalTransitionExecution.charges :=
  (boundedColumnExecution A).coverage.charges_eq_flatten

private theorem permMatrix_bitLength_le_one {n : Nat}
    (permutation : Equiv.Perm (Fin n)) :
    matrixBitLength (permutation.permMatrix Int) ≤ 1 := by
  unfold matrixBitLength
  apply Nat.size_le.2
  apply lt_of_le_of_lt (b := 1)
  · apply matrixHeight_le
    intro row column
    by_cases h : permutation row = column <;>
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
  · decide

private theorem preparation_transform_bitLength_le_one {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (preparation : Hermite.Principal.Preparation A) :
    matrixBitLength preparation.transform ≤ 1 := by
  exact permMatrix_bitLength_le_one preparation.rowPermutation

private theorem preparation_inverse_bitLength_le_one {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (preparation : Hermite.Principal.Preparation A) :
    matrixBitLength preparation.transformCertificate.inverse ≤ 1 := by
  unfold Hermite.Principal.Preparation.transformCertificate
    Hermite.Principal.permMatrixCertificate
  exact permMatrix_bitLength_le_one preparation.rowPermutation.symm

/-- Closed cost of principal replay plus its two preparation products. -/
@[expose] public def preparedPrincipalExecutionBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  let forwardBits :=
    Principal.principalMultiplierPrefixPolynomialBitLengthBound
      dimension inputBits
  let inverseBits :=
    Principal.principalInversePrefixPolynomialBitLengthBound
      dimension inputBits
  preparationExecutionBitOperationBound dimension inputBits +
    (principalExecutionBitOperationBound dimension inputBits +
      matrixMultiplicationBitOperationBound dimension forwardBits 1 +
      matrixMultiplicationBitOperationBound dimension 1 inverseBits)

public theorem preparedPrincipalExecution_cost_le {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    traceBitCost (preparedPrincipalExecution A hdet).charges ≤
      preparedPrincipalExecutionBitOperationBound n (matrixBitLength A) := by
  let preparationRun := preparationExecution A hdet
  let preparation := preparationRun.value
  let core := principalExecution preparation.matrix
  let forwardBits :=
    Principal.principalMultiplierPrefixPolynomialBitLengthBound
      n (matrixBitLength A)
  let inverseBits :=
    Principal.principalInversePrefixPolynomialBitLengthBound
      n (matrixBitLength A)
  have preparationBits :
      matrixBitLength preparation.matrix ≤ matrixBitLength A :=
    by
      rw [show preparation = Hermite.Principal.prepare A hdet from
        preparationRun.value_eq]
      exact prepare_matrixBitLength_le A hdet
  have preparationCost :
      traceBitCost preparationRun.charges ≤
        preparationExecutionBitOperationBound n (matrixBitLength A) :=
    preparationExecution_cost_le A hdet
  have coreCost :
      traceBitCost core.charges ≤
        principalExecutionBitOperationBound n (matrixBitLength A) :=
    (principalExecution_cost_le_of_ready preparation.matrix
      preparation.ready).trans <|
        principalExecutionBitOperationBound_mono_right n preparationBits
  have coreForward :
      matrixBitLength core.U ≤ forwardBits := by
    rw [core.value_refinement.2.1]
    apply (Nat.size_le_size
      (RowTrace.accumulator_height_le_intermediateMultiplierHeight
        (principalRun preparation.matrix).steps)).trans
    exact
      (principalIntermediateMultiplierBitLength_le_polynomial_of_ready
        preparation.matrix preparation.ready).trans <|
        principalMultiplierPrefixPolynomialBitLengthBound_mono n
          preparationBits
  have coreInverse :
      matrixBitLength core.Uinv ≤ inverseBits := by
    rw [core.value_refinement.2.2]
    apply (Nat.size_le_size
      (RowTrace.inverseAccumulator_height_le_intermediateInverseMultiplierHeight
        (principalRun preparation.matrix).steps)).trans
    exact
      (principalIntermediateInverseBitLength_le_polynomial_of_ready
        preparation.matrix preparation.ready).trans <|
        principalInversePrefixPolynomialBitLengthBound_mono n
          preparationBits
  have forwardCost :
      matrixMultiplicationBitOperationCost core.U preparation.transform ≤
        matrixMultiplicationBitOperationBound n forwardBits 1 :=
    matrixMultiplicationBitOperationCost_le _ _ coreForward
      (preparation_transform_bitLength_le_one preparation)
  have inverseCost :
      matrixMultiplicationBitOperationCost
          preparation.transformCertificate.inverse core.Uinv ≤
        matrixMultiplicationBitOperationBound n 1 inverseBits :=
    matrixMultiplicationBitOperationCost_le _ _
      (preparation_inverse_bitLength_le_one preparation) coreInverse
  change traceBitCost
      (preparationRun.charges ++
        (core.charges ++
          ((matrixProductExecution core.U preparation.transform).charges ++
            (matrixProductExecution
              preparation.transformCertificate.inverse core.Uinv).charges))) ≤ _
  simp only [traceBitCost_append, matrixProductExecution_cost_eq]
  unfold preparedPrincipalExecutionBitOperationBound
  dsimp only
  simpa only [forwardBits, inverseBits, Nat.add_assoc] using
    Nat.add_le_add preparationCost
      (Nat.add_le_add (Nat.add_le_add coreCost forwardCost) inverseCost)

public theorem preparedPrincipalExecutionBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    preparedPrincipalExecutionBitOperationBound dimension smaller ≤
      preparedPrincipalExecutionBitOperationBound dimension larger := by
  have forwardLe :=
    principalMultiplierPrefixPolynomialBitLengthBound_mono dimension hle
  have inverseLe :=
    principalInversePrefixPolynomialBitLengthBound_mono dimension hle
  unfold preparedPrincipalExecutionBitOperationBound
  exact Nat.add_le_add
    (preparationExecutionBitOperationBound_mono_right dimension hle)
    (Nat.add_le_add
      (Nat.add_le_add
        (principalExecutionBitOperationBound_mono_right dimension hle)
        (matrixMultiplicationBitOperationBound_mono
          dimension forwardLe le_rfl))
      (matrixMultiplicationBitOperationBound_mono
        dimension le_rfl inverseLe))

/-- Closed scalar and three-matrix replay bound for the bounded-column phase. -/
@[expose] public def boundedColumnExecutionBitOperationBound
    (dimension inputBits : Nat) : Nat :=
  dimension * principalScalarTransitionBitOperationBound inputBits +
    rowTraceDenseBitOperationBound dimension dimension
      (boundedColumnIntermediatePolynomialBitLengthBound dimension inputBits)
      (boundedColumnMultiplierPolynomialBitLengthBound dimension inputBits)
      (boundedColumnInversePolynomialBitLengthBound dimension inputBits)

private theorem boundedColumnMultiplierPolynomialBitLengthBound_mono
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    boundedColumnMultiplierPolynomialBitLengthBound dimension smaller ≤
      boundedColumnMultiplierPolynomialBitLengthBound dimension larger := by
  cases dimension with
  | zero => rfl
  | succ order =>
      simp only [boundedColumnMultiplierPolynomialBitLengthBound,
        determinantBitLengthBound]
      have intermediateLe :=
        boundedColumnIntermediateBound_mono_right (order + 1) hle
      gcongr

private theorem boundedColumnInversePolynomialBitLengthBound_mono
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    boundedColumnInversePolynomialBitLengthBound dimension smaller ≤
      boundedColumnInversePolynomialBitLengthBound dimension larger := by
  cases dimension with
  | zero => rfl
  | succ order =>
      simp only [boundedColumnInversePolynomialBitLengthBound,
        determinantBitLengthBound]
      have intermediateLe :=
        boundedColumnIntermediateBound_mono_right (order + 1) hle
      gcongr

public theorem boundedColumnExecutionBitOperationBound_mono_right
    (dimension : Nat) {smaller larger : Nat} (hle : smaller ≤ larger) :
    boundedColumnExecutionBitOperationBound dimension smaller ≤
      boundedColumnExecutionBitOperationBound dimension larger := by
  unfold boundedColumnExecutionBitOperationBound
  exact Nat.add_le_add
    (Nat.mul_le_mul_left dimension <|
      principalScalarTransitionBitOperationBound_mono hle)
    (rowTraceDenseBitOperationBound_mono dimension le_rfl
      (boundedColumnIntermediateBound_mono_right dimension hle)
      (boundedColumnMultiplierPolynomialBitLengthBound_mono dimension hle)
      (boundedColumnInversePolynomialBitLengthBound_mono dimension hle))

public theorem boundedColumnExecution_cost_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    traceBitCost (boundedColumnExecution A).charges ≤
      boundedColumnExecutionBitOperationBound
        (n + 1) (matrixBitLength A) := by
  let sequence := boundedColumnTransitionSequence A
  have refinement := boundedColumnTransitionSequence_value A
  have allWidths : ∀ event ∈ sequence.events,
      event.operandBitLength ≤ matrixBitLength A := by
    intro event member
    rw [refinement.2] at member
    exact
      (event.operandBitLength_le_list_of_mem
        (boundedColumnArithmeticEvents A) member).trans
        (boundedColumnArithmeticOperandBitLength_le_input A)
  have matrixWidth :
      sequence.steps.intermediateMatrixBitLength A ≤
        boundedColumnIntermediatePolynomialBitLengthBound
          (n + 1) (matrixBitLength A) := by
    rw [refinement.1]
    exact boundedColumnIntermediateMatrixBitLength_le_polynomial A
  have forwardWidth :
      sequence.steps.intermediateMultiplierBitLength ≤
        boundedColumnMultiplierPolynomialBitLengthBound
          (n + 1) (matrixBitLength A) := by
    rw [refinement.1]
    exact boundedColumnIntermediateMultiplierBitLength_le_polynomial A hdet
  have inverseWidth :
      sequence.steps.intermediateInverseMultiplierBitLength ≤
        boundedColumnInversePolynomialBitLengthBound
          (n + 1) (matrixBitLength A) := by
    rw [refinement.1]
    exact boundedColumnIntermediateInverseBitLength_le_polynomial A hdet
  have actualCost :=
    principalTransitionSequence_cost_le sequence
      allWidths matrixWidth forwardWidth inverseWidth
  have length : sequence.steps.length = n + 1 := by
    rw [refinement.1, boundedColumnTrace_length]
  rw [length] at actualCost
  change traceBitCost sequence.charges ≤ _
  unfold boundedColumnExecutionBitOperationBound
  exact actualCost

end NormalForms.Research.KannanBachem
