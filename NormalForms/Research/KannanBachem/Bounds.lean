/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.PolynomialBounds

/-! # Bounds Attached to the Instrumented Smith Execution -/

public section

namespace NormalForms.Research.KannanBachem

open NormalForms.Matrix.Smith
open NormalForms.Research.KannanBachem.Hermite
open NormalForms.Research.KannanBachem.Smith

/-- Closed input-size bound for the execution's unique leaf-cost fold. -/
@[expose] public def smithArithmeticWorkBound {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (_hdet : A.det ≠ 0) : Nat :=
  smithExecutionPolynomialBitOperationBound n (matrixBitLength A)

public theorem smithWithCost_cost_le_workBound {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithWithCost A hdet).cost ≤ smithArithmeticWorkBound A hdet := by
  rw [smithWithCost_cost_eq_traceBitCost]
  exact smithExecution_cost_le_polynomial A hdet

/-- Closed concrete-encoding bound at the execution's actual maximum entry width. -/
@[expose] public def smithBinaryOutputSizeWorkBound {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) : Nat :=
  smithOutputEncodingLengthBound n
    (smithOutputMatrixBitLength (smithExecution A hdet).value)

public theorem smithBinaryOutputSize_le_workBound {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    smithOutputEncodingLength (smithExecution A hdet).value ≤
      smithBinaryOutputSizeWorkBound A hdet :=
  smithOutputEncodingLength_le_bound (smithExecution A hdet).value

public theorem smithOutputEncodingLength_le_polynomialWorkBound {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    smithOutputEncodingLength (smithExecution A hdet).value ≤
      smithOutputEncodingLengthBound n
        (smithOutputPolynomialEntryBitBound n (matrixBitLength A)) := by
  rw [smithExecution_value]
  have sBound := smith_result_bitLength_le_polynomial A hdet
  have transformBound := smith_transformBitLength_le_polynomial A hdet
  have uBound :
      matrixBitLength (smith A hdet).U ≤
        smithCertificatePolynomialBitLengthBound n (matrixBitLength A) :=
    (le_max_left _ _).trans transformBound
  have uinvBound :
      matrixBitLength (smith A hdet).U_cert.inverse ≤
        smithCertificatePolynomialBitLengthBound n (matrixBitLength A) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans transformBound
  have vBound :
      matrixBitLength (smith A hdet).V ≤
        smithCertificatePolynomialBitLengthBound n (matrixBitLength A) :=
    ((le_max_left _ _).trans <| (le_max_right _ _).trans
      (le_max_right _ _)).trans transformBound
  have vinvBound :
      matrixBitLength (smith A hdet).V_cert.inverse ≤
        smithCertificatePolynomialBitLengthBound n (matrixBitLength A) :=
    ((le_max_right _ _).trans <| (le_max_right _ _).trans
      (le_max_right _ _)).trans transformBound
  let bits := smithOutputPolynomialEntryBitBound n (matrixBitLength A)
  have common :
      smithOutputMatrixBitLength (smith A hdet) ≤ bits := by
    dsimp only [smithOutputMatrixBitLength, smithOutputPolynomialEntryBitBound,
      bits]
    exact max_le
      (sBound.trans (le_max_left _ _))
      (max_le
        (uBound.trans (le_max_right _ _))
        (max_le
          (uinvBound.trans (le_max_right _ _))
          (max_le
            (vBound.trans (le_max_right _ _))
            (vinvBound.trans (le_max_right _ _)))))
  exact (smithOutputEncodingLength_le_bound (smith A hdet)).trans <| by
    unfold smithOutputEncodingLengthBound matrixEncodingLengthBound
    gcongr

private theorem envelope_le_matrixBinarySize
    {f : Nat → Nat → Nat} (envelope : PolyEnvelope f)
    (packed : PackedMatrix) :
    f packed.n (matrixBitLength packed.matrix) ≤
      2 ^ envelope.degree *
        (matrixBinarySize packed + 1) ^ envelope.degree := by
  have dimensionLe := packedMatrix_dimension_le_binarySize packed
  have matrixLe := matrixBitLength_le_binarySize packed
  have baseLe :
      polyBase packed.n (matrixBitLength packed.matrix) ≤
        2 * (matrixBinarySize packed + 1) := by
    unfold polyBase
    omega
  calc
    f packed.n (matrixBitLength packed.matrix) ≤
        polyBase packed.n (matrixBitLength packed.matrix) ^
          envelope.degree :=
      envelope.bound _ _
    _ ≤ (2 * (matrixBinarySize packed + 1)) ^ envelope.degree :=
      Nat.pow_le_pow_left baseLe envelope.degree
    _ = 2 ^ envelope.degree *
        (matrixBinarySize packed + 1) ^ envelope.degree := by
      rw [Nat.mul_pow]

@[expose] public def smithCostPolynomialDegree : Nat :=
  PolynomialBounds.smithExecutionPolynomial.degree

@[expose] public def smithCostPolynomialCoefficient : Nat :=
  2 ^ smithCostPolynomialDegree

@[expose] public def smithOutputPolynomialDegree : Nat :=
  PolynomialBounds.smithOutputEncodingPolynomial.degree

@[expose] public def smithOutputPolynomialCoefficient : Nat :=
  2 ^ smithOutputPolynomialDegree

public theorem smithCost_le_binarySizePolynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithWithCost A hdet).cost ≤
      smithCostPolynomialCoefficient *
        (matrixBinarySize ⟨n, A⟩ + 1) ^ smithCostPolynomialDegree := by
  exact (smithWithCost_cost_le_workBound A hdet).trans <| by
    simpa [smithArithmeticWorkBound, smithCostPolynomialCoefficient,
      smithCostPolynomialDegree] using
      envelope_le_matrixBinarySize
        PolynomialBounds.smithExecutionPolynomial
        (⟨n, A⟩ : PackedMatrix)

public theorem smithOutputEncodingLength_le_binarySizePolynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    smithOutputEncodingLength (smithExecution A hdet).value ≤
      smithOutputPolynomialCoefficient *
        (matrixBinarySize ⟨n, A⟩ + 1) ^ smithOutputPolynomialDegree := by
  exact (smithOutputEncodingLength_le_polynomialWorkBound A hdet).trans <| by
    simpa [smithOutputPolynomialCoefficient, smithOutputPolynomialDegree]
      using
        envelope_le_matrixBinarySize
          PolynomialBounds.smithOutputEncodingPolynomial
          (⟨n, A⟩ : PackedMatrix)

public theorem smithCost_le_encodingLengthPolynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (smithWithCost A hdet).cost ≤
      smithCostPolynomialCoefficient *
        (matrixEncodingLength ⟨n, A⟩ + 1) ^ smithCostPolynomialDegree := by
  apply (smithCost_le_binarySizePolynomial A hdet).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  rw [matrixEncodingLength_eq]
  omega

public theorem smithOutputEncodingLength_le_encodingLengthPolynomial {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    smithOutputEncodingLength (smithExecution A hdet).value ≤
      smithOutputPolynomialCoefficient *
        (matrixEncodingLength ⟨n, A⟩ + 1) ^
          smithOutputPolynomialDegree := by
  apply (smithOutputEncodingLength_le_binarySizePolynomial A hdet).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  rw [matrixEncodingLength_eq]
  omega

public theorem smithCost_polynomial_in_binarySize :
    ∃ C d, ∀ {n : Nat} (A : Matrix (Fin n) (Fin n) Int)
      (hdet : A.det ≠ 0),
      (smithWithCost A hdet).cost ≤
        C * (matrixBinarySize ⟨n, A⟩ + 1) ^ d :=
  ⟨smithCostPolynomialCoefficient, smithCostPolynomialDegree,
    smithCost_le_binarySizePolynomial⟩

public theorem smithOutputSize_polynomial_in_binarySize :
    ∃ C d, ∀ {n : Nat} (A : Matrix (Fin n) (Fin n) Int)
      (hdet : A.det ≠ 0),
      smithOutputBinarySize (smithExecution A hdet).value ≤
        C * (matrixBinarySize ⟨n, A⟩ + 1) ^ d := by
  refine ⟨smithOutputPolynomialCoefficient, smithOutputPolynomialDegree,
    ?_⟩
  intro n A hdet
  have encoded :=
    smithOutputEncodingLength_le_binarySizePolynomial A hdet
  rw [smithOutputEncodingLength_eq] at encoded
  omega

public theorem smithCost_polynomial_in_encodingLength :
    ∃ C d, ∀ {n : Nat} (A : Matrix (Fin n) (Fin n) Int)
      (hdet : A.det ≠ 0),
      (smithWithCost A hdet).cost ≤
        C * (matrixEncodingLength ⟨n, A⟩ + 1) ^ d :=
  ⟨smithCostPolynomialCoefficient, smithCostPolynomialDegree,
    smithCost_le_encodingLengthPolynomial⟩

public theorem smithOutputEncodingLength_polynomial :
    ∃ C d, ∀ {n : Nat} (A : Matrix (Fin n) (Fin n) Int)
      (hdet : A.det ≠ 0),
      smithOutputEncodingLength (smithExecution A hdet).value ≤
        C * (matrixEncodingLength ⟨n, A⟩ + 1) ^ d :=
  ⟨smithOutputPolynomialCoefficient, smithOutputPolynomialDegree,
    smithOutputEncodingLength_le_encodingLengthPolynomial⟩

/--
Bundled, data-producing arithmetic endpoint.  Its charged cost is exactly the
flat leaf fold; encoding length is measured in the concrete self-delimiting
binary alphabet.
-/
public structure VerifiedSmithPolynomialBitCostResult {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) where
  run : SmithExecution A
  value_smith : run.value = smith A hdet
  equation : run.value.U * A * run.value.V = run.value.S
  inverseEquation :
    run.value.U_cert.inverse * run.value.S *
      run.value.V_cert.inverse = A
  leftInverse : run.value.U_cert.inverse * run.value.U = 1
  leftRightInverse : run.value.U * run.value.U_cert.inverse = 1
  rightInverse : run.value.V_cert.inverse * run.value.V = 1
  rightRightInverse : run.value.V * run.value.V_cert.inverse = 1
  isSmith : IsSmithNormalFormFin run.value.S
  canonical : run.value.S = (smithNormalFormFin A).S
  arithmeticCost : Nat
  arithmeticCost_eq : arithmeticCost = traceBitCost run.charges
  arithmeticCost_le_polynomial :
    arithmeticCost ≤ smithCostPolynomialCoefficient *
      (matrixEncodingLength ⟨n, A⟩ + 1) ^ smithCostPolynomialDegree
  outputEncodingLength_le_polynomial :
    smithOutputEncodingLength run.value ≤
      smithOutputPolynomialCoefficient *
        (matrixEncodingLength ⟨n, A⟩ + 1) ^
          smithOutputPolynomialDegree

/--
Fixed-polynomial binary arithmetic cost endpoint for the value-producing
instrumented execution; decoding, serialization, storage, traversal, and
runtime-system costs are outside this arithmetic model.
-/
@[expose] public def verifiedSmithPolynomialBitCost {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    VerifiedSmithPolynomialBitCostResult A hdet := by
  let run := smithExecution A hdet
  exact
    { run
      value_smith := smithExecution_value A hdet
      equation := (smithExecution_replay A hdet).1
      inverseEquation := (smithExecution_replay A hdet).2
      leftInverse := (smithExecution_inverse_identities A hdet).1
      leftRightInverse := (smithExecution_inverse_identities A hdet).2.1
      rightInverse := (smithExecution_inverse_identities A hdet).2.2.1
      rightRightInverse := (smithExecution_inverse_identities A hdet).2.2.2
      isSmith := run.value.isSmith
      canonical := smithExecution_eq_reference A hdet
      arithmeticCost := traceBitCost run.charges
      arithmeticCost_eq := rfl
      arithmeticCost_le_polynomial := by
        simpa [smithWithCost, run] using
          smithCost_le_encodingLengthPolynomial A hdet
      outputEncodingLength_le_polynomial := by
        simpa [run] using
          smithOutputEncodingLength_le_encodingLengthPolynomial A hdet }

end NormalForms.Research.KannanBachem
