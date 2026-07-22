/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalPolynomialBound
import all NormalForms.Research.KannanBachem.Hermite.PrincipalPolynomialBound

/-! Polynomial bounds for every forward and inverse multiplier prefix. -/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix

namespace Principal

theorem matrixListHeight_size_le_of_mem {m n bound : Nat}
    (matrices : List (_root_.Matrix (Fin m) (Fin n) Int))
    (all_le : ∀ matrix ∈ matrices, matrixBitLength matrix ≤ bound) :
    Nat.size (matrixListHeight matrices) ≤ bound := by
  induction matrices with
  | nil => simp [matrixListHeight]
  | cons head tail ih =>
      rw [matrixListHeight, natSize_max]
      exact max_le
        (all_le head (by simp))
        (ih fun matrix member => all_le matrix (by simp [member]))

theorem RowTrace.intermediates_mul_mem {n : Nat}
    (steps : RowTrace Int n)
    (A currentLeft currentMatrix : _root_.Matrix (Fin n) (Fin n) Int)
    (equation : currentLeft * A = currentMatrix)
    {left : _root_.Matrix (Fin n) (Fin n) Int}
    (member : left ∈ steps.intermediates currentLeft) :
    left * A ∈ steps.intermediates currentMatrix := by
  induction steps generalizing currentLeft currentMatrix with
  | nil =>
      simp only [RowTrace.intermediates, List.mem_singleton] at member ⊢
      subst left
      exact equation
  | cons step tail ih =>
      simp only [RowTrace.intermediates, List.mem_cons] at member ⊢
      rcases member with rfl | member
      · exact Or.inl equation
      · apply Or.inr
        apply ih (step.forward * currentLeft) (step.forward * currentMatrix)
        · calc
            (step.forward * currentLeft) * A =
                step.forward * (currentLeft * A) := by
              rw [_root_.Matrix.mul_assoc]
            _ = step.forward * currentMatrix := by rw [equation]
        · exact member

theorem RowTrace.intermediateMultiplier_mul_mem {n : Nat}
    (steps : RowTrace Int n) (A : _root_.Matrix (Fin n) (Fin n) Int)
    {left : _root_.Matrix (Fin n) (Fin n) Int}
    (member : left ∈ steps.intermediates 1) :
    left * A ∈ steps.intermediates A := by
  apply RowTrace.intermediates_mul_mem steps A 1 A
  · exact NormalForms.Matrix.Constructive.one_mul A
  · exact member

theorem RowTrace.inverseIntermediates_mul_exists {n : Nat}
    (steps : RowTrace Int n)
    (A currentInverse currentMatrix : _root_.Matrix (Fin n) (Fin n) Int)
    (equation : currentInverse * currentMatrix = A)
    {inverse : _root_.Matrix (Fin n) (Fin n) Int}
    (member : inverse ∈ steps.inverseIntermediatesFrom currentInverse) :
    ∃ matrix ∈ steps.intermediates currentMatrix, inverse * matrix = A := by
  induction steps generalizing currentInverse currentMatrix with
  | nil =>
      simp only [RowTrace.inverseIntermediatesFrom, List.mem_singleton] at member
      subst inverse
      exact ⟨currentMatrix, by simp [RowTrace.intermediates], equation⟩
  | cons step tail ih =>
      simp only [RowTrace.inverseIntermediatesFrom, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨currentMatrix, by simp [RowTrace.intermediates], equation⟩
      · have nextEquation :
            (currentInverse * step.backward) *
                (step.forward * currentMatrix) = A := by
          calc
            (currentInverse * step.backward) *
                  (step.forward * currentMatrix) =
                currentInverse *
                  ((step.backward * step.forward) * currentMatrix) := by
              simp only [_root_.Matrix.mul_assoc]
            _ = currentInverse * (1 * currentMatrix) := by
              rw [step.backward_forward]
            _ = currentInverse * currentMatrix := by
              rw [NormalForms.Matrix.Constructive.one_mul]
            _ = A := equation
        rcases ih (currentInverse * step.backward)
            (step.forward * currentMatrix) nextEquation member with
          ⟨matrix, matrixMember, inverseEquation⟩
        exact ⟨matrix, by
          exact List.mem_cons_of_mem currentMatrix matrixMember,
          inverseEquation⟩

theorem RowTrace.intermediateInverse_mul_exists {n : Nat}
    (steps : RowTrace Int n) (A : _root_.Matrix (Fin n) (Fin n) Int)
    {inverse : _root_.Matrix (Fin n) (Fin n) Int}
    (member : inverse ∈ steps.inverseIntermediatesFrom 1) :
    ∃ matrix ∈ steps.intermediates A, inverse * matrix = A := by
  apply RowTrace.inverseIntermediates_mul_exists steps A 1 A
  · exact NormalForms.Matrix.Constructive.one_mul A
  · exact member

theorem PrincipalReady.det_ne {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int} (ready : PrincipalReady A) :
    A.det ≠ 0 := by
  have full := ready n le_rfl
  simpa [leadingSubmatrix] using full

/-- Closed polynomial bit budget for every accumulated forward multiplier. -/
@[expose] public def principalMultiplierPrefixPolynomialBitLengthBound
    (dimension inputBits : Nat) : Nat :=
  match dimension with
  | 0 => 0
  | order + 1 =>
      (order + 1) + principalPolynomialBitLengthBound (order + 1) inputBits +
        (order * (order + inputBits) + 2)

/-- Closed polynomial bit budget for every directly accumulated inverse. -/
@[expose] public def principalInversePrefixPolynomialBitLengthBound
    (dimension inputBits : Nat) : Nat :=
  match dimension with
  | 0 => 0
  | order + 1 =>
      (order + 1) + inputBits +
        (order *
          (order + principalPolynomialBitLengthBound (order + 1) inputBits) + 2)

theorem forwardPrefix_bitLength_le_polynomial {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (ready : PrincipalReady A)
    (left : _root_.Matrix (Fin n) (Fin n) Int)
    (member : left ∈ (principalRun A).steps.intermediates 1) :
    matrixBitLength left ≤
      principalMultiplierPrefixPolynomialBitLengthBound n
        (matrixBitLength A) := by
  cases n with
  | zero =>
      have zeroMatrix : left =
          (0 : _root_.Matrix (Fin 0) (Fin 0) Int) := Subsingleton.elim _ _
      rw [zeroMatrix, matrixBitLength_zero]
      rfl
  | succ order =>
      have transformedMember :=
        RowTrace.intermediateMultiplier_mul_mem (principalRun A).steps A member
      have transformedHeight : matrixHeight (left * A) ≤
          principalIntermediateMatrixHeight A :=
        matrixHeight_le_matrixListHeight_of_mem transformedMember
      have transformedBits : matrixBitLength (left * A) ≤
          Principal.principalPolynomialBitLengthBound (order + 1)
            (matrixBitLength A) :=
        (Nat.size_le_size transformedHeight).trans
          (principalIntermediateMatrixBitLength_le_polynomial_of_ready A ready)
      have cramer := leftMultiplier_bitLength_le_of_mul_eq
        A left (left * A) rfl ready.det_ne
      have dimensionSize : Nat.size (order + 1) ≤ order + 1 :=
        natSize_le_self _
      have determinantBits :=
        determinantBitLengthBound_le_polynomial order (matrixBitLength A)
      change matrixBitLength left ≤
        (order + 1) +
          principalPolynomialBitLengthBound (order + 1) (matrixBitLength A) +
          (order * (order + matrixBitLength A) + 2)
      exact cramer.trans <| by
        omega

theorem inversePrefix_bitLength_le_polynomial {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (ready : PrincipalReady A)
    (inverse : _root_.Matrix (Fin n) (Fin n) Int)
    (member : inverse ∈
      (principalRun A).steps.inverseIntermediatesFrom 1) :
    matrixBitLength inverse ≤
      principalInversePrefixPolynomialBitLengthBound n
        (matrixBitLength A) := by
  cases n with
  | zero =>
      have zeroMatrix : inverse =
          (0 : _root_.Matrix (Fin 0) (Fin 0) Int) := Subsingleton.elim _ _
      rw [zeroMatrix, matrixBitLength_zero]
      rfl
  | succ order =>
      rcases RowTrace.intermediateInverse_mul_exists
          (principalRun A).steps A member with
        ⟨matrix, matrixMember, inverseEquation⟩
      have matrixHeightBound : matrixHeight matrix ≤
          principalIntermediateMatrixHeight A :=
        matrixHeight_le_matrixListHeight_of_mem matrixMember
      have matrixBits : matrixBitLength matrix ≤
          principalPolynomialBitLengthBound (order + 1)
            (matrixBitLength A) :=
        (Nat.size_le_size matrixHeightBound).trans
          (principalIntermediateMatrixBitLength_le_polynomial_of_ready A ready)
      have matrixDetNe : matrix.det ≠ 0 := by
        intro matrixDetZero
        apply ready.det_ne
        rw [← inverseEquation, _root_.Matrix.det_mul, matrixDetZero, mul_zero]
      have cramer := leftMultiplier_bitLength_le_of_mul_eq
        matrix inverse A inverseEquation matrixDetNe
      have dimensionSize : Nat.size (order + 1) ≤ order + 1 :=
        natSize_le_self _
      have determinantBits :
          determinantBitLengthBound order (matrixBitLength matrix) ≤
            order *
                (order + principalPolynomialBitLengthBound (order + 1)
                  (matrixBitLength A)) + 2 :=
        (determinantBitLengthBound_le_polynomial order
          (matrixBitLength matrix)).trans <| by
            exact Nat.add_le_add_right
              (Nat.mul_le_mul_left order
                (Nat.add_le_add_left matrixBits order)) 2
      change matrixBitLength inverse ≤
        (order + 1) + matrixBitLength A +
          (order *
            (order + principalPolynomialBitLengthBound (order + 1)
              (matrixBitLength A)) + 2)
      exact cramer.trans <| by
        omega

end Principal

/-- Every accumulated forward multiplier prefix has polynomial bit length. -/
public theorem principalIntermediateMultiplierBitLength_le_polynomial_of_ready
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    principalIntermediateMultiplierBitLength A ≤
      Principal.principalMultiplierPrefixPolynomialBitLengthBound n
        (matrixBitLength A) := by
  unfold principalIntermediateMultiplierBitLength
    principalIntermediateMultiplierHeight
    RowTrace.intermediateMultiplierHeight
  apply Principal.matrixListHeight_size_le_of_mem
  intro left member
  exact Principal.forwardPrefix_bitLength_le_polynomial A ready left member

/-- Every directly accumulated inverse prefix has polynomial bit length. -/
public theorem principalIntermediateInverseBitLength_le_polynomial_of_ready
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Int)
    (ready : Principal.PrincipalReady A) :
    principalIntermediateInverseBitLength A ≤
      Principal.principalInversePrefixPolynomialBitLengthBound n
        (matrixBitLength A) := by
  unfold principalIntermediateInverseBitLength
    principalIntermediateInverseHeight
    RowTrace.intermediateInverseMultiplierHeight
  apply Principal.matrixListHeight_size_le_of_mem
  intro inverse member
  exact Principal.inversePrefix_bitLength_le_polynomial A ready inverse member

end NormalForms.Research.KannanBachem.Hermite
