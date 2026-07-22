/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.BoundedColumn
public import NormalForms.Research.KannanBachem.Hermite.PrincipalMultiplierBound
import all NormalForms.Research.KannanBachem.Smith.BoundedColumn
import all NormalForms.Research.KannanBachem.Hermite.PrincipalMultiplierBound

/-!
# Polynomial coefficient bounds for one-column Smith reduction

Every primitive boundary, transformed matrix, accumulated multiplier, and
explicit inverse in Step 4 receives a closed polynomial bit-length bound.
-/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite
open NormalForms.Research.KannanBachem.Hermite

namespace BoundedColumn

open Principal

theorem boundedIntXGCD_gcd_natAbs_le_max (a b : Int) :
    (boundedIntXGCD a b).gcd.natAbs ≤ max a.natAbs b.natAbs := by
  rw [boundedIntXGCD_gcd]
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst a
      subst b
      simp
    · exact (Int.gcd_le_natAbs_right a hb).trans (le_max_right _ _)
  · exact (Int.gcd_le_natAbs_left b ha).trans (le_max_left _ _)

theorem loop_row_unchanged {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : Transform A) →
      (row column : Fin (n + 1)) → k < row.val →
        (loop k hk state).B row column = state.B row column
  | 0, _hk, _state, _row, _column, _hrow => rfl
  | k + 1, hk, state, row, column, hrow => by
      rw [loop]
      let previous := loop k (by omega) state
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      have rowNeZero : row ≠ (0 : Fin (n + 1)) := by
        apply ne_of_gt
        change 0 < row.val
        omega
      have rowNeTarget : row ≠ target := by
        intro equality
        have := congrArg Fin.val equality
        simp [target] at this
        omega
      rw [pairAtFirstColumn_other_apply target row (by simp [target])
        rowNeZero rowNeTarget previous column]
      exact loop_row_unchanged k (by omega) state row column (by omega)

theorem loop_pivot_natAbs_le_height {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : Transform A) →
      ((loop k hk state).B 0 0).natAbs ≤ matrixHeight state.B
  | 0, _hk, state => entry_natAbs_le_matrixHeight state.B 0 0
  | k + 1, hk, state => by
      rw [loop, pairAtFirstColumn_pivot]
      let previous := loop k (by omega) state
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      apply (boundedIntXGCD_gcd_natAbs_le_max _ _).trans
      apply max_le
      · exact loop_pivot_natAbs_le_height k (by omega) state
      · rw [loop_row_unchanged k (by omega) state target 0 (by simp [target])]
        exact entry_natAbs_le_matrixHeight state.B target 0

theorem boundedBezoutReductionMatrix_entry_natAbs_le_of_inputs
    (a b : Int) (height : Nat)
    (ha : a.natAbs ≤ height) (hb : b.natAbs ≤ height)
    (row column : Fin 2) :
    (boundedBezoutReductionMatrix a b row column).natAbs ≤
      (height + 1) ^ 2 := by
  by_cases bothZero : a = 0 ∧ b = 0
  · rcases bothZero with ⟨rfl, rfl⟩
    fin_cases row <;> fin_cases column <;>
      simp [boundedBezoutReductionMatrix] <;> nlinarith
  · have notBothZero : a ≠ 0 ∨ b ≠ 0 := by
      by_cases ha0 : a = 0
      · exact Or.inr fun hb0 => bothZero ⟨ha0, hb0⟩
      · exact Or.inl ha0
    exact (boundedBezoutReductionMatrix_entry_natAbs_le a b notBothZero row column).trans <| by
      unfold boundedIntXGCDCoefficientHeight
      exact Nat.pow_le_pow_left (Nat.add_le_add_right (max_le ha hb) 1) 2

def stepMatrixHeightBound (height : Nat) : Nat :=
  2 * (height + 1) ^ 2 + 1

theorem one_entry_natAbs_le (dimension : Nat) (row column : Fin dimension) :
    ((1 : Matrix (Fin dimension) (Fin dimension) Int) row column).natAbs ≤ 1 := by
  by_cases equality : row = column <;> simp [Matrix.one_apply, equality]

theorem boundedPairBezoutMatrix_height_le {dimension : Nat}
    (pivot target : Fin dimension) (hne : pivot ≠ target)
    (a b : Int) (height : Nat)
    (ha : a.natAbs ≤ height) (hb : b.natAbs ≤ height) :
    matrixHeight (boundedPairBezoutMatrix pivot target a b) ≤
      stepMatrixHeightBound height := by
  apply matrixHeight_le
  intro row column
  let coefficientBound := (height + 1) ^ 2
  have coefficient : ∀ i j : Fin 2,
      (boundedBezoutReductionMatrix a b i j).natAbs ≤ coefficientBound := by
    intro i j
    exact boundedBezoutReductionMatrix_entry_natAbs_le_of_inputs
      a b height ha hb i j
  by_cases rowPivot : row = pivot
  · subst row
    rw [boundedPairBezoutMatrix,
      twoRowLiftMatrix_apply_pivot pivot target hne]
    calc
      (boundedBezoutReductionMatrix a b 0 0 *
            (1 : Matrix (Fin dimension) (Fin dimension) Int) pivot column +
          boundedBezoutReductionMatrix a b 0 1 *
            (1 : Matrix (Fin dimension) (Fin dimension) Int) target column).natAbs ≤
          (boundedBezoutReductionMatrix a b 0 0).natAbs *
              ((1 : Matrix (Fin dimension) (Fin dimension) Int) pivot column).natAbs +
            (boundedBezoutReductionMatrix a b 0 1).natAbs *
              ((1 : Matrix (Fin dimension) (Fin dimension) Int) target column).natAbs := by
        simpa only [Int.natAbs_mul] using Int.natAbs_add_le
          (boundedBezoutReductionMatrix a b 0 0 *
            (1 : Matrix (Fin dimension) (Fin dimension) Int) pivot column)
          (boundedBezoutReductionMatrix a b 0 1 *
            (1 : Matrix (Fin dimension) (Fin dimension) Int) target column)
      _ ≤ coefficientBound * 1 + coefficientBound * 1 :=
        Nat.add_le_add
          (Nat.mul_le_mul (coefficient 0 0)
            (one_entry_natAbs_le dimension pivot column))
          (Nat.mul_le_mul (coefficient 0 1)
            (one_entry_natAbs_le dimension target column))
      _ ≤ stepMatrixHeightBound height := by
        unfold coefficientBound stepMatrixHeightBound
        omega
  · by_cases rowTarget : row = target
    · subst row
      rw [boundedPairBezoutMatrix, twoRowLiftMatrix_apply_target]
      calc
        (boundedBezoutReductionMatrix a b 1 0 *
              (1 : Matrix (Fin dimension) (Fin dimension) Int) pivot column +
            boundedBezoutReductionMatrix a b 1 1 *
              (1 : Matrix (Fin dimension) (Fin dimension) Int) target column).natAbs ≤
            (boundedBezoutReductionMatrix a b 1 0).natAbs *
                ((1 : Matrix (Fin dimension) (Fin dimension) Int) pivot column).natAbs +
              (boundedBezoutReductionMatrix a b 1 1).natAbs *
                ((1 : Matrix (Fin dimension) (Fin dimension) Int) target column).natAbs := by
          simpa only [Int.natAbs_mul] using Int.natAbs_add_le
            (boundedBezoutReductionMatrix a b 1 0 *
              (1 : Matrix (Fin dimension) (Fin dimension) Int) pivot column)
            (boundedBezoutReductionMatrix a b 1 1 *
              (1 : Matrix (Fin dimension) (Fin dimension) Int) target column)
        _ ≤ coefficientBound * 1 + coefficientBound * 1 :=
          Nat.add_le_add
            (Nat.mul_le_mul (coefficient 1 0)
              (one_entry_natAbs_le dimension pivot column))
            (Nat.mul_le_mul (coefficient 1 1)
              (one_entry_natAbs_le dimension target column))
        _ ≤ stepMatrixHeightBound height := by
          unfold coefficientBound stepMatrixHeightBound
          omega
    · rw [boundedPairBezoutMatrix,
        twoRowLiftMatrix_apply_other pivot target row rowPivot rowTarget]
      exact (one_entry_natAbs_le dimension row column).trans <| by
        unfold stepMatrixHeightBound
        omega

def stepHeightFactor (dimension height : Nat) : Nat :=
  dimension * stepMatrixHeightBound height + 1

def intermediateHeightBound (dimension steps height : Nat) : Nat :=
  height * stepHeightFactor dimension height ^ steps

theorem pairAtFirstColumn_height_le {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (target : Fin (n + 1)) (hne : (0 : Fin (n + 1)) ≠ target)
    (state : Transform A) (inputHeight currentBound : Nat)
    (pivotBound : (state.B 0 0).natAbs ≤ inputHeight)
    (targetBound : (state.B target 0).natAbs ≤ inputHeight)
    (currentHeight : matrixHeight state.B ≤ currentBound) :
    matrixHeight (pairAtFirstColumn target hne state).B ≤
      stepHeightFactor (n + 1) inputHeight * currentBound := by
  change matrixHeight
      (boundedPairBezoutMatrix 0 target (state.B 0 0) (state.B target 0) *
        state.B) ≤ _
  exact (matrix_mul_height_le _ _).trans <| by
    have forwardHeight := boundedPairBezoutMatrix_height_le 0 target hne
      (state.B 0 0) (state.B target 0) inputHeight pivotBound targetBound
    calc
      (n + 1) *
          (matrixHeight
              (boundedPairBezoutMatrix 0 target (state.B 0 0)
                (state.B target 0)) * matrixHeight state.B) ≤
        (n + 1) * (stepMatrixHeightBound inputHeight * currentBound) := by
          gcongr
      _ ≤ stepHeightFactor (n + 1) inputHeight * currentBound := by
        unfold stepHeightFactor
        nlinarith

theorem loop_height_le {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : Transform A) →
      matrixHeight (loop k hk state).B ≤
        intermediateHeightBound (n + 1) k (matrixHeight state.B)
  | 0, _hk, _state => by
      change matrixHeight _state.B ≤ _
      simp [intermediateHeightBound]
  | k + 1, hk, state => by
      let previous := loop k (by omega) state
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      have previousHeight := loop_height_le k (by omega) state
      have pivotBound := loop_pivot_natAbs_le_height k (by omega) state
      have targetUnchanged : previous.B target 0 = state.B target 0 :=
        loop_row_unchanged k (by omega) state target 0 (by simp [target])
      have targetBound : (previous.B target 0).natAbs ≤ matrixHeight state.B := by
        rw [targetUnchanged]
        exact entry_natAbs_le_matrixHeight state.B target 0
      have next := pairAtFirstColumn_height_le target (by simp [target]) previous
        (matrixHeight state.B)
        (intermediateHeightBound (n + 1) k (matrixHeight state.B))
        pivotBound targetBound previousHeight
      rw [loop]
      exact next.trans_eq <| by
        unfold intermediateHeightBound
        rw [pow_succ]
        ring

theorem unitScale_height_le {dimension columns : Nat}
    (B : Matrix (Fin dimension) (Fin columns) Int)
    (row : Fin dimension) (unit : Intˣ) :
    matrixHeight (applyRowOperation B (.smul row (unit : Int))) ≤ matrixHeight B := by
  apply matrixHeight_le
  intro current column
  by_cases equality : current = row
  · subst current
    simp only [applyRowOperation, if_pos]
    rw [Int.natAbs_mul, Int.units_natAbs, one_mul]
    exact entry_natAbs_le_matrixHeight B row column
  · simpa [applyRowOperation, equality] using
      entry_natAbs_le_matrixHeight B current column

theorem compute_height_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    matrixHeight (compute A).B ≤
      intermediateHeightBound (n + 1) n (matrixHeight A) := by
  let reduced := loop n le_rfl (Transform.refl A)
  have reducedHeight := loop_height_le n le_rfl (Transform.refl A)
  have normalizedHeight := unitScale_height_le reduced.B 0
    (ComputableEuclideanOps.normUnitUnit (reduced.B 0 0))
  change matrixHeight
      (applyRowOperation reduced.B
        (.smul 0 ((ComputableEuclideanOps.normUnitUnit (reduced.B 0 0) : Int)))) ≤ _
  exact normalizedHeight.trans <| by
    simpa [reduced, Transform.refl] using reducedHeight

theorem intermediateHeightBound_le_succ (dimension steps height : Nat) :
    intermediateHeightBound dimension steps height ≤
      intermediateHeightBound dimension (steps + 1) height := by
  unfold intermediateHeightBound
  rw [pow_succ]
  have factorPositive : 1 ≤ stepHeightFactor dimension height := by
    unfold stepHeightFactor
    omega
  calc
    height * stepHeightFactor dimension height ^ steps =
        (height * stepHeightFactor dimension height ^ steps) * 1 := by omega
    _ ≤ (height * stepHeightFactor dimension height ^ steps) *
          stepHeightFactor dimension height :=
      Nat.mul_le_mul_left _ factorPositive
    _ = height *
          (stepHeightFactor dimension height ^ steps *
            stepHeightFactor dimension height) := by ring

theorem Transform.replay_eq {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (state : Transform A) : state.steps.replay A = state.B := by
  rw [RowTrace.replay_eq_accumulator_mul, state.accumulator_eq]
  exact state.equation

theorem singleton_intermediateHeight_le {dimension columns bound : Nat}
    (A B : Matrix (Fin dimension) (Fin columns) Int)
    (step : ReversibleRowStep Int dimension)
    (equation : step.forward * A = B)
    (aBound : matrixHeight A ≤ bound)
    (bBound : matrixHeight B ≤ bound) :
    RowTrace.intermediateMatrixHeight A ([step] : RowTrace Int dimension) ≤
      bound := by
  simp [RowTrace.intermediateMatrixHeight, RowTrace.intermediates,
    matrixListHeight, equation, aBound, bBound]

theorem loop_refl_intermediateHeight_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (k : Nat) → (hk : k ≤ n) →
      (loop k hk (Transform.refl A)).steps.intermediateMatrixHeight A ≤
        intermediateHeightBound (n + 1) k (matrixHeight A)
  | 0, _hk => by
      simp [loop, Transform.refl, RowTrace.intermediateMatrixHeight,
        RowTrace.intermediates, matrixListHeight, intermediateHeightBound]
  | k + 1, hk => by
      let previous := loop k (by omega) (Transform.refl A)
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      let step := ReversibleRowStep.ofCertificate .bezoutPair
        (boundedPairBezoutMatrixInverseCertificate 0 target (by simp [target])
          (previous.B 0 0) (previous.B target 0))
      have previousIntermediate := loop_refl_intermediateHeight_le A k (by omega)
      have previousBound : matrixHeight previous.B ≤
          intermediateHeightBound (n + 1) (k + 1) (matrixHeight A) :=
        (loop_height_le k (by omega) (Transform.refl A)).trans
          (intermediateHeightBound_le_succ (n + 1) k (matrixHeight A))
      have nextBound : matrixHeight (pairAtFirstColumn target
            (by simp [target]) previous).B ≤
          intermediateHeightBound (n + 1) (k + 1) (matrixHeight A) :=
        loop_height_le (k + 1) hk (Transform.refl A)
      have stepEquation : step.forward * previous.B =
          (pairAtFirstColumn target (by simp [target]) previous).B := rfl
      have singletonBound := singleton_intermediateHeight_le previous.B
        (pairAtFirstColumn target (by simp [target]) previous).B step
        stepEquation previousBound nextBound
      have appended := RowTrace.intermediateMatrixHeight_append_le A
        previous.steps [step]
        (previousIntermediate.trans
          (intermediateHeightBound_le_succ (n + 1) k (matrixHeight A)))
        (by rw [Transform.replay_eq previous]
            exact singletonBound)
      simpa [loop, pairAtFirstColumn, Transform.trans, Transform.ofPrimitive,
        previous, target, step] using appended

theorem unitScale_singleton_intermediateHeight_le {dimension columns : Nat}
    (B : Matrix (Fin dimension) (Fin columns) Int)
    (row : Fin dimension) (unit : Intˣ) :
    let step := ReversibleRowStep.ofCertificate .unitScale
      (rowUnitScaleInverseCertificate row unit)
    RowTrace.intermediateMatrixHeight B ([step] : RowTrace Int dimension) ≤
      matrixHeight B := by
  intro step
  apply singleton_intermediateHeight_le B
    (applyRowOperation B (.smul row (unit : Int))) step
  · exact rowOperationMatrix_mul B (.smul row (unit : Int))
  · exact le_rfl
  · exact unitScale_height_le B row unit

theorem compute_intermediateHeight_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (compute A).steps.intermediateMatrixHeight A ≤
      intermediateHeightBound (n + 1) n (matrixHeight A) := by
  let reduced := loop n le_rfl (Transform.refl A)
  let unit := ComputableEuclideanOps.normUnitUnit (reduced.B 0 0)
  let step := ReversibleRowStep.ofCertificate .unitScale
    (rowUnitScaleInverseCertificate (0 : Fin (n + 1)) unit)
  have reducedIntermediate := loop_refl_intermediateHeight_le A n le_rfl
  have normalizedIntermediate := unitScale_singleton_intermediateHeight_le
    reduced.B (0 : Fin (n + 1)) unit
  have reducedHeight := loop_height_le n le_rfl (Transform.refl A)
  have appended := RowTrace.intermediateMatrixHeight_append_le A
    reduced.steps [step] reducedIntermediate
    (by rw [Transform.replay_eq reduced]
        exact normalizedIntermediate.trans reducedHeight)
  simpa [compute, Transform.trans, Transform.unitScale,
    Transform.ofPrimitive, reduced, unit, step] using appended

def stepFactorPolynomialBits (dimension inputBits : Nat) : Nat :=
  Nat.size dimension + 2 * (inputBits + 1) + 6

def intermediatePolynomialBits
    (dimension steps inputBits : Nat) : Nat :=
  inputBits + steps * stepFactorPolynomialBits dimension inputBits + 1

theorem stepMatrixHeightBound_size_le (height : Nat) :
    Nat.size (stepMatrixHeightBound height) ≤
      2 * (Nat.size height + 1) + 4 := by
  unfold stepMatrixHeightBound
  calc
    Nat.size (2 * (height + 1) ^ 2 + 1) ≤
        Nat.size (2 * (height + 1) ^ 2) + 1 :=
      Principal.natSize_succ_le _
    _ ≤ (Nat.size 2 + Nat.size ((height + 1) ^ 2)) + 1 :=
      Nat.add_le_add_right (Principal.natSize_mul_le' _ _) 1
    _ ≤ (2 + (2 * Nat.size (height + 1) + 1)) + 1 := by
      have twoSize : Nat.size 2 = 2 := by decide
      rw [twoSize]
      gcongr
      exact Principal.natSize_pow_le' _ 2
    _ ≤ 2 * (Nat.size height + 1) + 4 := by
      have successor := Principal.natSize_succ_le height
      omega

theorem stepHeightFactor_size_le (dimension height : Nat) :
    Nat.size (stepHeightFactor dimension height) ≤
      stepFactorPolynomialBits dimension (Nat.size height) := by
  unfold stepHeightFactor stepFactorPolynomialBits
  calc
    Nat.size (dimension * stepMatrixHeightBound height + 1) ≤
        Nat.size (dimension * stepMatrixHeightBound height) + 1 :=
      Principal.natSize_succ_le _
    _ ≤ (Nat.size dimension + Nat.size (stepMatrixHeightBound height)) + 1 :=
      Nat.add_le_add_right (Principal.natSize_mul_le' _ _) 1
    _ ≤ Nat.size dimension + 2 * (Nat.size height + 1) + 6 := by
      have matrixSize := stepMatrixHeightBound_size_le height
      omega

theorem intermediateHeightBound_size_le_polynomial
    (dimension steps height : Nat) :
    Nat.size (intermediateHeightBound dimension steps height) ≤
      intermediatePolynomialBits dimension steps (Nat.size height) := by
  unfold intermediateHeightBound intermediatePolynomialBits
  calc
    Nat.size (height * stepHeightFactor dimension height ^ steps) ≤
        Nat.size height +
          Nat.size (stepHeightFactor dimension height ^ steps) :=
      Principal.natSize_mul_le' _ _
    _ ≤ Nat.size height +
          (steps * Nat.size (stepHeightFactor dimension height) + 1) :=
      Nat.add_le_add_left (Principal.natSize_pow_le' _ steps) _
    _ ≤ Nat.size height +
          steps * stepFactorPolynomialBits dimension (Nat.size height) + 1 := by
      have factorSize := stepHeightFactor_size_le dimension height
      exact Nat.add_le_add_left
        (Nat.add_le_add_right (Nat.mul_le_mul_left steps factorSize) 1)
        (Nat.size height)

theorem compute_intermediateBitLength_le_polynomial {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (compute A).steps.intermediateMatrixBitLength A ≤
      intermediatePolynomialBits (n + 1) n (matrixBitLength A) := by
  unfold RowTrace.intermediateMatrixBitLength matrixBitLength
  exact (Nat.size_le_size (compute_intermediateHeight_le A)).trans
    (intermediateHeightBound_size_le_polynomial
      (n + 1) n (matrixHeight A))

def multiplierPolynomialBits (dimension inputBits : Nat) : Nat :=
  match dimension with
  | 0 => 0
  | order + 1 =>
      Nat.size (order + 1) +
        intermediatePolynomialBits (order + 1) order inputBits +
        determinantBitLengthBound order inputBits

def inversePolynomialBits (dimension inputBits : Nat) : Nat :=
  match dimension with
  | 0 => 0
  | order + 1 =>
      Nat.size (order + 1) + inputBits +
        determinantBitLengthBound order
          (intermediatePolynomialBits (order + 1) order inputBits)

theorem compute_forwardPrefix_bitLength_le_polynomial {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0)
    (left : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (member : left ∈ (compute A).steps.intermediates 1) :
    matrixBitLength left ≤ multiplierPolynomialBits (n + 1) (matrixBitLength A) := by
  have transformedMember := Principal.RowTrace.intermediateMultiplier_mul_mem
    (compute A).steps A member
  have transformedHeight := matrixHeight_le_matrixListHeight_of_mem transformedMember
  have transformedBits : matrixBitLength (left * A) ≤
      intermediatePolynomialBits (n + 1) n (matrixBitLength A) :=
    (Nat.size_le_size transformedHeight).trans
      (compute_intermediateBitLength_le_polynomial A)
  have cramer := leftMultiplier_bitLength_le_of_mul_eq A left (left * A) rfl hdet
  change matrixBitLength left ≤
    Nat.size (n + 1) + intermediatePolynomialBits (n + 1) n (matrixBitLength A) +
      determinantBitLengthBound n (matrixBitLength A)
  exact cramer.trans <| by omega

theorem compute_inversePrefix_bitLength_le_polynomial {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0)
    (inverse : Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (member : inverse ∈ (compute A).steps.inverseIntermediatesFrom 1) :
    matrixBitLength inverse ≤ inversePolynomialBits (n + 1) (matrixBitLength A) := by
  rcases Principal.RowTrace.intermediateInverse_mul_exists
      (compute A).steps A member with
    ⟨matrix, matrixMember, inverseEquation⟩
  have matrixHeightBound := matrixHeight_le_matrixListHeight_of_mem matrixMember
  have matrixBits : matrixBitLength matrix ≤
      intermediatePolynomialBits (n + 1) n (matrixBitLength A) :=
    (Nat.size_le_size matrixHeightBound).trans
      (compute_intermediateBitLength_le_polynomial A)
  have matrixDetNe : matrix.det ≠ 0 := by
    intro matrixDetZero
    apply hdet
    rw [← inverseEquation, Matrix.det_mul, matrixDetZero, mul_zero]
  have cramer := leftMultiplier_bitLength_le_of_mul_eq
    matrix inverse A inverseEquation matrixDetNe
  have determinantBits :
      determinantBitLengthBound n (matrixBitLength matrix) ≤
        determinantBitLengthBound n
          (intermediatePolynomialBits (n + 1) n (matrixBitLength A)) := by
    unfold determinantBitLengthBound
    gcongr
  change matrixBitLength inverse ≤
    Nat.size (n + 1) + matrixBitLength A +
      determinantBitLengthBound n
        (intermediatePolynomialBits (n + 1) n (matrixBitLength A))
  exact cramer.trans (Nat.add_le_add_left determinantBits _)

theorem compute_intermediateMultiplierBitLength_le_polynomial {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    (compute A).steps.intermediateMultiplierBitLength ≤
      multiplierPolynomialBits (n + 1) (matrixBitLength A) := by
  unfold RowTrace.intermediateMultiplierBitLength
    RowTrace.intermediateMultiplierHeight RowTrace.intermediateMatrixHeight
  apply Principal.matrixListHeight_size_le_of_mem
  intro left member
  exact compute_forwardPrefix_bitLength_le_polynomial A hdet left member

theorem compute_intermediateInverseBitLength_le_polynomial {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) (hdet : A.det ≠ 0) :
    (compute A).steps.intermediateInverseMultiplierBitLength ≤
      inversePolynomialBits (n + 1) (matrixBitLength A) := by
  unfold RowTrace.intermediateInverseMultiplierBitLength
    RowTrace.intermediateInverseMultiplierHeight
  apply Principal.matrixListHeight_size_le_of_mem
  intro inverse member
  exact compute_inversePrefix_bitLength_le_polynomial A hdet inverse member

theorem arithmeticLoop_operandHeight_le {n : Nat}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int} :
    (k : Nat) → (hk : k ≤ n) → (state : Transform A) →
      (arithmeticLoop k hk state).Forall
        (fun event => event.operandHeight ≤ matrixHeight state.B)
  | 0, _hk, _state => by simp [arithmeticLoop]
  | k + 1, hk, state => by
      let previous := loop k (by omega) state
      let target : Fin (n + 1) := ⟨k + 1, by omega⟩
      rw [arithmeticLoop, List.forall_append]
      constructor
      · exact arithmeticLoop_operandHeight_le k (by omega) state
      · rw [List.forall_cons]
        constructor
        · change max (previous.B 0 0).natAbs (previous.B target 0).natAbs ≤
            matrixHeight state.B
          apply max_le
          · exact loop_pivot_natAbs_le_height k (by omega) state
          · rw [loop_row_unchanged k (by omega) state target 0 (by simp [target])]
            exact entry_natAbs_le_matrixHeight state.B target 0
        · simp

theorem arithmeticEvents_operandHeight_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    (arithmeticEvents A).Forall
      (fun event => event.operandHeight ≤ matrixHeight A) := by
  let reduced := loop n le_rfl (Transform.refl A)
  rw [arithmeticEvents, List.forall_append]
  constructor
  · exact arithmeticLoop_operandHeight_le n le_rfl (Transform.refl A)
  · rw [List.forall_cons]
    constructor
    · change (reduced.B 0 0).natAbs ≤ matrixHeight A
      simpa [reduced, Transform.refl] using
        loop_pivot_natAbs_le_height n le_rfl (Transform.refl A)
    · simp

theorem arithmeticEventListHeight_le_of_forall
    (events : List PrincipalArithmeticEvent) (height : Nat)
    (allBounded : events.Forall (fun event => event.operandHeight ≤ height)) :
    arithmeticEventListHeight events ≤ height := by
  induction events with
  | nil => simp [arithmeticEventListHeight]
  | cons head tail ih =>
      rw [List.forall_cons] at allBounded
      simp only [arithmeticEventListHeight]
      exact max_le allBounded.1 (ih allBounded.2)

theorem arithmeticEvents_height_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    arithmeticEventListHeight (arithmeticEvents A) ≤ matrixHeight A :=
  arithmeticEventListHeight_le_of_forall _ _
    (arithmeticEvents_operandHeight_le A)

end BoundedColumn

open BoundedColumn

/-- Closed Step-4 bound for every transformed-matrix coefficient. -/
@[expose] public def boundedColumnIntermediatePolynomialBitLengthBound
    (dimension inputBits : Nat) : Nat :=
  match dimension with
  | 0 => inputBits + 1
  | order + 1 =>
      inputBits + order *
        (Nat.size (order + 1) + 2 * (inputBits + 1) + 6) + 1

/-- Closed Step-4 bound for every accumulated forward multiplier. -/
@[expose] public def boundedColumnMultiplierPolynomialBitLengthBound
    (dimension inputBits : Nat) : Nat :=
  match dimension with
  | 0 => 0
  | order + 1 =>
      Nat.size (order + 1) +
        boundedColumnIntermediatePolynomialBitLengthBound
          (order + 1) inputBits +
        determinantBitLengthBound order inputBits

/-- Closed Step-4 bound for every directly accumulated inverse. -/
@[expose] public def boundedColumnInversePolynomialBitLengthBound
    (dimension inputBits : Nat) : Nat :=
  match dimension with
  | 0 => 0
  | order + 1 =>
      Nat.size (order + 1) + inputBits +
        determinantBitLengthBound order
          (boundedColumnIntermediatePolynomialBitLengthBound
            (order + 1) inputBits)

/-- Maximum transformed-matrix coefficient length observed by Step 4. -/
@[expose] public def boundedColumnIntermediateMatrixBitLength
    {n : Nat} (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  (boundedColumnTrace A).intermediateMatrixBitLength A

/-- Maximum forward-prefix coefficient length observed by Step 4. -/
@[expose] public def boundedColumnIntermediateMultiplierBitLength
    {n : Nat} (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  (boundedColumnTrace A).intermediateMultiplierBitLength

/-- Maximum inverse-prefix coefficient length observed by Step 4. -/
@[expose] public def boundedColumnIntermediateInverseBitLength
    {n : Nat} (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  (boundedColumnTrace A).intermediateInverseMultiplierBitLength

/-- Maximum bit length of every XGCD and normalization operand in Step 4. -/
@[expose] public def boundedColumnArithmeticOperandBitLength
    {n : Nat} (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Nat :=
  Nat.size <| arithmeticEventListHeight (boundedColumnArithmeticEvents A)

public theorem boundedColumnIntermediateMatrixBitLength_le_polynomial
    {n : Nat} (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    boundedColumnIntermediateMatrixBitLength A ≤
      boundedColumnIntermediatePolynomialBitLengthBound
        (n + 1) (matrixBitLength A) := by
  simpa [boundedColumnIntermediateMatrixBitLength, boundedColumnTrace,
    boundedColumnIntermediatePolynomialBitLengthBound,
    intermediatePolynomialBits, stepFactorPolynomialBits] using
    compute_intermediateBitLength_le_polynomial A

public theorem boundedColumnIntermediateMultiplierBitLength_le_polynomial
    {n : Nat} (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    boundedColumnIntermediateMultiplierBitLength A ≤
      boundedColumnMultiplierPolynomialBitLengthBound
        (n + 1) (matrixBitLength A) := by
  simpa [boundedColumnIntermediateMultiplierBitLength, boundedColumnTrace,
    boundedColumnMultiplierPolynomialBitLengthBound,
    boundedColumnIntermediatePolynomialBitLengthBound,
    multiplierPolynomialBits, intermediatePolynomialBits,
    stepFactorPolynomialBits] using
    compute_intermediateMultiplierBitLength_le_polynomial A hdet

public theorem boundedColumnIntermediateInverseBitLength_le_polynomial
    {n : Nat} (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0) :
    boundedColumnIntermediateInverseBitLength A ≤
      boundedColumnInversePolynomialBitLengthBound
        (n + 1) (matrixBitLength A) := by
  simpa [boundedColumnIntermediateInverseBitLength, boundedColumnTrace,
    boundedColumnInversePolynomialBitLengthBound,
    boundedColumnIntermediatePolynomialBitLengthBound,
    inversePolynomialBits, intermediatePolynomialBits,
    stepFactorPolynomialBits] using
    compute_intermediateInverseBitLength_le_polynomial A hdet

public theorem boundedColumnArithmeticOperandBitLength_le_input
    {n : Nat} (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    boundedColumnArithmeticOperandBitLength A ≤ matrixBitLength A := by
  unfold boundedColumnArithmeticOperandBitLength matrixBitLength
  exact Nat.size_le_size <| by
    simpa [boundedColumnArithmeticEvents] using arithmeticEvents_height_le A

end NormalForms.Research.KannanBachem.Smith
