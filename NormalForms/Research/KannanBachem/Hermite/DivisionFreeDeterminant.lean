/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.CoefficientSize
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird
import all Mathlib.Data.Vector.Basic

/-!
# Cached Division-Free Determinant Recurrence

Mathlib exposes Bird's division-free scalar recurrence.  Its recursive
definition is convenient for kernel normalization, but independently
recomputes earlier entries when used as an executable program.  This module
materializes every recurrence matrix as nested `Vector`s, so one iteration
reads the preceding matrix instead of rebuilding its recursion tree.

The first layer below is deliberately algebraic: it proves that the cached
program agrees entrywise with the corresponding matrix recurrence.  The
separate correctness layer identifies the final scalar with `Matrix.det`; the
separate cost layer charges the exact sign-magnitude operations.  Keeping
those obligations apart prevents an implementation-cost claim from being
smuggled through the mathematical definition of determinant.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix BigOperators

namespace DivisionFreeDeterminant

/-- A square matrix stored as two materialized, fixed-length arrays. -/
public abbrev DenseMatrix (n : Nat) (R : Type*) := Vector (Vector R n) n

namespace DenseMatrix

private theorem vector_get_ofFn {n : Nat} {α : Type*}
    (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Vector.ofFn]

private theorem vector_ofFn_get {n : Nat} {α : Type*}
    (v : Vector α n) : Vector.ofFn v.get = v := by
  apply Vector.ext
  intro i hi
  change (Vector.ofFn v.get).get ⟨i, hi⟩ = v.get ⟨i, hi⟩
  exact vector_get_ofFn v.get ⟨i, hi⟩

/-- Materialize a functional matrix in row-major nested vectors. -/
@[expose] public def ofMatrix {n : Nat} {R : Type*}
    (A : _root_.Matrix (Fin n) (Fin n) R) : DenseMatrix n R :=
  Vector.ofFn fun i => Vector.ofFn fun j => A i j

/-- Read a dense matrix through the ordinary functional matrix interface. -/
@[expose] public def toMatrix {n : Nat} {R : Type*}
    (A : DenseMatrix n R) : _root_.Matrix (Fin n) (Fin n) R :=
  fun i j => (A.get i).get j

@[simp] public theorem toMatrix_ofMatrix {n : Nat} {R : Type*}
    (A : _root_.Matrix (Fin n) (Fin n) R) :
    toMatrix (ofMatrix A) = A := by
  ext i j
  rw [toMatrix, ofMatrix, vector_get_ofFn, vector_get_ofFn]

@[simp] public theorem ofMatrix_toMatrix {n : Nat} {R : Type*}
    (A : DenseMatrix n R) :
    ofMatrix (toMatrix A) = A := by
  unfold ofMatrix toMatrix
  rw [← vector_ofFn_get A]
  congr 1
  funext i
  rw [vector_get_ofFn]
  exact vector_ofFn_get (A.get i)

@[simp] public theorem get_ofMatrix {n : Nat} {R : Type*}
    (A : _root_.Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ((ofMatrix A).get i).get j = A i j := by
  rw [ofMatrix, vector_get_ofFn, vector_get_ofFn]

end DenseMatrix

variable {R : Type*} [CommRing R]

/-- Increasing list of column indices strictly below/right of `i`. -/
@[expose] public def upperIndices {n : Nat} (i : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun k => i < k

/-- One scalar entry of Bird's matrix recurrence. -/
@[expose] public def entry {n : Nat}
    (input current : _root_.Matrix (Fin n) (Fin n) R)
    (i j : Fin n) : R :=
  -((upperIndices i).map fun k => current k k).sum * input i j +
    ((upperIndices i).map fun k => current i k * input k j).sum

/-- One mathematical matrix step of the division-free recurrence. -/
@[expose] public def matrixStep {n : Nat}
    (input current : _root_.Matrix (Fin n) (Fin n) R) :
    _root_.Matrix (Fin n) (Fin n) R :=
  fun i j => entry input current i j

/-- One cached step; `Vector.ofFn` materializes every output entry once. -/
@[expose] public def denseStep {n : Nat}
    (input current : DenseMatrix n R) : DenseMatrix n R :=
  DenseMatrix.ofMatrix
    (matrixStep input.toMatrix current.toMatrix)

@[simp] public theorem DenseMatrix.toMatrix_denseStep {n : Nat}
    (input current : DenseMatrix n R) :
    (denseStep input current).toMatrix =
      matrixStep input.toMatrix current.toMatrix := by
  simp [denseStep]

/-- Iterate the mathematical recurrence, starting with the input matrix. -/
@[expose] public def matrixIterate {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) R) : Nat →
      _root_.Matrix (Fin n) (Fin n) R
  | 0 => input
  | steps + 1 => matrixStep input (matrixIterate input steps)

/-- Iterate the cached recurrence, retaining only the preceding dense matrix. -/
@[expose] public def denseIterate {n : Nat}
    (input : DenseMatrix n R) : Nat → DenseMatrix n R
  | 0 => input
  | steps + 1 => denseStep input (denseIterate input steps)

/-- Every materialized stage agrees entrywise with the mathematical stage. -/
@[simp] public theorem DenseMatrix.toMatrix_denseIterate {n : Nat}
    (input : DenseMatrix n R) (steps : Nat) :
    (denseIterate input steps).toMatrix =
      matrixIterate input.toMatrix steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [denseIterate, matrixIterate,
        DenseMatrix.toMatrix_denseStep, ih]

/-- Bird's final scalar, stated over the mathematical matrix recurrence. -/
@[expose] public def matrixBirdDet {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k * matrixIterate input k 0 0

/-- Executable Bird scalar with every intermediate matrix cached in vectors. -/
@[expose] public def cachedBirdDet {n : Nat}
    (input : DenseMatrix n R) : R :=
  match n with
  | 0 => 1
  | k + 1 => (-1 : R) ^ k *
      (((denseIterate input k).get 0).get 0)

/-- The cached program returns exactly the mathematical recurrence scalar. -/
public theorem cachedBirdDet_eq_matrixBirdDet {n : Nat}
    (input : DenseMatrix n R) :
    cachedBirdDet input = matrixBirdDet input.toMatrix := by
  cases n with
  | zero => rfl
  | succ k =>
      simp only [cachedBirdDet, matrixBirdDet]
      rw [← DenseMatrix.toMatrix_denseIterate]
      rfl

/-- Matrix-facing executable entrypoint. -/
@[expose] public def evaluate {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) R) : R :=
  cachedBirdDet (DenseMatrix.ofMatrix input)

public theorem evaluate_eq_matrixBirdDet {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) R) :
    evaluate input = matrixBirdDet input := by
  rw [evaluate, cachedBirdDet_eq_matrixBirdDet]
  simp

/-! ## Integer coefficient bounds -/

@[simp] public theorem upperIndices_length_le {n : Nat} (i : Fin n) :
    (upperIndices i).length ≤ n := by
  exact (List.length_filter_le _ _).trans (by simp)

/-- Absolute value of a list sum is at most the sum of absolute values. -/
public theorem list_sum_natAbs_le (values : List Int) :
    values.sum.natAbs ≤ (values.map Int.natAbs).sum := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (Int.natAbs_add_le head tail.sum).trans
        (Nat.add_le_add_left ih head.natAbs)

/-- Uniform height bound for an integer list sum. -/
public theorem list_sum_natAbs_le_length_mul
    (values : List Int) (height : Nat)
    (bounded : ∀ value ∈ values, value.natAbs ≤ height) :
    values.sum.natAbs ≤ values.length * height := by
  calc
    values.sum.natAbs ≤ (values.map Int.natAbs).sum :=
      list_sum_natAbs_le values
    _ ≤ (values.map fun _ => height).sum := by
      exact List.sum_le_sum bounded
    _ = values.length * height := by simp

/-- One Bird matrix step grows height by at most the two tail sums. -/
public theorem matrixStep_height_le {n : Nat}
    (input current : _root_.Matrix (Fin n) (Fin n) Int) :
    matrixHeight (matrixStep input current) ≤
      2 * n * (matrixHeight current * matrixHeight input) := by
  apply matrixHeight_le
  intro i j
  let indices := upperIndices i
  let diagonal := (indices.map fun k => current k k).sum
  let trailing :=
    (indices.map fun k => current i k * input k j).sum
  have indicesLength : indices.length ≤ n := by
    exact upperIndices_length_le i
  have diagonalHeight :
      diagonal.natAbs ≤ n * matrixHeight current := by
    calc
      diagonal.natAbs ≤ indices.length * matrixHeight current := by
        have bound := list_sum_natAbs_le_length_mul
          (indices.map fun k => current k k) (matrixHeight current)
          (by
            intro value member
            rw [List.mem_map] at member
            obtain ⟨k, _member, rfl⟩ := member
            exact entry_natAbs_le_matrixHeight current k k)
        simpa only [diagonal, List.length_map] using bound
      _ ≤ n * matrixHeight current :=
        Nat.mul_le_mul_right _ indicesLength
  have trailingHeight :
      trailing.natAbs ≤
        n * (matrixHeight current * matrixHeight input) := by
    calc
      trailing.natAbs ≤
          indices.length *
            (matrixHeight current * matrixHeight input) := by
        have bound := list_sum_natAbs_le_length_mul
          (indices.map fun k => current i k * input k j)
          (matrixHeight current * matrixHeight input)
          (by
            intro value member
            rw [List.mem_map] at member
            obtain ⟨k, _member, rfl⟩ := member
            rw [Int.natAbs_mul]
            exact Nat.mul_le_mul
              (entry_natAbs_le_matrixHeight current i k)
              (entry_natAbs_le_matrixHeight input k j))
        simpa only [trailing, List.length_map] using bound
      _ ≤ n * (matrixHeight current * matrixHeight input) :=
        Nat.mul_le_mul_right _ indicesLength
  change
    (-diagonal * input i j + trailing).natAbs ≤
      2 * n * (matrixHeight current * matrixHeight input)
  calc
    (-diagonal * input i j + trailing).natAbs ≤
        (-diagonal * input i j).natAbs + trailing.natAbs :=
      Int.natAbs_add_le _ _
    _ = diagonal.natAbs * (input i j).natAbs + trailing.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_neg]
    _ ≤ (n * matrixHeight current) * matrixHeight input +
          n * (matrixHeight current * matrixHeight input) :=
      Nat.add_le_add
        (Nat.mul_le_mul diagonalHeight
          (entry_natAbs_le_matrixHeight input i j))
        trailingHeight
    _ = 2 * n * (matrixHeight current * matrixHeight input) := by ring

/-- Closed height envelope for a cached recurrence stage. -/
@[expose] public def iterationHeightBound
    (dimension inputHeight steps : Nat) : Nat :=
  (2 * dimension * inputHeight) ^ steps * inputHeight

public theorem matrixIterate_height_le {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) Int) (steps : Nat) :
    matrixHeight (matrixIterate input steps) ≤
      iterationHeightBound n (matrixHeight input) steps := by
  induction steps with
  | zero => simp [matrixIterate, iterationHeightBound]
  | succ steps ih =>
      rw [matrixIterate]
      calc
        matrixHeight (matrixStep input (matrixIterate input steps)) ≤
            2 * n *
              (matrixHeight (matrixIterate input steps) *
                matrixHeight input) :=
          matrixStep_height_le input (matrixIterate input steps)
        _ ≤ 2 * n *
              (iterationHeightBound n (matrixHeight input) steps *
                matrixHeight input) := by
          gcongr
        _ = iterationHeightBound n (matrixHeight input) (steps + 1) := by
          simp only [iterationHeightBound, pow_succ]
          ring

private theorem natSize_mul_le (left right : Nat) :
    Nat.size (left * right) ≤ Nat.size left + Nat.size right := by
  rw [Nat.size_le, pow_add]
  exact mul_lt_mul''
    (Nat.lt_size_self left)
    (Nat.lt_size_self right)
    (Nat.zero_le _)
    (Nat.zero_le _)

private theorem natSize_pow_le (base exponent : Nat) :
    Nat.size (base ^ exponent) ≤ exponent * Nat.size base + 1 := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      rw [pow_succ]
      calc
        Nat.size (base ^ exponent * base) ≤
            Nat.size (base ^ exponent) + Nat.size base :=
          natSize_mul_le _ _
        _ ≤ (exponent * Nat.size base + 1) + Nat.size base :=
          Nat.add_le_add_right ih _
        _ = (exponent + 1) * Nat.size base + 1 := by ring

/-- Polynomial bit-length envelope for every cached recurrence stage. -/
@[expose] public def iterationBitLengthBound
    (dimension inputBits steps : Nat) : Nat :=
  steps * (Nat.size dimension + inputBits + 3) + inputBits + 2

public theorem matrixIterate_bitLength_le {n : Nat}
    (input : _root_.Matrix (Fin n) (Fin n) Int) (steps : Nat) :
    matrixBitLength (matrixIterate input steps) ≤
      iterationBitLengthBound n (matrixBitLength input) steps := by
  let height := matrixHeight input
  let factor := 2 * n * height
  have heightBound := matrixIterate_height_le input steps
  unfold matrixBitLength at heightBound ⊢
  calc
    Nat.size (matrixHeight (matrixIterate input steps)) ≤
        Nat.size (factor ^ steps * height) := by
      exact Nat.size_le_size heightBound
    _ ≤ Nat.size (factor ^ steps) + Nat.size height :=
      natSize_mul_le _ _
    _ ≤ (steps * Nat.size factor + 1) + Nat.size height :=
      Nat.add_le_add_right (natSize_pow_le factor steps) _
    _ ≤ steps * (Nat.size n + Nat.size height + 3) +
          Nat.size height + 2 := by
      have factorSize :
          Nat.size factor ≤ Nat.size n + Nat.size height + 3 := by
        simp only [factor]
        calc
          Nat.size (2 * n * height) ≤
              Nat.size (2 * n) + Nat.size height :=
            natSize_mul_le _ _
          _ ≤ (Nat.size 2 + Nat.size n) + Nat.size height :=
            Nat.add_le_add_right (natSize_mul_le 2 n) _
          _ ≤ Nat.size n + Nat.size height + 3 := by
            have twoSize : Nat.size 2 = 2 := rfl
            rw [twoSize]
            omega
      have scaled := Nat.mul_le_mul_left steps factorSize
      omega
    _ = iterationBitLengthBound n (Nat.size height) steps := by
      simp [iterationBitLengthBound]

end DivisionFreeDeterminant

end NormalForms.Research.KannanBachem.Hermite
