import NormalForms.Matrix.Hermite.Transform

/-!
# Hermite Bezout Infrastructure

Block-lift and top-row Bezout gadgets used by Hermite and Smith normalization.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates

def diagLiftMatrix {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) :
    _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun i j =>
    Fin.cases
      (Fin.cases (1 : R) (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => U i' j') j)
      i


@[simp] theorem diagLiftMatrix_zero_zero {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) :
    diagLiftMatrix U 0 0 = 1 := by
  simp [diagLiftMatrix]


@[simp] theorem diagLiftMatrix_zero_succ {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) (j : Fin m) :
    diagLiftMatrix U 0 j.succ = 0 := by
  simp [diagLiftMatrix]


@[simp] theorem diagLiftMatrix_succ_zero {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) (i : Fin m) :
    diagLiftMatrix U i.succ 0 = 0 := by
  simp [diagLiftMatrix]


@[simp] theorem diagLiftMatrix_succ_succ {m : Nat} {R : Type _} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    diagLiftMatrix U i.succ j.succ = U i j := by
  simp [diagLiftMatrix]


@[simp] theorem diagLiftMatrix_one {m : Nat} {R : Type _} [CommRing R] :
    diagLiftMatrix (1 : _root_.Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simp [diagLiftMatrix, _root_.Matrix.one_apply]
      | succ j =>
          have h : (0 : Fin (m + 1)) ≠ j.succ := by
            intro hEq
            exact Fin.succ_ne_zero j hEq.symm
          simp [diagLiftMatrix, _root_.Matrix.one_apply, h]
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have h : (i.succ : Fin (m + 1)) ≠ 0 := by simp
          simp [diagLiftMatrix, _root_.Matrix.one_apply, h]
      | succ j =>
          simp [diagLiftMatrix, _root_.Matrix.one_apply]


@[simp] theorem diagLiftMatrix_mul {m : Nat} {R : Type _}
    [CommRing R]
    (U V : _root_.Matrix (Fin m) (Fin m) R) :
    diagLiftMatrix U * diagLiftMatrix V = diagLiftMatrix (U * V) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases <;>
        simp [diagLiftMatrix, _root_.Matrix.mul_apply, Fin.sum_univ_succ]
  | succ i =>
      cases j using Fin.cases <;>
        simp [diagLiftMatrix, _root_.Matrix.mul_apply, Fin.sum_univ_succ]


theorem unimodular_diagLiftMatrix {m : Nat} {R : Type _} [CommRing R]
    {U : _root_.Matrix (Fin m) (Fin m) R} (hU : Unimodular U) :
    Unimodular (diagLiftMatrix U) := by
  have hmul : diagLiftMatrix U * diagLiftMatrix U⁻¹ = 1 := by
    calc
      diagLiftMatrix U * diagLiftMatrix U⁻¹ = diagLiftMatrix (U * U⁻¹) := by
        rw [diagLiftMatrix_mul]
      _ = diagLiftMatrix (1 : _root_.Matrix (Fin m) (Fin m) R) := by
        rw [_root_.Matrix.mul_nonsing_inv _ hU]
      _ = 1 := diagLiftMatrix_one
  have hmul' : diagLiftMatrix U⁻¹ * diagLiftMatrix U = 1 := by
    calc
      diagLiftMatrix U⁻¹ * diagLiftMatrix U = diagLiftMatrix (U⁻¹ * U) := by
        rw [diagLiftMatrix_mul]
      _ = diagLiftMatrix (1 : _root_.Matrix (Fin m) (Fin m) R) := by
        rw [_root_.Matrix.nonsing_inv_mul _ hU]
      _ = 1 := diagLiftMatrix_one
  have hUnit : IsUnit (diagLiftMatrix U) := by
    exact ⟨⟨diagLiftMatrix U, diagLiftMatrix U⁻¹, hmul, hmul'⟩, rfl⟩
  exact (_root_.Matrix.isUnit_iff_isUnit_det (A := diagLiftMatrix U)).1 hUnit


@[simp] theorem diagLiftMatrix_mul_topRow {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (A : _root_.Matrix (Fin (m + 1)) (Fin n) R) :
    (diagLiftMatrix U * A) 0 = A 0 := by
  ext j
  simp [diagLiftMatrix, _root_.Matrix.mul_apply, Fin.sum_univ_succ]


@[simp] theorem lowerRight_diagLiftMatrix_mul {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) :
    lowerRight (diagLiftMatrix U * A) = U * lowerRight A := by
  ext i j
  simp [diagLiftMatrix, lowerRight, _root_.Matrix.mul_apply, Fin.sum_univ_succ]


private def topLiftMatrix {m : Nat} {R : Type _} [Zero R]
    (B : _root_.Matrix (Fin 2) (Fin 2) R)
    (U : _root_.Matrix (Fin m) (Fin m) R) :
    _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  fun i j =>
    Fin.cases
      (Fin.cases (B 0 0)
        (fun j' => Fin.cases (B 0 1) (fun _ => 0) j')
        j)
      (fun i' =>
        Fin.cases
          (Fin.cases (B 1 0)
            (fun j' => Fin.cases (B 1 1) (fun _ => 0) j')
            j)
          (fun i'' =>
            Fin.cases 0
              (fun j' => Fin.cases 0 (fun j'' => U i'' j'') j')
              j)
          i')
      i


def topBezoutMatrix {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) : _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  topLiftMatrix (bezoutReductionMatrix a b) 1


private noncomputable def topBezoutMatrixInv {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    R -> R -> _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  fun a b => topLiftMatrix (bezoutReductionMatrix a b)⁻¹ 1


@[simp] theorem topBezoutMatrix_zero_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 0 0 = bezoutReductionMatrix a b 0 0 := by
  rfl


@[simp] theorem topBezoutMatrix_zero_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 0 1 = bezoutReductionMatrix a b 0 1 := by
  rfl


@[simp] theorem topBezoutMatrix_one_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 1 0 = bezoutReductionMatrix a b 1 0 := by
  rfl


@[simp] theorem topBezoutMatrix_one_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 1 1 = bezoutReductionMatrix a b 1 1 := by
  rfl


@[simp] theorem topBezoutMatrix_zero_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    topBezoutMatrix (m := m) a b 0 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_one_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    topBezoutMatrix (m := m) a b 1 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ 0 = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ 1 = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i j : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 0 0 = (bezoutReductionMatrix a b)⁻¹ 0 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 0 1 = (bezoutReductionMatrix a b)⁻¹ 0 1 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 1 0 = (bezoutReductionMatrix a b)⁻¹ 1 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 1 1 = (bezoutReductionMatrix a b)⁻¹ 1 1 := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    topBezoutMatrixInv (m := m) a b 0 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    topBezoutMatrixInv (m := m) a b 1 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ 0 = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ 1 = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i j : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
  rfl


private theorem topBezoutMatrix_mul_inv_topBlock {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M 0 0 = 1 ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = 1 := by
  have hBezout : Unimodular (bezoutReductionMatrix a b) := by
    simp [Unimodular, det_bezoutReductionMatrix]
  have hMulTop : bezoutReductionMatrix a b * (bezoutReductionMatrix a b)⁻¹ = 1 := by
    exact _root_.Matrix.mul_nonsing_inv _ hBezout
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [_root_.Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hMulTop 0) 0
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [_root_.Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hMulTop 0) 1
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [_root_.Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hMulTop 1) 0
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simpa [_root_.Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hMulTop 1) 1


private theorem topBezoutMatrix_mul_inv_offDiag {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (j : Fin m) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M 0 j.succ.succ = 0 ∧ M 1 j.succ.succ = 0 ∧
      M j.succ.succ 0 = 0 ∧ M j.succ.succ 1 = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [_root_.Matrix.one_apply]


private theorem topBezoutMatrix_mul_inv_unitBlock {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) (i j : Fin m) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R) i.succ.succ j.succ.succ := by
  have hTail :
      ((1 : _root_.Matrix (Fin m) (Fin m) R) * (1 : _root_.Matrix (Fin m) (Fin m) R)) i j =
        (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
    simp
  dsimp
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [_root_.Matrix.one_apply]


theorem topBezoutMatrix_mul_inv {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) :
    topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b = 1 := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          exact (topBezoutMatrix_mul_inv_topBlock (m := m) a b).1
      | succ j =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrix_mul_inv_topBlock (m := m) a b).2.1
          | succ j =>
              exact (topBezoutMatrix_mul_inv_offDiag (m := m) a b j).1
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrix_mul_inv_topBlock (m := m) a b).2.2.1
          | succ j =>
              cases j using Fin.cases with
              | zero =>
                  exact (topBezoutMatrix_mul_inv_topBlock (m := m) a b).2.2.2
              | succ j =>
                  exact (topBezoutMatrix_mul_inv_offDiag (m := m) a b j).2.1
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrix_mul_inv_offDiag (m := m) a b i).2.2.1
          | succ j =>
              cases j using Fin.cases with
              | zero =>
                  exact (topBezoutMatrix_mul_inv_offDiag (m := m) a b i).2.2.2
              | succ j =>
                  exact topBezoutMatrix_mul_inv_unitBlock (m := m) a b i j


theorem unimodular_topBezoutMatrix {m : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    (a b : R) : Unimodular (topBezoutMatrix (m := m) a b) := by
  simpa [Unimodular] using
    (_root_.Matrix.isUnit_det_of_right_inverse
      (A := topBezoutMatrix (m := m) a b)
      (B := topBezoutMatrixInv (m := m) a b)
      (topBezoutMatrix_mul_inv (m := m) a b))


theorem topBezoutMatrix_mul_apply_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) 0 j =
      bezoutReductionMatrix a b 0 0 * A 0 j +
        bezoutReductionMatrix a b 0 1 * A 1 j := by
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [topBezoutMatrix_zero_zero, topBezoutMatrix_zero_one, topBezoutMatrix_zero_succ_succ]


theorem topBezoutMatrix_mul_apply_one {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) 1 j =
      bezoutReductionMatrix a b 1 0 * A 0 j +
        bezoutReductionMatrix a b 1 1 * A 1 j := by
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [topBezoutMatrix_one_zero, topBezoutMatrix_one_one, topBezoutMatrix_one_succ_succ]


theorem topBezoutMatrix_mul_apply_succ_succ {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin m) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) i.succ.succ j = A i.succ.succ j := by
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [topBezoutMatrix_succ_succ_zero, topBezoutMatrix_succ_succ_one,
    topBezoutMatrix_succ_succ_succ_succ, _root_.Matrix.one_apply]


theorem Bezout_preserves_zeros {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) (i : Fin m)
    (h : A i.succ.succ 0 = 0) :
    (topBezoutMatrix (m := m) a b * A) i.succ.succ 0 = 0 := by
  rw [topBezoutMatrix_mul_apply_succ_succ (m := m) (n := n + 1) (a := a) (b := b)
    (A := A) i (0 : Fin (n + 1))]
  exact h


theorem topBezoutMatrix_mul_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) :
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 0 0 =
      EuclideanDomain.gcd (A 0 0) (A 1 0) := by
  have hvec := bezoutReductionMatrix_mulVec (A 0 0) (A 1 0)
  calc
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 0 0
        = bezoutReductionMatrix (A 0 0) (A 1 0) 0 0 * A 0 0 +
            bezoutReductionMatrix (A 0 0) (A 1 0) 0 1 * A 1 0 :=
          topBezoutMatrix_mul_apply_zero (m := m) (n := n + 1) (A 0 0) (A 1 0) A
            (0 : Fin (n + 1))
    _ = EuclideanDomain.gcd (A 0 0) (A 1 0) := by
          simpa [_root_.Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hvec 0


theorem topBezoutMatrix_mul_rowOneFirstCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) :
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 1 0 = 0 := by
  have hvec := bezoutReductionMatrix_mulVec (A 0 0) (A 1 0)
  calc
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 1 0
        = bezoutReductionMatrix (A 0 0) (A 1 0) 1 0 * A 0 0 +
            bezoutReductionMatrix (A 0 0) (A 1 0) 1 1 * A 1 0 :=
          topBezoutMatrix_mul_apply_one (m := m) (n := n + 1) (A 0 0) (A 1 0) A
            (0 : Fin (n + 1))
    _ = 0 := by
          simpa [_root_.Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hvec 1


def LeftTransform.diagLift {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (U : _root_.Matrix (Fin m) (Fin m) R) (hU : Unimodular U) :
    LeftTransform A :=
  { U := diagLiftMatrix U
    B := diagLiftMatrix U * A
    left_mul := by rfl
    unimodular := unimodular_diagLiftMatrix hU }


def LeftTransform.topBezout {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) : LeftTransform A :=
  { U := topBezoutMatrix (m := m) (A 0 0) (A 1 0)
    B := topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A
    left_mul := by rfl
    unimodular := unimodular_topBezoutMatrix (m := m) (A 0 0) (A 1 0) }


end NormalForms.Matrix.Hermite
