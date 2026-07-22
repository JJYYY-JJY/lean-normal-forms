/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Matrix.Hermite.Transform
import all NormalForms.Matrix.Constructive

/-!
# Hermite Bezout Infrastructure

Block-lift and top-row Bezout gadgets used by Hermite and Smith normalization.
-/

set_option linter.privateModule false

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
        simp [diagLiftMatrix, _root_.Matrix.mul_apply,
          NormalForms.Matrix.Constructive.sum_univ_succ]
  | succ i =>
      cases j using Fin.cases <;>
        simp [diagLiftMatrix, _root_.Matrix.mul_apply,
          NormalForms.Matrix.Constructive.sum_univ_succ]


def diagLiftInverseCertificate {m : Nat} {R : Type _} [CommRing R]
    {U : _root_.Matrix (Fin m) (Fin m) R} (U_cert : MatrixInverseCertificate U) :
    MatrixInverseCertificate (diagLiftMatrix U) :=
  { inverse := diagLiftMatrix U_cert.inverse
    left_inv := by
      rw [diagLiftMatrix_mul, U_cert.left_inv, diagLiftMatrix_one]
    right_inv := by
      rw [diagLiftMatrix_mul, U_cert.right_inv, diagLiftMatrix_one] }


theorem unimodular_diagLiftMatrix {m : Nat} {R : Type _} [CommRing R]
    {U : _root_.Matrix (Fin m) (Fin m) R} (U_cert : MatrixInverseCertificate U) :
    Unimodular (diagLiftMatrix U) :=
  (diagLiftInverseCertificate U_cert).unimodular


@[simp] theorem diagLiftMatrix_mul_topRow {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (A : _root_.Matrix (Fin (m + 1)) (Fin n) R) :
    (diagLiftMatrix U * A) 0 = A 0 := by
  ext j
  simp [diagLiftMatrix, _root_.Matrix.mul_apply,
    NormalForms.Matrix.Constructive.sum_univ_succ]


@[simp] theorem lowerRight_diagLiftMatrix_mul {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (U : _root_.Matrix (Fin m) (Fin m) R)
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) :
    lowerRight (diagLiftMatrix U * A) = U * lowerRight A := by
  ext i j
  simp [diagLiftMatrix, lowerRight, _root_.Matrix.mul_apply,
    NormalForms.Matrix.Constructive.sum_univ_succ]


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
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) : _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  topLiftMatrix (bezoutReductionMatrix a b) 1


private def topBezoutMatrixInv {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] :
    R -> R -> _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R :=
  fun a b => topLiftMatrix (bezoutReductionInverseMatrix a b) 1


@[simp] theorem topBezoutMatrix_zero_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 0 0 = bezoutReductionMatrix a b 0 0 := by
  rfl


@[simp] theorem topBezoutMatrix_zero_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 0 1 = bezoutReductionMatrix a b 0 1 := by
  rfl


@[simp] theorem topBezoutMatrix_one_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 1 0 = bezoutReductionMatrix a b 1 0 := by
  rfl


@[simp] theorem topBezoutMatrix_one_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrix (m := m) a b 1 1 = bezoutReductionMatrix a b 1 1 := by
  rfl


@[simp] theorem topBezoutMatrix_zero_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (j : Fin m) :
    topBezoutMatrix (m := m) a b 0 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_one_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (j : Fin m) :
    topBezoutMatrix (m := m) a b 1 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (i : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ 0 = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (i : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ 1 = 0 := by
  rfl


@[simp] theorem topBezoutMatrix_succ_succ_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (i j : Fin m) :
    topBezoutMatrix (m := m) a b i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 0 0 = bezoutReductionInverseMatrix a b 0 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 0 1 = bezoutReductionInverseMatrix a b 0 1 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 1 0 = bezoutReductionInverseMatrix a b 1 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b 1 1 = bezoutReductionInverseMatrix a b 1 1 := by
  rfl


@[simp] theorem topBezoutMatrixInv_zero_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (j : Fin m) :
    topBezoutMatrixInv (m := m) a b 0 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_one_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (j : Fin m) :
    topBezoutMatrixInv (m := m) a b 1 j.succ.succ = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_zero {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (i : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ 0 = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_one {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (i : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ 1 = 0 := by
  rfl


@[simp] theorem topBezoutMatrixInv_succ_succ_succ_succ {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (i j : Fin m) :
    topBezoutMatrixInv (m := m) a b i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
  rfl


private theorem topBezoutMatrix_mul_inv_topBlock {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M 0 0 = 1 ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = 1 := by
  have hMulTop :
      bezoutReductionMatrix a b * bezoutReductionInverseMatrix a b = 1 :=
    bezoutReductionMatrix_mul_inverse a b
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    have hEntry := congrFun (congrFun hMulTop 0) 0
    rw [_root_.Matrix.mul_apply,
      NormalForms.Matrix.Constructive.sum_univ_two] at hEntry
    simpa using hEntry
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    have hEntry := congrFun (congrFun hMulTop 0) 1
    rw [_root_.Matrix.mul_apply,
      NormalForms.Matrix.Constructive.sum_univ_two] at hEntry
    simpa using hEntry
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    have hEntry := congrFun (congrFun hMulTop 1) 0
    rw [_root_.Matrix.mul_apply,
      NormalForms.Matrix.Constructive.sum_univ_two] at hEntry
    simpa using hEntry
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    have hEntry := congrFun (congrFun hMulTop 1) 1
    rw [_root_.Matrix.mul_apply,
      NormalForms.Matrix.Constructive.sum_univ_two] at hEntry
    simpa using hEntry


private theorem topBezoutMatrix_mul_inv_offDiag {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (j : Fin m) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M 0 j.succ.succ = 0 ∧ M 1 j.succ.succ = 0 ∧
      M j.succ.succ 0 = 0 ∧ M j.succ.succ 1 = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    simp [_root_.Matrix.one_apply]


private theorem topBezoutMatrix_mul_inv_unitBlock {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (i j : Fin m) :
    let M := topBezoutMatrix (m := m) a b * topBezoutMatrixInv (m := m) a b
    M i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R) i.succ.succ j.succ.succ := by
  have hTail :
      ((1 : _root_.Matrix (Fin m) (Fin m) R) * (1 : _root_.Matrix (Fin m) (Fin m) R)) i j =
        (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
    exact congrFun
      (congrFun
        (NormalForms.Matrix.Constructive.one_mul
          (1 : _root_.Matrix (Fin m) (Fin m) R)) i) j
  dsimp
  rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
    NormalForms.Matrix.Constructive.sum_univ_succ]
  rw [_root_.Matrix.mul_apply] at hTail
  rw [Fin.succ_zero_eq_one]
  simpa only [topBezoutMatrix_succ_succ_zero, topBezoutMatrix_succ_succ_one,
    topBezoutMatrix_succ_succ_succ_succ,
    topBezoutMatrixInv_zero_succ_succ, topBezoutMatrixInv_one_succ_succ,
    topBezoutMatrixInv_succ_succ_succ_succ, zero_mul, mul_zero, zero_add,
    add_zero, hTail, _root_.Matrix.one_apply, Fin.succ_inj]


private theorem topBezoutMatrixInv_mul_topBlock {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    let M := topBezoutMatrixInv (m := m) a b * topBezoutMatrix (m := m) a b
    M 0 0 = 1 ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = 1 := by
  have hMulTop :
      bezoutReductionInverseMatrix a b * bezoutReductionMatrix a b = 1 :=
    bezoutReductionInverseMatrix_mul a b
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    have hEntry := congrFun (congrFun hMulTop 0) 0
    rw [_root_.Matrix.mul_apply,
      NormalForms.Matrix.Constructive.sum_univ_two] at hEntry
    simpa using hEntry
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    have hEntry := congrFun (congrFun hMulTop 0) 1
    rw [_root_.Matrix.mul_apply,
      NormalForms.Matrix.Constructive.sum_univ_two] at hEntry
    simpa using hEntry
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    have hEntry := congrFun (congrFun hMulTop 1) 0
    rw [_root_.Matrix.mul_apply,
      NormalForms.Matrix.Constructive.sum_univ_two] at hEntry
    simpa using hEntry
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    have hEntry := congrFun (congrFun hMulTop 1) 1
    rw [_root_.Matrix.mul_apply,
      NormalForms.Matrix.Constructive.sum_univ_two] at hEntry
    simpa using hEntry


private theorem topBezoutMatrixInv_mul_offDiag {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (j : Fin m) :
    let M := topBezoutMatrixInv (m := m) a b * topBezoutMatrix (m := m) a b
    M 0 j.succ.succ = 0 ∧ M 1 j.succ.succ = 0 ∧
      M j.succ.succ 0 = 0 ∧ M j.succ.succ 1 = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    simp [_root_.Matrix.one_apply]
  · rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
      NormalForms.Matrix.Constructive.sum_univ_succ]
    simp [_root_.Matrix.one_apply]


private theorem topBezoutMatrixInv_mul_unitBlock {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (i j : Fin m) :
    let M := topBezoutMatrixInv (m := m) a b * topBezoutMatrix (m := m) a b
    M i.succ.succ j.succ.succ =
      (1 : _root_.Matrix (Fin (m + 2)) (Fin (m + 2)) R) i.succ.succ j.succ.succ := by
  have hTail :
      ((1 : _root_.Matrix (Fin m) (Fin m) R) * (1 : _root_.Matrix (Fin m) (Fin m) R)) i j =
        (1 : _root_.Matrix (Fin m) (Fin m) R) i j := by
    exact congrFun
      (congrFun
        (NormalForms.Matrix.Constructive.one_mul
          (1 : _root_.Matrix (Fin m) (Fin m) R)) i) j
  dsimp
  rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
    NormalForms.Matrix.Constructive.sum_univ_succ]
  rw [_root_.Matrix.mul_apply] at hTail
  rw [Fin.succ_zero_eq_one]
  simpa only [topBezoutMatrixInv_succ_succ_zero,
    topBezoutMatrixInv_succ_succ_one,
    topBezoutMatrixInv_succ_succ_succ_succ,
    topBezoutMatrix_zero_succ_succ, topBezoutMatrix_one_succ_succ,
    topBezoutMatrix_succ_succ_succ_succ, zero_mul, mul_zero, zero_add,
    add_zero, hTail, _root_.Matrix.one_apply, Fin.succ_inj]


theorem topBezoutMatrix_mul_inv {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
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


theorem topBezoutMatrixInv_mul {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) :
    topBezoutMatrixInv (m := m) a b * topBezoutMatrix (m := m) a b = 1 := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          exact (topBezoutMatrixInv_mul_topBlock (m := m) a b).1
      | succ j =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrixInv_mul_topBlock (m := m) a b).2.1
          | succ j =>
              exact (topBezoutMatrixInv_mul_offDiag (m := m) a b j).1
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrixInv_mul_topBlock (m := m) a b).2.2.1
          | succ j =>
              cases j using Fin.cases with
              | zero =>
                  exact (topBezoutMatrixInv_mul_topBlock (m := m) a b).2.2.2
              | succ j =>
                  exact (topBezoutMatrixInv_mul_offDiag (m := m) a b j).2.1
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exact (topBezoutMatrixInv_mul_offDiag (m := m) a b i).2.2.1
          | succ j =>
              cases j using Fin.cases with
              | zero =>
                  exact (topBezoutMatrixInv_mul_offDiag (m := m) a b i).2.2.2
              | succ j =>
                  exact topBezoutMatrixInv_mul_unitBlock (m := m) a b i j


def topBezoutMatrixInverseCertificate {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R] (a b : R) :
    MatrixInverseCertificate (topBezoutMatrix (m := m) a b) :=
  { inverse := topBezoutMatrixInv (m := m) a b
    left_inv := topBezoutMatrixInv_mul (m := m) a b
    right_inv := topBezoutMatrix_mul_inv (m := m) a b }


/-- Lift a two-by-two row transform to any distinct pair of rows. -/
def twoRowLiftMatrix {ι R : Type _} [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target : ι) (pair : _root_.Matrix (Fin 2) (Fin 2) R) :
    _root_.Matrix ι ι R :=
  let one : _root_.Matrix ι ι R := 1
  (one.updateRow pivot
      (pair 0 0 • one pivot + pair 0 1 • one target)).updateRow target
    (pair 1 0 • one pivot + pair 1 1 • one target)


@[simp] theorem twoRowLiftMatrix_apply_pivot {ι R : Type _}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target : ι) (hne : pivot ≠ target)
    (pair : _root_.Matrix (Fin 2) (Fin 2) R) (column : ι) :
    twoRowLiftMatrix pivot target pair pivot column =
      pair 0 0 * (1 : _root_.Matrix ι ι R) pivot column +
        pair 0 1 * (1 : _root_.Matrix ι ι R) target column := by
  simp [twoRowLiftMatrix, hne, _root_.Matrix.updateRow_apply, smul_eq_mul]


@[simp] theorem twoRowLiftMatrix_apply_target {ι R : Type _}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target : ι) (pair : _root_.Matrix (Fin 2) (Fin 2) R) (column : ι) :
    twoRowLiftMatrix pivot target pair target column =
      pair 1 0 * (1 : _root_.Matrix ι ι R) pivot column +
        pair 1 1 * (1 : _root_.Matrix ι ι R) target column := by
  simp [twoRowLiftMatrix, _root_.Matrix.updateRow_apply, smul_eq_mul]


@[simp] theorem twoRowLiftMatrix_apply_other {ι R : Type _}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target row : ι) (hp : row ≠ pivot) (ht : row ≠ target)
    (pair : _root_.Matrix (Fin 2) (Fin 2) R) (column : ι) :
    twoRowLiftMatrix pivot target pair row column =
      (1 : _root_.Matrix ι ι R) row column := by
  simp [twoRowLiftMatrix, hp, ht, _root_.Matrix.updateRow_apply]


theorem twoRowLiftMatrix_mul_apply_pivot {ι κ R : Type _}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target : ι) (hne : pivot ≠ target)
    (pair : _root_.Matrix (Fin 2) (Fin 2) R)
    (A : _root_.Matrix ι κ R) (column : κ) :
    (twoRowLiftMatrix pivot target pair * A) pivot column =
      pair 0 0 * A pivot column + pair 0 1 * A target column := by
  rw [twoRowLiftMatrix, NormalForms.Matrix.Constructive.updateRow_mul]
  simp only [_root_.Matrix.updateRow_apply, if_neg hne]
  rw [NormalForms.Matrix.Constructive.updateRow_mul]
  simp only [_root_.Matrix.updateRow_apply, if_pos]
  simp [_root_.Matrix.add_vecMul, _root_.Matrix.smul_vecMul,
    NormalForms.Matrix.Elementary.basisRow_vecMul, smul_eq_mul]


theorem twoRowLiftMatrix_mul_apply_target {ι κ R : Type _}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target : ι) (pair : _root_.Matrix (Fin 2) (Fin 2) R)
    (A : _root_.Matrix ι κ R) (column : κ) :
    (twoRowLiftMatrix pivot target pair * A) target column =
      pair 1 0 * A pivot column + pair 1 1 * A target column := by
  rw [twoRowLiftMatrix, NormalForms.Matrix.Constructive.updateRow_mul]
  simp only [_root_.Matrix.updateRow_apply, if_pos]
  simp [_root_.Matrix.add_vecMul, _root_.Matrix.smul_vecMul,
    NormalForms.Matrix.Elementary.basisRow_vecMul, smul_eq_mul]


theorem twoRowLiftMatrix_mul_apply_other {ι κ R : Type _}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target row : ι) (hp : row ≠ pivot) (ht : row ≠ target)
    (pair : _root_.Matrix (Fin 2) (Fin 2) R)
    (A : _root_.Matrix ι κ R) (column : κ) :
    (twoRowLiftMatrix pivot target pair * A) row column = A row column := by
  rw [twoRowLiftMatrix, NormalForms.Matrix.Constructive.updateRow_mul]
  simp only [_root_.Matrix.updateRow_apply, if_neg ht]
  rw [NormalForms.Matrix.Constructive.updateRow_mul]
  simp only [_root_.Matrix.updateRow_apply, if_neg hp]
  exact congrArg (fun matrix => matrix row column)
    (NormalForms.Matrix.Constructive.one_mul A)


@[simp] theorem twoRowLiftMatrix_one {ι R : Type _}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target : ι) (hne : pivot ≠ target) :
    twoRowLiftMatrix pivot target
        (1 : _root_.Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext row column
  by_cases hp : row = pivot
  · subst row
    simp [twoRowLiftMatrix_apply_pivot, hne]
  · by_cases ht : row = target
    · subst row
      simp [twoRowLiftMatrix_apply_target]
    · exact twoRowLiftMatrix_apply_other pivot target row hp ht 1 column


@[simp] theorem twoRowLiftMatrix_mul {ι R : Type _}
    [Fintype ι] [DecidableEq ι] [CommRing R]
    (pivot target : ι) (hne : pivot ≠ target)
    (left right : _root_.Matrix (Fin 2) (Fin 2) R) :
    twoRowLiftMatrix pivot target left * twoRowLiftMatrix pivot target right =
      twoRowLiftMatrix pivot target (left * right) := by
  ext row column
  by_cases hp : row = pivot
  · subst row
    rw [twoRowLiftMatrix_mul_apply_pivot pivot target hne]
    rw [twoRowLiftMatrix_apply_pivot pivot target hne,
      twoRowLiftMatrix_apply_target,
      twoRowLiftMatrix_apply_pivot pivot target hne]
    have h00 : (left * right) 0 0 =
        left 0 0 * right 0 0 + left 0 1 * right 1 0 := by
      rw [_root_.Matrix.mul_apply,
        NormalForms.Matrix.Constructive.sum_univ_two]
    have h01 : (left * right) 0 1 =
        left 0 0 * right 0 1 + left 0 1 * right 1 1 := by
      rw [_root_.Matrix.mul_apply,
        NormalForms.Matrix.Constructive.sum_univ_two]
    rw [h00, h01]
    ring
  · by_cases ht : row = target
    · subst row
      rw [twoRowLiftMatrix_mul_apply_target]
      rw [twoRowLiftMatrix_apply_pivot pivot target hne,
        twoRowLiftMatrix_apply_target, twoRowLiftMatrix_apply_target]
      have h10 : (left * right) 1 0 =
          left 1 0 * right 0 0 + left 1 1 * right 1 0 := by
        rw [_root_.Matrix.mul_apply,
          NormalForms.Matrix.Constructive.sum_univ_two]
      have h11 : (left * right) 1 1 =
          left 1 0 * right 0 1 + left 1 1 * right 1 1 := by
        rw [_root_.Matrix.mul_apply,
          NormalForms.Matrix.Constructive.sum_univ_two]
      rw [h10, h11]
      ring
    · rw [twoRowLiftMatrix_mul_apply_other pivot target row hp ht,
        twoRowLiftMatrix_apply_other pivot target row hp ht,
        twoRowLiftMatrix_apply_other pivot target row hp ht]


/-- Full-size arbitrary-pair Bezout matrix. -/
def pairBezoutMatrix {ι R : Type _}
    [Fintype ι] [DecidableEq ι]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (pivot target : ι) (a b : R) : _root_.Matrix ι ι R :=
  twoRowLiftMatrix pivot target (bezoutReductionMatrix a b)


/-- The arbitrary-pair Bezout lift carries an explicit inverse. -/
def pairBezoutMatrixInverseCertificate {ι R : Type _}
    [Fintype ι] [DecidableEq ι]
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (pivot target : ι) (hne : pivot ≠ target) (a b : R) :
    MatrixInverseCertificate (pairBezoutMatrix pivot target a b) :=
  { inverse := twoRowLiftMatrix pivot target (bezoutReductionInverseMatrix a b)
    left_inv := by
      rw [pairBezoutMatrix, twoRowLiftMatrix_mul pivot target hne,
        bezoutReductionInverseMatrix_mul, twoRowLiftMatrix_one pivot target hne]
    right_inv := by
      rw [pairBezoutMatrix, twoRowLiftMatrix_mul pivot target hne,
        bezoutReductionMatrix_mul_inverse, twoRowLiftMatrix_one pivot target hne] }


theorem unimodular_topBezoutMatrix {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) : Unimodular (topBezoutMatrix (m := m) a b) :=
  (topBezoutMatrixInverseCertificate (m := m) a b).unimodular


theorem topBezoutMatrix_mul_apply_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) 0 j =
      bezoutReductionMatrix a b 0 0 * A 0 j +
        bezoutReductionMatrix a b 0 1 * A 1 j := by
  rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
    NormalForms.Matrix.Constructive.sum_univ_succ]
  simp [topBezoutMatrix_zero_zero, topBezoutMatrix_zero_one, topBezoutMatrix_zero_succ_succ]


theorem topBezoutMatrix_mul_apply_one {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) 1 j =
      bezoutReductionMatrix a b 1 0 * A 0 j +
        bezoutReductionMatrix a b 1 1 * A 1 j := by
  rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
    NormalForms.Matrix.Constructive.sum_univ_succ]
  simp [topBezoutMatrix_one_zero, topBezoutMatrix_one_one, topBezoutMatrix_one_succ_succ]


theorem topBezoutMatrix_mul_apply_succ_succ {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin m) (j : Fin n) :
    (topBezoutMatrix (m := m) a b * A) i.succ.succ j = A i.succ.succ j := by
  rw [_root_.Matrix.mul_apply, NormalForms.Matrix.Constructive.sum_univ_succ,
    NormalForms.Matrix.Constructive.sum_univ_succ]
  rw [Fin.succ_zero_eq_one]
  simp only [topBezoutMatrix_succ_succ_zero, topBezoutMatrix_succ_succ_one,
    topBezoutMatrix_succ_succ_succ_succ, _root_.Matrix.one_apply,
    zero_mul, zero_add, ite_mul, one_mul]
  rw [NormalForms.Matrix.Constructive.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]


theorem Bezout_preserves_zeros {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) (i : Fin m)
    (h : A i.succ.succ 0 = 0) :
    (topBezoutMatrix (m := m) a b * A) i.succ.succ 0 = 0 := by
  rw [topBezoutMatrix_mul_apply_succ_succ (m := m) (n := n + 1) (a := a) (b := b)
    (A := A) i (0 : Fin (n + 1))]
  exact h


theorem topBezoutMatrix_mul_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) :
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 0 0 =
      (ComputableEuclideanOps.xgcd (A 0 0) (A 1 0)).gcd := by
  have hvec := bezoutReductionMatrix_mulVec (A 0 0) (A 1 0)
  have hentry := congrFun hvec 0
  rw [_root_.Matrix.mulVec, dotProduct,
    NormalForms.Matrix.Constructive.sum_univ_two] at hentry
  calc
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 0 0
        = bezoutReductionMatrix (A 0 0) (A 1 0) 0 0 * A 0 0 +
            bezoutReductionMatrix (A 0 0) (A 1 0) 0 1 * A 1 0 :=
          topBezoutMatrix_mul_apply_zero (m := m) (n := n + 1) (A 0 0) (A 1 0) A
            (0 : Fin (n + 1))
    _ = (ComputableEuclideanOps.xgcd (A 0 0) (A 1 0)).gcd := by
          simpa using hentry


theorem topBezoutMatrix_mul_rowOneFirstCol {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) :
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 1 0 = 0 := by
  have hvec := bezoutReductionMatrix_mulVec (A 0 0) (A 1 0)
  have hentry := congrFun hvec 1
  rw [_root_.Matrix.mulVec, dotProduct,
    NormalForms.Matrix.Constructive.sum_univ_two] at hentry
  calc
    (topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A) 1 0
        = bezoutReductionMatrix (A 0 0) (A 1 0) 1 0 * A 0 0 +
            bezoutReductionMatrix (A 0 0) (A 1 0) 1 1 * A 1 0 :=
          topBezoutMatrix_mul_apply_one (m := m) (n := n + 1) (A 0 0) (A 1 0) A
            (0 : Fin (n + 1))
    _ = 0 := by
          simpa using hentry


def LeftTransform.diagLift {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (U : _root_.Matrix (Fin m) (Fin m) R) (U_cert : MatrixInverseCertificate U) :
    LeftTransform A :=
  { U := diagLiftMatrix U
    U_cert := diagLiftInverseCertificate U_cert
    B := diagLiftMatrix U * A
    left_mul := by rfl }


def LeftTransform.topBezout {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) : LeftTransform A :=
  { U := topBezoutMatrix (m := m) (A 0 0) (A 1 0)
    U_cert := topBezoutMatrixInverseCertificate (m := m) (A 0 0) (A 1 0)
    B := topBezoutMatrix (m := m) (A 0 0) (A 1 0) * A
    left_mul := by rfl }


end NormalForms.Matrix.Hermite
