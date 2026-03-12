import NormalForms.Matrix.Smith.Defs
import NormalForms.Matrix.Hermite.Bezout

/-!
# Smith Transform Infrastructure
Two-sided transform packaging together with the public
block-lift helpers shared by the Smith algorithm.
-/

namespace NormalForms.Matrix.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

theorem unimodular_transpose {m R : Type _}
    [Fintype m] [DecidableEq m] [CommRing R]
    {U : _root_.Matrix m m R} (hU : Unimodular U) :
    Unimodular U.transpose := by
  simpa [Unimodular, _root_.Matrix.det_transpose] using hU


structure TwoSidedTransform {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  B : _root_.Matrix m n R
  V : _root_.Matrix n n R
  two_sided_mul : U * A * V = B
  leftUnimodular : Unimodular U
  rightUnimodular : Unimodular V


def TwoSidedTransform.refl {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) : TwoSidedTransform A :=
  { U := 1
    B := A
    V := 1
    two_sided_mul := by simp
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_one }


def TwoSidedTransform.trans {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R}
    (first : TwoSidedTransform A) (second : TwoSidedTransform first.B) :
    TwoSidedTransform A :=
  { U := second.U * first.U
    B := second.B
    V := first.V * second.V
    two_sided_mul := by
      calc
        (second.U * first.U) * A * (first.V * second.V)
            = second.U * (first.U * A * first.V) * second.V := by
                simp [Matrix.mul_assoc]
        _ = second.U * first.B * second.V := by
              rw [first.two_sided_mul]
        _ = second.B := second.two_sided_mul
    leftUnimodular := unimodular_mul second.leftUnimodular first.leftUnimodular
    rightUnimodular := unimodular_mul first.rightUnimodular second.rightUnimodular }


def TwoSidedTransform.ofLeftTransform {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (t : LeftTransform A) :
    TwoSidedTransform A :=
  { U := t.U
    B := t.B
    V := 1
    two_sided_mul := by simpa using t.left_mul
    leftUnimodular := t.unimodular
    rightUnimodular := unimodular_one }


def TwoSidedTransform.ofTransposeLeftTransform {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} (t : LeftTransform A.transpose) :
    TwoSidedTransform A :=
  { U := 1
    B := t.B.transpose
    V := t.U.transpose
    two_sided_mul := by
      have h := congrArg _root_.Matrix.transpose t.left_mul
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using h
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_transpose t.unimodular }


def TwoSidedTransform.swapRows {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i j : m) : TwoSidedTransform A :=
  { U := rowOperationMatrix (.swap i j)
    B := applyRowOperation A (.swap i j)
    V := 1
    two_sided_mul := by
      simp [rowOperationMatrix_mul]
    leftUnimodular := unimodular_rowOperationMatrix (.swap i j) (by trivial)
    rightUnimodular := unimodular_one }


def TwoSidedTransform.swapCols {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i j : n) : TwoSidedTransform A :=
  { U := 1
    B := applyColumnOperation A (.swap i j)
    V := columnOperationMatrix (.swap i j)
    two_sided_mul := by
      simp [mul_columnOperationMatrix]
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_columnOperationMatrix (.swap i j) (by trivial) }


def TwoSidedTransform.addRows {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (src dst : m) (c : R) (hne : src ≠ dst) :
    TwoSidedTransform A :=
  { U := rowOperationMatrix (.add src dst c)
    B := applyRowOperation A (.add src dst c)
    V := 1
    two_sided_mul := by
      simp [rowOperationMatrix_mul]
    leftUnimodular := unimodular_rowOperationMatrix (.add src dst c) hne
    rightUnimodular := unimodular_one }


def TwoSidedTransform.addCols {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (src dst : n) (c : R) (hne : src ≠ dst) :
    TwoSidedTransform A :=
  { U := 1
    B := applyColumnOperation A (.add src dst c)
    V := columnOperationMatrix (.add src dst c)
    two_sided_mul := by
      simp [mul_columnOperationMatrix]
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_columnOperationMatrix (.add src dst c) hne }


def TwoSidedTransform.unitSmulRow {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i : m) (c : R) (hc : IsUnit c) :
    TwoSidedTransform A :=
  { U := rowOperationMatrix (.smul i c)
    B := applyRowOperation A (.smul i c)
    V := 1
    two_sided_mul := by
      simp [rowOperationMatrix_mul]
    leftUnimodular := unimodular_rowOperationMatrix (.smul i c) hc
    rightUnimodular := unimodular_one }


def TwoSidedTransform.unitSmulCol {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i : n) (c : R) (hc : IsUnit c) :
    TwoSidedTransform A :=
  { U := 1
    B := applyColumnOperation A (.smul i c)
    V := columnOperationMatrix (.smul i c)
    two_sided_mul := by
      simp [mul_columnOperationMatrix]
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_columnOperationMatrix (.smul i c) hc }


def TwoSidedTransform.diagLiftLeft {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (U : _root_.Matrix (Fin m) (Fin m) R) (hU : Unimodular U) :
    TwoSidedTransform A :=
  { U := diagLiftMatrix U
    B := diagLiftMatrix U * A
    V := 1
    two_sided_mul := by simp [Matrix.mul_assoc]
    leftUnimodular := unimodular_diagLiftMatrix hU
    rightUnimodular := unimodular_one }


def TwoSidedTransform.diagLiftRight {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (V : _root_.Matrix (Fin n) (Fin n) R) (hV : Unimodular V) :
    TwoSidedTransform A :=
  { U := 1
    B := A * diagLiftMatrix V
    V := diagLiftMatrix V
    two_sided_mul := by simp [Matrix.mul_assoc]
    leftUnimodular := unimodular_one
    rightUnimodular := unimodular_diagLiftMatrix hV }


@[simp] theorem mul_diagLiftMatrix_firstCol {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) R)
    (V : _root_.Matrix (Fin n) (Fin n) R) (i : Fin m) :
    (A * diagLiftMatrix V) i 0 = A i 0 := by
  simp [diagLiftMatrix, _root_.Matrix.mul_apply, Fin.sum_univ_succ]


@[simp] theorem lowerRight_mul_diagLiftMatrix {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (V : _root_.Matrix (Fin n) (Fin n) R) :
    lowerRight (A * diagLiftMatrix V) = lowerRight A * V := by
  ext i j
  simp [diagLiftMatrix, lowerRight, _root_.Matrix.mul_apply, Fin.sum_univ_succ]



end NormalForms.Matrix.Smith
