/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import all NormalForms.Matrix.Smith.Defs
import all NormalForms.Matrix.Hermite.Bezout
import all NormalForms.Matrix.Certificates.Basic

/-!
# Smith Transform Infrastructure
Two-sided transform packaging together with the public
block-lift helpers shared by the Smith algorithm.
-/

set_option linter.privateModule false

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
  U_cert : MatrixInverseCertificate U
  B : _root_.Matrix m n R
  V : _root_.Matrix n n R
  V_cert : MatrixInverseCertificate V
  two_sided_mul : U * A * V = B


theorem TwoSidedTransform.leftUnimodular {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (t : TwoSidedTransform A) :
    Unimodular t.U :=
  t.U_cert.unimodular


theorem TwoSidedTransform.rightUnimodular {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (t : TwoSidedTransform A) :
    Unimodular t.V :=
  t.V_cert.unimodular


def TwoSidedTransform.refl {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) : TwoSidedTransform A :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    B := A
    V := 1
    V_cert := MatrixInverseCertificate.one
    two_sided_mul :=
      NormalForms.Matrix.Constructive.one_mul_mul_one A }


def TwoSidedTransform.trans {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R}
    (first : TwoSidedTransform A) (second : TwoSidedTransform first.B) :
    TwoSidedTransform A :=
  { U := second.U * first.U
    U_cert := second.U_cert.mul first.U_cert
    B := second.B
    V := first.V * second.V
    V_cert := first.V_cert.mul second.V_cert
    two_sided_mul := by
      calc
        (second.U * first.U) * A * (first.V * second.V)
            = second.U * (first.U * A * first.V) * second.V := by
                simp only [NormalForms.Matrix.Constructive.mul_assoc]
        _ = second.U * first.B * second.V := by
              rw [first.two_sided_mul]
        _ = second.B := second.two_sided_mul }


def TwoSidedTransform.ofLeftTransform {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (t : LeftTransform A) :
    TwoSidedTransform A :=
  { U := t.U
    U_cert := t.U_cert
    B := t.B
    V := 1
    V_cert := MatrixInverseCertificate.one
    two_sided_mul := by
      calc
        t.U * A * (1 : _root_.Matrix n n R) = t.U * A :=
          NormalForms.Matrix.Constructive.mul_one _
        _ = t.B := t.left_mul }


def TwoSidedTransform.ofTransposeLeftTransform {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} (t : LeftTransform A.transpose) :
    TwoSidedTransform A :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    B := t.B.transpose
    V := t.U.transpose
    V_cert := t.U_cert.transpose
    two_sided_mul := by
      have h := congrArg _root_.Matrix.transpose t.left_mul
      have htrans : A * t.U.transpose = t.B.transpose := by
        simpa only [_root_.Matrix.transpose_mul,
          _root_.Matrix.transpose_transpose] using h
      calc
        (1 : _root_.Matrix (Fin m) (Fin m) R) * A * t.U.transpose =
            A * t.U.transpose := by
          rw [NormalForms.Matrix.Constructive.one_mul]
        _ = t.B.transpose := htrans }


def TwoSidedTransform.swapRows {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i j : m) : TwoSidedTransform A :=
  { U := rowOperationMatrix (.swap i j)
    U_cert := rowSwapInverseCertificate i j
    B := applyRowOperation A (.swap i j)
    V := 1
    V_cert := MatrixInverseCertificate.one
    two_sided_mul := by
      rw [NormalForms.Matrix.Constructive.mul_one,
        rowOperationMatrix_mul] }


def TwoSidedTransform.swapCols {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i j : n) : TwoSidedTransform A :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    B := applyColumnOperation A (.swap i j)
    V := columnOperationMatrix (.swap i j)
    V_cert := columnSwapInverseCertificate i j
    two_sided_mul := by
      rw [NormalForms.Matrix.Constructive.one_mul,
        mul_columnOperationMatrix] }


def TwoSidedTransform.addRows {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (src dst : m) (c : R) (hne : src ≠ dst) :
    TwoSidedTransform A :=
  { U := rowOperationMatrix (.add src dst c)
    U_cert := rowAddInverseCertificate src dst c hne
    B := applyRowOperation A (.add src dst c)
    V := 1
    V_cert := MatrixInverseCertificate.one
    two_sided_mul := by
      rw [NormalForms.Matrix.Constructive.mul_one,
        rowOperationMatrix_mul] }


def TwoSidedTransform.addCols {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (src dst : n) (c : R) (hne : src ≠ dst) :
    TwoSidedTransform A :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    B := applyColumnOperation A (.add src dst c)
    V := columnOperationMatrix (.add src dst c)
    V_cert := columnAddInverseCertificate src dst c hne
    two_sided_mul := by
      rw [NormalForms.Matrix.Constructive.one_mul,
        mul_columnOperationMatrix] }


def TwoSidedTransform.unitSmulRow {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i : m) (u : Rˣ) :
    TwoSidedTransform A :=
  { U := rowOperationMatrix (.smul i (u : R))
    U_cert := rowUnitScaleInverseCertificate i u
    B := applyRowOperation A (.smul i (u : R))
    V := 1
    V_cert := MatrixInverseCertificate.one
    two_sided_mul := by
      rw [NormalForms.Matrix.Constructive.mul_one,
        rowOperationMatrix_mul] }


def TwoSidedTransform.unitSmulCol {m n : Type _} {R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) (i : n) (u : Rˣ) :
    TwoSidedTransform A :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    B := applyColumnOperation A (.smul i (u : R))
    V := columnOperationMatrix (.smul i (u : R))
    V_cert := columnUnitScaleInverseCertificate i u
    two_sided_mul := by
      rw [NormalForms.Matrix.Constructive.one_mul,
        mul_columnOperationMatrix] }


def TwoSidedTransform.diagLiftLeft {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (U : _root_.Matrix (Fin m) (Fin m) R) (U_cert : MatrixInverseCertificate U) :
    TwoSidedTransform A :=
  { U := diagLiftMatrix U
    U_cert := diagLiftInverseCertificate U_cert
    B := diagLiftMatrix U * A
    V := 1
    V_cert := MatrixInverseCertificate.one
    two_sided_mul := by
      rw [NormalForms.Matrix.Constructive.mul_one] }


def TwoSidedTransform.diagLiftRight {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (V : _root_.Matrix (Fin n) (Fin n) R) (V_cert : MatrixInverseCertificate V) :
    TwoSidedTransform A :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    B := A * diagLiftMatrix V
    V := diagLiftMatrix V
    V_cert := diagLiftInverseCertificate V_cert
    two_sided_mul := by
      rw [NormalForms.Matrix.Constructive.one_mul] }


@[simp] theorem mul_diagLiftMatrix_firstCol {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin m) (Fin (n + 1)) R)
    (V : _root_.Matrix (Fin n) (Fin n) R) (i : Fin m) :
    (A * diagLiftMatrix V) i 0 = A i 0 := by
  simp [diagLiftMatrix, _root_.Matrix.mul_apply,
    NormalForms.Matrix.Constructive.sum_univ_succ]


@[simp] theorem lowerRight_mul_diagLiftMatrix {m n : Nat} {R : Type _}
    [CommRing R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (V : _root_.Matrix (Fin n) (Fin n) R) :
    lowerRight (A * diagLiftMatrix V) = lowerRight A * V := by
  ext i j
  simp [diagLiftMatrix, lowerRight, _root_.Matrix.mul_apply,
    NormalForms.Matrix.Constructive.sum_univ_succ]



end NormalForms.Matrix.Smith
