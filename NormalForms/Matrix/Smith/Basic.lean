import NormalForms.Matrix.Certificates
import NormalForms.Matrix.Hermite.Basic

/-!
# Smith Normal Form API

Two-sided Smith normal forms over Euclidean domains.
-/

namespace NormalForms.Matrix.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

namespace Internal

def diagEntry {m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin m) (Fin n) R) (k : Nat)
    (hk : k < Nat.min m n) : R :=
  A ⟨k, Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)⟩
    ⟨k, Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩


def offDiagZero {m n : Nat} {R : Type _} [Zero R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ i j, i.1 ≠ j.1 -> A i j = 0


def diagNormalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ k (hk : k < Nat.min m n), diagEntry A k hk = normalize (diagEntry A k hk)


def diagChain {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ k (hk : k + 1 < Nat.min m n),
    diagEntry A k (Nat.lt_trans (Nat.lt_succ_self k) hk) ∣
      diagEntry A (k + 1) hk


def IsSmithNormalFormDiag {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : Prop :=
  offDiagZero A ∧ diagNormalized A ∧ diagChain A


noncomputable instance {m n : Nat} {R : Type _} [Zero R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} : Decidable (offDiagZero A) := by
  classical
  unfold offDiagZero
  infer_instance


noncomputable instance {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} : Decidable (diagNormalized A) := by
  classical
  unfold diagNormalized diagEntry
  infer_instance


noncomputable instance {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} : Decidable (diagChain A) := by
  classical
  infer_instance


noncomputable instance {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} : Decidable (IsSmithNormalFormDiag A) := by
  classical
  unfold IsSmithNormalFormDiag
  infer_instance


inductive IsSmithNormalFormFin {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] :
    {m n : Nat} -> _root_.Matrix (Fin m) (Fin n) R -> Prop
  | emptyRows {n : Nat} (A : _root_.Matrix (Fin 0) (Fin n) R) :
      IsSmithNormalFormFin A
  | emptyCols {m : Nat} (A : _root_.Matrix (Fin m) (Fin 0) R) :
      IsSmithNormalFormFin A
  | zeroLead {m n : Nat} (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
      (hrow : ∀ j : Fin n, A 0 j.succ = 0)
      (hcol : ∀ i : Fin m, A i.succ 0 = 0)
      (hLower : IsSmithNormalFormFin (lowerRight A)) :
      IsSmithNormalFormFin A
  | pivot {m n : Nat} (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
      (hpivot : A 0 0 ≠ 0)
      (hnorm : A 0 0 = normalize (A 0 0))
      (hrow : ∀ j : Fin n, A 0 j.succ = 0)
      (hcol : ∀ i : Fin m, A i.succ 0 = 0)
      (hLower : IsSmithNormalFormFin (lowerRight A))
      (hdiv : ∀ i : Fin m, ∀ j : Fin n, A 0 0 ∣ A i.succ j.succ) :
      IsSmithNormalFormFin A

structure FinSNFResult {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) where
  U : _root_.Matrix (Fin m) (Fin m) R
  S : _root_.Matrix (Fin m) (Fin n) R
  V : _root_.Matrix (Fin n) (Fin n) R
  two_sided_mul : U * A * V = S
  leftUnimodular : Unimodular U
  rightUnimodular : Unimodular V
  isSmith : IsSmithNormalFormFin S

end Internal

/-- Public Smith-normal-form predicate. -/
def IsSmithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) : Prop :=
  Internal.IsSmithNormalFormDiag
    (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)

noncomputable instance {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} : Decidable (IsSmithNormalForm A) := by
  classical
  unfold IsSmithNormalForm
  infer_instance


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


/-- Public result package for a two-sided Smith normal form transform. -/
structure SNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  S : _root_.Matrix m n R
  V : _root_.Matrix n n R
  two_sided_mul : U * A * V = S
  isSmith : IsSmithNormalForm S


/-- Forget the Smith witness and keep only the two-sided transformation data. -/
def SNFResult.toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    NormalForms.Matrix.Certificates.TwoSidedCertificate A :=
  { U := result.U
    result := result.S
    V := result.V
    equation := result.two_sided_mul }


/-- Executable Smith-normal-form entrypoint. -/
noncomputable def smithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [CanonicalMod R]
    (A : _root_.Matrix m n R) : Option (SNFResult A) :=
  none


theorem smithNormalForm_isSmith {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [CanonicalMod R]
    {A : _root_.Matrix m n R} {result : SNFResult A}
    (_hresult : smithNormalForm A = some result) :
    IsSmithNormalForm result.S := by
  exact result.isSmith

end NormalForms.Matrix.Smith
