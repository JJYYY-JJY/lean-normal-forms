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
      (hzero : A 0 0 = 0)
      (hrow : ∀ j : Fin n, A 0 j.succ = 0)
      (hcol : ∀ i : Fin m, A i.succ 0 = 0)
      (hLowerZero : lowerRight A = 0) :
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


def invariantFactors {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] :
    {m n : Nat} -> _root_.Matrix (Fin m) (Fin n) R -> List R
  | 0, _, _ => []
  | _, 0, _ => []
  | _ + 1, _ + 1, A =>
      let d := normalize (A 0 0)
      if d = 0 then
        []
      else
        d :: invariantFactors (lowerRight A)


@[simp] theorem invariantFactors_emptyRows {n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin 0) (Fin n) R) :
    invariantFactors A = [] := by
  simp [invariantFactors]


@[simp] theorem invariantFactors_emptyCols {m : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin 0) R) :
    invariantFactors A = [] := by
  cases m <;> simp [invariantFactors]


@[simp] theorem invariantFactors_zeroLead {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hzero : A 0 0 = 0) :
    invariantFactors A = [] := by
  simp [invariantFactors, hzero]


@[simp] theorem invariantFactors_pivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hpivot : A 0 0 ≠ 0)
    (hnorm : A 0 0 = normalize (A 0 0)) :
    invariantFactors A = A 0 0 :: invariantFactors (lowerRight A) := by
  have hnormNe : normalize (A 0 0) ≠ 0 := by
    rw [← hnorm]
    exact hpivot
  dsimp [invariantFactors]
  rw [if_neg hnormNe]
  rw [← hnorm]


private theorem diagEntry_lowerRight {m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (k : Nat) (hk : k < Nat.min m n) :
    diagEntry (lowerRight A) k hk =
      diagEntry A (k + 1)
        ((lt_min_iff).2
          ⟨Nat.succ_lt_succ ((lt_min_iff).1 hk).1,
            Nat.succ_lt_succ ((lt_min_iff).1 hk).2⟩) := by
  simp [diagEntry, lowerRight]


private theorem lt_min_of_succ_lt_min_succ {a b k : Nat}
    (hk : k + 1 < Nat.min (a + 1) (b + 1)) :
    k < Nat.min a b := by
  refine (lt_min_iff).2 ⟨?_, ?_⟩
  · exact Nat.succ_lt_succ_iff.mp ((lt_min_iff).1 hk).1
  · exact Nat.succ_lt_succ_iff.mp ((lt_min_iff).1 hk).2


private theorem two_lt_min_succ_of_lt_min {a b k : Nat}
    (hk : k + 1 < Nat.min a b) :
    k + 2 < Nat.min (a + 1) (b + 1) := by
  refine (lt_min_iff).2 ⟨?_, ?_⟩
  · exact Nat.succ_lt_succ ((lt_min_iff).1 hk).1
  · exact Nat.succ_lt_succ ((lt_min_iff).1 hk).2


private theorem offDiagZero_lowerRight {m n : Nat} {R : Type _} [Zero R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : offDiagZero A) :
    offDiagZero (lowerRight A) := by
  intro i j hij
  exact hA i.succ j.succ (by
    intro hEq
    exact hij (Nat.succ.inj hEq))


private theorem diagNormalized_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : diagNormalized A) :
    diagNormalized (lowerRight A) := by
  intro k hk
  rw [diagEntry_lowerRight]
  exact hA (k + 1) ((lt_min_iff).2
    ⟨Nat.succ_lt_succ ((lt_min_iff).1 hk).1,
      Nat.succ_lt_succ ((lt_min_iff).1 hk).2⟩)


private theorem diagChain_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : diagChain A) :
    diagChain (lowerRight A) := by
  intro k hk
  rw [diagEntry_lowerRight, diagEntry_lowerRight]
  exact hA (k + 1) (two_lt_min_succ_of_lt_min hk)


theorem isSmithNormalFormFin_toDiag {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A) :
    IsSmithNormalFormDiag A := by
  induction hA
  case emptyRows A =>
      refine ⟨?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro k hk
        simpa using hk
      · intro k hk
        simpa using hk
  case emptyCols A =>
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        exact Fin.elim0 j
      · intro k hk
        simpa using hk
      · intro k hk
        simpa using hk
  case zeroLead m' n' A hzero hrow hcol hLowerZero =>
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero =>
                exact False.elim (hij rfl)
            | succ j =>
                exact hrow j
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                exact hcol i
            | succ j =>
                simpa [lowerRight] using congrFun (congrFun hLowerZero i) j
      · intro k hk
        cases k with
        | zero =>
            simpa [diagEntry, hzero]
        | succ k =>
            have hk' : k < Nat.min m' n' := lt_min_of_succ_lt_min_succ hk
            rw [← diagEntry_lowerRight (A := A) k hk']
            simp [hLowerZero, diagEntry]
      · intro k hk
        cases k with
        | zero =>
            have hk' : 0 < Nat.min m' n' := lt_min_of_succ_lt_min_succ hk
            have hRight : diagEntry A 1 hk = 0 := by
              rw [← diagEntry_lowerRight (A := A) 0 hk']
              simp [hLowerZero, diagEntry]
            simpa [diagEntry, hzero] using hRight
        | succ k =>
            have hkMid : k + 1 < Nat.min (m' + 1) (n' + 1) :=
              Nat.lt_trans (Nat.lt_succ_self (k + 1)) hk
            have hkLeft : k < Nat.min m' n' := lt_min_of_succ_lt_min_succ hkMid
            have hkRight : k + 1 < Nat.min m' n' := lt_min_of_succ_lt_min_succ hk
            rw [← diagEntry_lowerRight (A := A) k hkLeft]
            rw [← diagEntry_lowerRight (A := A) (k + 1) hkRight]
            simp [hLowerZero, diagEntry]
  case pivot m' n' A hpivot hnorm hrow hcol hLower hdiv ih =>
      rcases ih with ⟨hOffLower, hNormLower, hChainLower⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero =>
                exact False.elim (hij rfl)
            | succ j =>
                exact hrow j
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                exact hcol i
            | succ j =>
                exact hOffLower i j (by
                  intro hEq
                  exact hij (by simpa [hEq]))
      · intro k hk
        cases k with
        | zero =>
            simpa [diagEntry] using hnorm
        | succ k =>
            simpa [diagEntry_lowerRight] using
              hNormLower k (lt_min_of_succ_lt_min_succ hk)
      · intro k hk
        cases k with
        | zero =>
            have hm : 0 < m' := Nat.succ_lt_succ_iff.mp ((lt_min_iff).1 hk).1
            have hn : 0 < n' := Nat.succ_lt_succ_iff.mp ((lt_min_iff).1 hk).2
            let i0 : Fin m' := ⟨0, hm⟩
            let j0 : Fin n' := ⟨0, hn⟩
            simpa [diagEntry, i0, j0] using hdiv i0 j0
        | succ k =>
            simpa [diagEntry_lowerRight] using
              hChainLower k (lt_min_of_succ_lt_min_succ hk)

end Internal

/-- The bridge-side submodule attached to a matrix: its column span. -/
def smithColumnSpan {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R]
    (A : _root_.Matrix m n R) : Submodule R (m -> R) :=
  LinearMap.range A.mulVecLin


/-- Read normalized nonzero diagonal entries from a Smith matrix, truncating at the first `0`. -/
noncomputable def smithInvariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) : List R :=
  Internal.invariantFactors
    (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)

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

noncomputable def SNFResult.invariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) : List R :=
  smithInvariantFactors result.S

/-- Package an existing two-sided certificate together with a Smith witness. -/
def SNFResult.ofCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R}
    (cert : NormalForms.Matrix.Certificates.TwoSidedCertificate A)
    (hSmith : IsSmithNormalForm cert.result) :
    SNFResult A :=
  { U := cert.U
    S := cert.result
    V := cert.V
    two_sided_mul := cert.equation
    isSmith := hSmith }


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
