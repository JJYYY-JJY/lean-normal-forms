import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NormalForms.Matrix.Smith.Basic

/-!
# Smith Uniqueness Helpers

Auxiliary uniqueness lemmas for Smith-normal-form matrices.
-/

namespace NormalForms.Matrix.Smith

open NormalForms.Matrix.Hermite

namespace Internal

private theorem succ_lt_min_succ {k m n : Nat} (hk : k < Nat.min m n) :
    k.succ < Nat.min m.succ n.succ := by
  exact lt_min_iff.mpr
    ⟨Nat.succ_lt_succ (lt_min_iff.mp hk).1, Nat.succ_lt_succ (lt_min_iff.mp hk).2⟩

private theorem succ_le_min_succ {k m n : Nat} (hk : k ≤ Nat.min m n) :
    k.succ ≤ Nat.min m.succ n.succ := by
  exact le_min_iff.mpr
    ⟨Nat.succ_le_succ (le_min_iff.mp hk).1, Nat.succ_le_succ (le_min_iff.mp hk).2⟩

private theorem diagEntry_lowerRight {m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (k : Nat) (hk : k < Nat.min m n) :
    diagEntry (lowerRight A) k hk =
      diagEntry A (k + 1) (succ_lt_min_succ hk) := by
  simp [diagEntry, lowerRight]

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
  simpa [diagEntry_lowerRight (A := A)] using hA (k + 1) (succ_lt_min_succ hk)

private theorem diagChain_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : diagChain A) :
    diagChain (lowerRight A) := by
  intro k hk
  rw [diagEntry_lowerRight, diagEntry_lowerRight]
  exact hA (k + 1) (succ_lt_min_succ hk)

private theorem isSmithNormalFormDiag_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : IsSmithNormalFormDiag A) :
    IsSmithNormalFormDiag (lowerRight A) := by
  rcases hA with ⟨hOff, hNorm, hChain⟩
  exact ⟨offDiagZero_lowerRight hOff, diagNormalized_lowerRight hNorm, diagChain_lowerRight hChain⟩

private theorem diagEntry_eq_zero_of_head_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hChain : diagChain A) (hzero : A 0 0 = 0) :
    ∀ k (hk : k < Nat.min (m + 1) (n + 1)), diagEntry A k hk = 0
  | 0, _ => by
      simpa [diagEntry] using hzero
  | k + 1, hk => by
      have hkPrev : k < Nat.min (m + 1) (n + 1) := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hdiv : diagEntry A k hkPrev ∣ diagEntry A (k + 1) hk := by
        simpa using hChain k hk
      rw [diagEntry_eq_zero_of_head_zero hChain hzero k hkPrev] at hdiv
      exact zero_dvd_iff.mp hdiv

private theorem lowerRight_eq_zero_of_head_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hOff : offDiagZero A) (hChain : diagChain A) (hzero : A 0 0 = 0) :
    lowerRight A = 0 := by
  ext i j
  by_cases hij : i.1 = j.1
  · have hk : j.1 + 1 < Nat.min (m + 1) (n + 1) := by
      refine lt_min_iff.mpr ?_
      constructor
      · exact Nat.succ_lt_succ (by simpa [hij] using i.is_lt)
      · exact Nat.succ_lt_succ j.is_lt
    have hdiag : diagEntry A (j.1 + 1) hk = 0 :=
      diagEntry_eq_zero_of_head_zero hChain hzero (j.1 + 1) hk
    have hrow :
        i.succ = ⟨j.1 + 1, Nat.succ_lt_succ (by simpa [hij] using i.is_lt)⟩ := by
      ext
      simp [hij]
    have hcol :
        j.succ = ⟨j.1 + 1, Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩ := by
      ext
      simp
    calc
      (lowerRight A) i j = A i.succ j.succ := rfl
      _ = A ⟨j.1 + 1, Nat.succ_lt_succ (by simpa [hij] using i.is_lt)⟩
            ⟨j.1 + 1, Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩ := by rw [hrow, hcol]
      _ = diagEntry A (j.1 + 1) hk := by simp [diagEntry]
      _ = 0 := hdiag
  · exact hOff i.succ j.succ (by simpa using hij)

private theorem headDiag_dvd_diagEntry_of_diagChain {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hChain : diagChain A) :
    ∀ k (hk : k < Nat.min m n),
      A 0 0 ∣ diagEntry A (k + 1) (succ_lt_min_succ hk)
  | 0, hk => by
      simpa [diagEntry] using hChain 0 (succ_lt_min_succ hk)
  | k + 1, hk => by
      have hkPrev : k < Nat.min m n := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hprev : A 0 0 ∣ diagEntry A (k + 1) (succ_lt_min_succ hkPrev) :=
        headDiag_dvd_diagEntry_of_diagChain hChain k hkPrev
      have hnext :
          diagEntry A (k + 1) (succ_lt_min_succ hkPrev) ∣
            diagEntry A (k + 2) (succ_lt_min_succ hk) := by
        simpa using hChain (k + 1) (succ_lt_min_succ hk)
      exact dvd_trans hprev hnext

private theorem det_submatrix_mul_aux {k m n p : Nat} {R : Type _}
    [CommRing R]
    {M : _root_.Matrix (Fin m) (Fin n) R}
    {N : _root_.Matrix (Fin n) (Fin p) R}
    {r : Fin k ↪ Fin m} {c : Fin k ↪ Fin p}
    {f : Fin k → Fin n}
    (hf : ¬ Function.Injective f) :
    (∑ σ : Equiv.Perm (Fin k),
      (↑(Equiv.Perm.sign σ : ℤˣ) : R) * ∏ i, M (r (σ i)) (f i) * N (f i) (c i)) = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    rw [Function.Injective] at hf
    push_neg at hf
    exact hf
  have hFactor :
      (∑ σ : Equiv.Perm (Fin k),
        (↑(Equiv.Perm.sign σ : ℤˣ) : R) * ∏ i, M (r (σ i)) (f i) * N (f i) (c i)) =
        (∏ i, N (f i) (c i)) * ∑ σ : Equiv.Perm (Fin k),
          (↑(Equiv.Perm.sign σ : ℤˣ) : R) * ∏ i, M (r (σ i)) (f i) := by
    simp_rw [Finset.prod_mul_distrib]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  have hdet : _root_.Matrix.det (M.submatrix r f) = 0 := by
    apply _root_.Matrix.det_zero_of_column_eq hne
    intro l
    simp [hij]
  calc
    (∑ σ : Equiv.Perm (Fin k),
      (↑(Equiv.Perm.sign σ : ℤˣ) : R) * ∏ i, M (r (σ i)) (f i) * N (f i) (c i)) =
        (∏ i, N (f i) (c i)) * _root_.Matrix.det (M.submatrix r f) := by
            rw [hFactor, _root_.Matrix.det_apply']
            apply congrArg ((∏ i, N (f i) (c i)) * ·)
            simp
    _ = 0 := by simp [hdet]

private theorem det_submatrix_mul_sum_embeddings {k m n p : Nat} {R : Type _}
    [CommRing R]
    (M : _root_.Matrix (Fin m) (Fin n) R)
    (N : _root_.Matrix (Fin n) (Fin p) R)
    (r : Fin k ↪ Fin m)
    (c : Fin k ↪ Fin p) :
    _root_.Matrix.det ((M * N).submatrix r c) =
      ∑ e : Fin k ↪ Fin n, _root_.Matrix.det (M.submatrix r e) * ∏ i, N (e i) (c i) := by
  classical
  calc
    _root_.Matrix.det ((M * N).submatrix r c) =
        ∑ σ : Equiv.Perm (Fin k),
          (↑(Equiv.Perm.sign σ : ℤˣ) : R) *
            ∏ i, ∑ j : Fin n, M (r (σ i)) j * N j (c i) := by
          rw [_root_.Matrix.det_apply']
          simp [_root_.Matrix.mul_apply]
    _ = ∑ σ : Equiv.Perm (Fin k),
          ∑ f : Fin k → Fin n,
            (↑(Equiv.Perm.sign σ : ℤˣ) : R) *
              ∏ i, M (r (σ i)) (f i) * N (f i) (c i) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [Finset.prod_univ_sum, Finset.mul_sum]
          simp [Fintype.piFinset_univ]
    _ = ∑ f : Fin k → Fin n,
          ∑ σ : Equiv.Perm (Fin k),
            (↑(Equiv.Perm.sign σ : ℤˣ) : R) *
              ∏ i, M (r (σ i)) (f i) * N (f i) (c i) := by
          rw [Finset.sum_comm]
    _ = ∑ f : Fin k → Fin n with Function.Injective f,
          ∑ σ : Equiv.Perm (Fin k),
            (↑(Equiv.Perm.sign σ : ℤˣ) : R) *
              ∏ i, M (r (σ i)) (f i) * N (f i) (c i) := by
          refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
          intro f hf hnotinj
          have hf' : ¬ Function.Injective f := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnotinj
          exact det_submatrix_mul_aux (hf := hf')
    _ = ∑ e : Fin k ↪ Fin n,
          ∑ σ : Equiv.Perm (Fin k),
            (↑(Equiv.Perm.sign σ : ℤˣ) : R) *
              ∏ i, M (r (σ i)) (e i) * N (e i) (c i) := by
          refine Finset.sum_bij (fun f hf => ⟨f, (Finset.mem_filter.mp hf).2⟩)
            (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
          · intro f hf g hg hfg
            simpa using congrArg Function.Embedding.toFun hfg
          · intro e he
            refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.injective⟩, ?_⟩
            rfl
          · intro f hf
            rfl
    _ = ∑ e : Fin k ↪ Fin n, _root_.Matrix.det (M.submatrix r e) * ∏ i, N (e i) (c i) := by
          apply Finset.sum_congr rfl
          intro e he
          have hFactor :
              (∑ σ : Equiv.Perm (Fin k),
                (↑(Equiv.Perm.sign σ : ℤˣ) : R) *
                  ∏ i, M (r (σ i)) (e i) * N (e i) (c i)) =
                (∏ i, N (e i) (c i)) * ∑ σ : Equiv.Perm (Fin k),
                  (↑(Equiv.Perm.sign σ : ℤˣ) : R) * ∏ i, M (r (σ i)) (e i) := by
            simp_rw [Finset.prod_mul_distrib]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro σ hσ
            ring
          rw [hFactor, _root_.Matrix.det_apply']
          simp
          ring

private theorem minor_dvd_of_right_mul {k m n p : Nat} {R : Type _}
    [CommRing R]
    {d : R}
    {M : _root_.Matrix (Fin m) (Fin n) R}
    {N : _root_.Matrix (Fin n) (Fin p) R}
    (hM : ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n, d ∣ _root_.Matrix.det (M.submatrix r c)) :
    ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin p, d ∣ _root_.Matrix.det ((M * N).submatrix r c) := by
  intro r c
  rw [det_submatrix_mul_sum_embeddings M N r c]
  refine Finset.dvd_sum ?_
  intro e he
  rcases hM r e with ⟨x, hx⟩
  refine ⟨x * ∏ i, N (e i) (c i), ?_⟩
  rw [hx]
  ring

private theorem minor_dvd_of_left_mul {k m n : Nat} {R : Type _}
    [CommRing R]
    {d : R}
    {U : _root_.Matrix (Fin m) (Fin m) R}
    {M : _root_.Matrix (Fin m) (Fin n) R}
    (hM : ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n, d ∣ _root_.Matrix.det (M.submatrix r c)) :
    ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n, d ∣ _root_.Matrix.det ((U * M).submatrix r c) := by
  intro r c
  have hTranspose :
      ∀ r' : Fin k ↪ Fin n, ∀ c' : Fin k ↪ Fin m,
        d ∣ _root_.Matrix.det (M.transpose.submatrix r' c') := by
    intro r' c'
    have hEq : _root_.Matrix.det (M.transpose.submatrix r' c') = _root_.Matrix.det (M.submatrix c' r') := by
      simpa [_root_.Matrix.transpose_submatrix] using
        (_root_.Matrix.det_transpose (M := M.submatrix c' r'))
    rw [hEq]
    exact hM c' r'
  have hRight : d ∣ _root_.Matrix.det ((M.transpose * U.transpose).submatrix c r) :=
    minor_dvd_of_right_mul (M := M.transpose) (N := U.transpose) (d := d) hTranspose c r
  have hEq : _root_.Matrix.det ((M.transpose * U.transpose).submatrix c r) = _root_.Matrix.det ((U * M).submatrix r c) := by
    calc
      _root_.Matrix.det ((M.transpose * U.transpose).submatrix c r)
          = _root_.Matrix.det (((U * M).submatrix r c).transpose) := by
              simp [_root_.Matrix.transpose_mul, _root_.Matrix.transpose_submatrix]
      _ = _root_.Matrix.det ((U * M).submatrix r c) := by rw [_root_.Matrix.det_transpose]
  rw [hEq] at hRight
  exact hRight


def firstInvariantFactor {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizedGCDMonoid R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : R :=
  (Finset.univ : Finset (Fin m × Fin n)).gcd fun p => A p.1 p.2

theorem firstInvariantFactor_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizedGCDMonoid R]
    (A : _root_.Matrix (Fin m) (Fin n) R) :
    normalize (firstInvariantFactor A) = firstInvariantFactor A := by
  simpa [firstInvariantFactor] using
    (Finset.normalize_gcd
      (s := (Finset.univ : Finset (Fin m × Fin n)))
      (f := fun p : Fin m × Fin n => A p.1 p.2))

private theorem firstInvariantFactor_dvd_entry {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizedGCDMonoid R]
    (A : _root_.Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    firstInvariantFactor A ∣ A i j := by
  simpa [firstInvariantFactor] using
    (Finset.gcd_dvd
      (s := (Finset.univ : Finset (Fin m × Fin n)))
      (f := fun p : Fin m × Fin n => A p.1 p.2)
      (b := (i, j))
      (by simp))

private theorem dvd_firstInvariantFactor {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizedGCDMonoid R]
    {d : R} {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : ∀ i : Fin m, ∀ j : Fin n, d ∣ A i j) :
    d ∣ firstInvariantFactor A := by
  simpa [firstInvariantFactor] using
    (Finset.dvd_gcd
      (s := (Finset.univ : Finset (Fin m × Fin n)))
      (f := fun p : Fin m × Fin n => A p.1 p.2)
      (fun p _ => hA p.1 p.2))

private def singleRowEmb {m : Nat} (i : Fin m) : Fin 1 ↪ Fin m where
  toFun := fun _ => i
  inj' := by
    intro a b _
    exact Subsingleton.elim _ _

private def singleColEmb {n : Nat} (j : Fin n) : Fin 1 ↪ Fin n where
  toFun := fun _ => j
  inj' := by
    intro a b _
    exact Subsingleton.elim _ _

@[simp] private theorem det_submatrix_singleton {m n : Nat} {R : Type _}
    [CommRing R]
    (A : _root_.Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    _root_.Matrix.det (A.submatrix (singleRowEmb i) (singleColEmb j)) = A i j := by
  rw [_root_.Matrix.det_fin_one]
  rfl

private theorem firstInvariantFactor_dvd_two_sided_mul {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizedGCDMonoid R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    {U : _root_.Matrix (Fin m) (Fin m) R}
    {V : _root_.Matrix (Fin n) (Fin n) R} :
    firstInvariantFactor A ∣ firstInvariantFactor (U * A * V) := by
  let d := firstInvariantFactor A
  refine dvd_firstInvariantFactor ?_
  intro i j
  have hAminors :
      ∀ r : Fin 1 ↪ Fin m, ∀ c : Fin 1 ↪ Fin n,
        d ∣ _root_.Matrix.det (A.submatrix r c) := by
    intro r c
    have hentry : d ∣ A (r 0) (c 0) :=
      firstInvariantFactor_dvd_entry A (r 0) (c 0)
    rw [_root_.Matrix.det_fin_one]
    simpa using hentry
  have hLeft :
      ∀ r : Fin 1 ↪ Fin m, ∀ c : Fin 1 ↪ Fin n,
        d ∣ _root_.Matrix.det ((U * A).submatrix r c) :=
    minor_dvd_of_left_mul (k := 1) (U := U) (M := A) (d := d) hAminors
  have hRight :
      ∀ r : Fin 1 ↪ Fin m, ∀ c : Fin 1 ↪ Fin n,
        d ∣ _root_.Matrix.det (((U * A) * V).submatrix r c) :=
    minor_dvd_of_right_mul (k := 1) (M := U * A) (N := V) (d := d) hLeft
  have hminor :
      d ∣ _root_.Matrix.det (((U * A) * V).submatrix (singleRowEmb i) (singleColEmb j)) :=
    hRight (singleRowEmb i) (singleColEmb j)
  rw [det_submatrix_singleton] at hminor
  simpa [d, _root_.Matrix.mul_assoc] using hminor

theorem first_invariantFactor_eq_of_two_sided_equiv {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizedGCDMonoid R]
    {A B : _root_.Matrix (Fin m) (Fin n) R}
    {U : _root_.Matrix (Fin m) (Fin m) R}
    {V : _root_.Matrix (Fin n) (Fin n) R}
    (hU : NormalForms.Matrix.Certificates.Unimodular U)
    (hV : NormalForms.Matrix.Certificates.Unimodular V)
    (hEq : U * A * V = B) :
    firstInvariantFactor A = firstInvariantFactor B := by
  have hAB : firstInvariantFactor A ∣ firstInvariantFactor B := by
    rw [← hEq]
    exact firstInvariantFactor_dvd_two_sided_mul (A := A) (U := U) (V := V)
  have hEqInv : U⁻¹ * B * V⁻¹ = A := by
    calc
      U⁻¹ * B * V⁻¹ = U⁻¹ * (U * A * V) * V⁻¹ := by rw [hEq]
      _ = U⁻¹ * (U * (A * V)) * V⁻¹ := by simp [_root_.Matrix.mul_assoc]
      _ = (A * V) * V⁻¹ := by
        rw [_root_.Matrix.nonsing_inv_mul_cancel_left (A := U) (B := A * V) hU]
      _ = A := by
        rw [_root_.Matrix.mul_nonsing_inv_cancel_right (A := V) (B := A) hV]
  have hBA : firstInvariantFactor B ∣ firstInvariantFactor A := by
    rw [← hEqInv]
    exact firstInvariantFactor_dvd_two_sided_mul (A := B) (U := U⁻¹) (V := V⁻¹)
  exact dvd_antisymm_of_normalize_eq
    (firstInvariantFactor_normalized A)
    (firstInvariantFactor_normalized B)
    hAB hBA

def diagPrefixProduct {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin m) (Fin n) R) (k : Nat)
    (hk : k ≤ Nat.min m n) : R :=
  ∏ i : Fin k, diagEntry A i.1 (lt_of_lt_of_le i.is_lt hk)

private def liftEmbeddingSucc {k m : Nat}
    (r : Fin k ↪ Fin m) :
    Fin k ↪ Fin (m + 1) where
  toFun := fun i => (r i).succ
  inj' := by
    intro i j hij
    exact r.inj' (by simpa using hij)

private def tailEmbeddingOfHeadZero {k m : Nat}
    (r : Fin (k + 1) ↪ Fin (m + 1)) (hr0 : r 0 = 0) :
    Fin k ↪ Fin m where
  toFun := fun i => (r i.succ).pred (by
    intro h
    have : i.succ = 0 := r.inj' (by simpa [hr0] using h)
    exact i.succ_ne_zero this)
  inj' := by
    intro i j hij
    have hEq : r i.succ = r j.succ := by
      simpa using congrArg Fin.succ hij
    simpa using r.inj' hEq
private theorem submatrix_lowerRight_eq_submatrix_tail {k m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (r : Fin (k + 1) ↪ Fin (m + 1)) (c : Fin (k + 1) ↪ Fin (n + 1))
    (hr0 : r 0 = 0) (hc0 : c 0 = 0) :
    lowerRight (A.submatrix r c) =
      (lowerRight A).submatrix (tailEmbeddingOfHeadZero r hr0) (tailEmbeddingOfHeadZero c hc0) := by
  ext i j
  simp [lowerRight, tailEmbeddingOfHeadZero]

private theorem submatrix_tail_reindex_via_predAbove {k m n : Nat} {R : Type _}
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R)
    (r : Fin k ↪ Fin (m + 1)) (c : Fin k ↪ Fin (n + 1))
    (hr : ∀ i, r i ≠ 0) (hc : ∀ j, c j ≠ 0) :
    ∃ r' : Fin k ↪ Fin m, ∃ c' : Fin k ↪ Fin n,
      A.submatrix r c = (lowerRight A).submatrix r' c' := by
  let r' : Fin k ↪ Fin m := {
    toFun := fun i => (r i).pred (hr i)
    inj' := by
      intro i j hij
      have hEq : r i = r j := by
        simpa using congrArg Fin.succ hij
      exact r.inj' hEq
  }
  let c' : Fin k ↪ Fin n := {
    toFun := fun j => (c j).pred (hc j)
    inj' := by
      intro i j hij
      have hEq : r i = r j := by
        simpa using congrArg Fin.succ hij
      exact r.inj' hEq
  }
  refine ⟨r', c', ?_⟩
  ext i j
  simp [r', c', lowerRight]

private theorem det_minor_head_factor_of_offDiagZero {k m n : Nat} {R : Type _}
    [CommRing R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hOff : offDiagZero A)
    (r : Fin (k + 1) ↪ Fin (m + 1)) (c : Fin (k + 1) ↪ Fin (n + 1))
    (hr0 : r 0 = 0) (hc0 : c 0 = 0) :
    _root_.Matrix.det (A.submatrix r c) =
      A 0 0 * _root_.Matrix.det
        ((lowerRight A).submatrix (tailEmbeddingOfHeadZero r hr0) (tailEmbeddingOfHeadZero c hc0)) := by
  let M := A.submatrix r c
  let f : Fin (k + 1) → R := fun j =>
    (-1) ^ (j : ℕ) * M 0 j * _root_.Matrix.det (M.submatrix Fin.succ (Fin.succAbove j))
  have hsum : ∑ j : Fin (k + 1), f j = f 0 := by
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro j _ hj
      have hcj : c j ≠ 0 := by
        intro h
        exact hj (c.inj' (by simpa [hc0] using h))
      have hzeroEntry : M 0 j = 0 := by
        exact hOff (r 0) (c j) (by
          intro hval
          apply hcj
          ext
          simpa [hr0] using hval.symm)
      simp [f, hzeroEntry]
    · intro h0
      simp at h0
  calc
    _root_.Matrix.det M = ∑ j : Fin (k + 1), f j := by
      rw [_root_.Matrix.det_succ_row_zero]
    _ = f 0 := hsum
    _ = A 0 0 * _root_.Matrix.det ((A.submatrix r c).submatrix Fin.succ Fin.succ) := by
      simp [f, M, hr0, hc0]
    _ = A 0 0 * _root_.Matrix.det (lowerRight (A.submatrix r c)) := by
      rfl
    _ = A 0 0 * _root_.Matrix.det
          ((lowerRight A).submatrix (tailEmbeddingOfHeadZero r hr0) (tailEmbeddingOfHeadZero c hc0)) := by
      rw [submatrix_lowerRight_eq_submatrix_tail A r c hr0 hc0]
private theorem det_minor_zero_of_missing_head_row {k m n : Nat} {R : Type _}
    [CommRing R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hOff : offDiagZero A)
    (r : Fin (k + 1) ↪ Fin (m + 1)) (c : Fin (k + 1) ↪ Fin (n + 1))
    (hr0 : r 0 = 0) (hc : ∀ j, c j ≠ 0) :
    _root_.Matrix.det (A.submatrix r c) = 0 := by
  apply _root_.Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  exact hOff (r 0) (c j) (by
    intro hval
    apply hc j
    ext
    simpa [hr0] using hval.symm)
private theorem det_minor_zero_of_missing_head_col {k m n : Nat} {R : Type _}
    [CommRing R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hOff : offDiagZero A)
    (r : Fin (k + 1) ↪ Fin (m + 1)) (c : Fin (k + 1) ↪ Fin (n + 1))
    (hr : ∀ i, r i ≠ 0) (hc0 : c 0 = 0) :
    _root_.Matrix.det (A.submatrix r c) = 0 := by
  apply _root_.Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  exact hOff (r i) (c 0) (by
    intro hval
    apply hr i
    ext
    simpa [hc0] using hval)

private theorem det_minor_eq_head_mul_lowerRight_minor {k m n : Nat} {R : Type _}
    [CommRing R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hOff : offDiagZero A) (h00 : A 0 0 ≠ 0)
    (r : Fin (k + 1) ↪ Fin (m + 1)) (c : Fin (k + 1) ↪ Fin (n + 1))
    (hr0 : r 0 = 0) (hc0 : c 0 = 0) :
    _root_.Matrix.det (A.submatrix r c) =
      A 0 0 * _root_.Matrix.det
        ((lowerRight A).submatrix (tailEmbeddingOfHeadZero r hr0) (tailEmbeddingOfHeadZero c hc0)) := by
  let _ := h00
  simpa using det_minor_head_factor_of_offDiagZero (A := A) hOff r c hr0 hc0

private theorem diagPrefixProduct_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (hk : 0 ≤ Nat.min m n) :
    diagPrefixProduct A 0 hk = 1 := by
  simp [diagPrefixProduct]

private theorem diagPrefixProduct_succ {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin m) (Fin n) R) (k : Nat)
    (hk : k + 1 ≤ Nat.min m n) :
    diagPrefixProduct A (k + 1) hk =
      diagPrefixProduct A k (Nat.le_trans (Nat.le_succ k) hk) *
        diagEntry A k (lt_of_lt_of_le (Nat.lt_succ_self k) hk) := by
  let f : Fin (k + 1) → R := fun i => diagEntry A i.1 (lt_of_lt_of_le i.is_lt hk)
  simpa [diagPrefixProduct, f, Nat.le_trans (Nat.le_succ k) hk] using Fin.prod_univ_castSucc f

private theorem diagPrefixProduct_dvd_of_tail {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hChain : diagChain A)
    (k : Nat) (hk : k + 1 ≤ Nat.min m n) :
    diagPrefixProduct A k (Nat.le_trans (Nat.le_succ k) hk) ∣
      diagPrefixProduct A (k + 1) hk := by
  let _ := hChain
  refine ⟨diagEntry A k (lt_of_lt_of_le (Nat.lt_succ_self k) hk), ?_⟩
  rw [diagPrefixProduct_succ A k hk]

private theorem diagPrefixProduct_head_mul_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (k : Nat)
    (hk : k ≤ Nat.min m n) :
    diagPrefixProduct A (k + 1) (succ_le_min_succ hk) =
      A 0 0 * diagPrefixProduct (lowerRight A) k hk := by
  let f : Fin (k + 1) → R := fun i =>
    diagEntry A i.1 (lt_of_lt_of_le i.is_lt (succ_le_min_succ hk))
  simpa [diagPrefixProduct, f, diagEntry, diagEntry_lowerRight] using Fin.prod_univ_succ f
private theorem diagPrefixProduct_dvd_minor_step {m n k : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hOff : offDiagZero A) (hChain : diagChain A) (h00 : A 0 0 ≠ 0)
    (hk : k ≤ Nat.min m n)
    (hTail : ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
      diagPrefixProduct (lowerRight A) k hk ∣
        _root_.Matrix.det ((lowerRight A).submatrix r c)) :
    ∀ r : Fin (k + 1) ↪ Fin (m + 1), ∀ c : Fin (k + 1) ↪ Fin (n + 1),
      diagPrefixProduct A (k + 1) (succ_le_min_succ hk) ∣
        _root_.Matrix.det (A.submatrix r c) := by
  let _ := h00
  intro r c
  have hprefix :
      diagPrefixProduct A (k + 1) (succ_le_min_succ hk) =
        A 0 0 * diagPrefixProduct (lowerRight A) k hk :=
    diagPrefixProduct_head_mul_lowerRight A k hk
  by_cases hrow : ∃ i, r i = 0
  · rcases hrow with ⟨i, hi⟩
    by_cases hcol : ∃ j, c j = 0
    · rcases hcol with ⟨j, hj⟩
      rw [_root_.Matrix.det_succ_row (A := A.submatrix r c) i]
      apply Finset.dvd_sum
      intro t ht
      by_cases htj : t = j
      · subst t
        let rTail : Fin k ↪ Fin (m + 1) := {
          toFun := fun u => r (i.succAbove u)
          inj' := by
            intro u v huv
            exact i.succAbove_right_injective (r.inj' huv)
        }
        let cTail : Fin k ↪ Fin (n + 1) := {
          toFun := fun u => c (Fin.succAbove j u)
          inj' := by
            intro u v huv
            have hjinj : Function.Injective (Fin.succAbove j) := Fin.succAbove_right_injective
            exact hjinj (c.inj' huv)
        }
        have hrTail : ∀ u, rTail u ≠ 0 := by
          intro u hu
          have : i.succAbove u = i := r.inj' (by simpa [rTail, hi] using hu)
          exact Fin.ne_succAbove i u this.symm
        have hcTail : ∀ u, cTail u ≠ 0 := by
          intro u hu
          have : Fin.succAbove j u = j := c.inj' (by simpa [cTail, hj] using hu)
          exact Fin.ne_succAbove j u this.symm
        obtain ⟨r', c', hEqTail⟩ :=
          submatrix_tail_reindex_via_predAbove A rTail cTail hrTail hcTail
        have hminor :
            diagPrefixProduct (lowerRight A) k hk ∣
              _root_.Matrix.det ((A.submatrix r c).submatrix i.succAbove (Fin.succAbove j)) := by
          change diagPrefixProduct (lowerRight A) k hk ∣ _root_.Matrix.det (A.submatrix rTail cTail)
          rw [hEqTail]
          exact hTail r' c'
        have hmul :
            diagPrefixProduct A (k + 1) (succ_le_min_succ hk) ∣
              A 0 0 * _root_.Matrix.det ((A.submatrix r c).submatrix i.succAbove (Fin.succAbove j)) := by
          rw [hprefix]
          exact mul_dvd_mul (dvd_refl _) hminor
        simpa [hi, hj, mul_assoc, mul_left_comm, mul_comm] using
          dvd_mul_of_dvd_right hmul ((-1 : R) ^ (i + j : Nat))
      · have hct : c t ≠ 0 := by
          intro hzero
          apply htj
          exact c.inj' (by simpa [hj] using hzero)
        have hzeroEntry : (A.submatrix r c) i t = 0 := by
          exact hOff (r i) (c t) (by
            intro hval
            apply hct
            ext
            simpa [hi] using hval.symm)
        rw [hzeroEntry]
        simp
    · have hcolAll : ∀ t, c t ≠ 0 := by
        intro t ht
        exact hcol ⟨t, ht⟩
      have hdetZero : _root_.Matrix.det (A.submatrix r c) = 0 := by
        apply _root_.Matrix.det_eq_zero_of_row_eq_zero i
        intro t
        exact hOff (r i) (c t) (by
          intro hval
          apply hcolAll t
          ext
          simpa [hi] using hval.symm)
      rw [hdetZero]
      exact dvd_zero _
  · by_cases hcol : ∃ j, c j = 0
    · rcases hcol with ⟨j, hj⟩
      have hrowAll : ∀ t, r t ≠ 0 := by
        intro t ht
        exact hrow ⟨t, ht⟩
      have hdetZero : _root_.Matrix.det (A.submatrix r c) = 0 := by
        apply _root_.Matrix.det_eq_zero_of_column_eq_zero j
        intro t
        exact hOff (r t) (c j) (by
          intro hval
          apply hrowAll t
          ext
          simpa [hj] using hval)
      rw [hdetZero]
      exact dvd_zero _
    · have hrowAll : ∀ t, r t ≠ 0 := by
        intro t ht
        exact hrow ⟨t, ht⟩
      have hcolAll : ∀ t, c t ≠ 0 := by
        intro t ht
        exact hcol ⟨t, ht⟩
      obtain ⟨r', c', hEq⟩ := submatrix_tail_reindex_via_predAbove A r c hrowAll hcolAll
      rw [hEq, hprefix]
      let B : _root_.Matrix (Fin (k + 1)) (Fin (k + 1)) R := (lowerRight A).submatrix r' c'
      change A 0 0 * diagPrefixProduct (lowerRight A) k hk ∣ _root_.Matrix.det B
      rw [_root_.Matrix.det_succ_row_zero (A := B)]
      apply Finset.dvd_sum
      intro j hj
      have hentry : A 0 0 ∣ B 0 j := by
        by_cases hEqIdx : (r' 0).1 = (c' j).1
        · have hkHead : (r' 0).1 < Nat.min m n := by
            exact lt_min_iff.mpr ⟨(r' 0).is_lt, by simpa [hEqIdx] using (c' j).is_lt⟩
          have hdiag : A 0 0 ∣ diagEntry (lowerRight A) (r' 0).1 hkHead := by
            rw [diagEntry_lowerRight (A := A) (r' 0).1 hkHead]
            exact headDiag_dvd_diagEntry_of_diagChain hChain (r' 0).1 hkHead
          have hcEq : c' j = ⟨(r' 0).1, by simpa [hEqIdx] using (c' j).is_lt⟩ := by
            ext
            simpa [hEqIdx]
          simpa [B, diagEntry, hcEq] using hdiag
        · have hzeroEntry : B 0 j = 0 := by
            exact offDiagZero_lowerRight hOff (r' 0) (c' j) hEqIdx
          rw [hzeroEntry]
          exact dvd_zero _
      let rTail : Fin k ↪ Fin m := {
        toFun := fun u => r' u.succ
        inj' := by
          intro u v huv
          simpa using r'.inj' huv
      }
      let cTail : Fin k ↪ Fin n := {
        toFun := fun u => c' (Fin.succAbove j u)
        inj' := by
          intro u v huv
          have hjinj : Function.Injective (Fin.succAbove j) := Fin.succAbove_right_injective
          exact hjinj (c'.inj' huv)
      }
      have hcof :
          diagPrefixProduct (lowerRight A) k hk ∣
            _root_.Matrix.det (B.submatrix Fin.succ (Fin.succAbove j)) := by
        dsimp [B]
        rw [_root_.Matrix.submatrix_submatrix]
        simpa [rTail, cTail, Function.comp] using hTail rTail cTail
      have hmul :
          A 0 0 * diagPrefixProduct (lowerRight A) k hk ∣
            B 0 j * _root_.Matrix.det (B.submatrix Fin.succ (Fin.succAbove j)) := by
        exact mul_dvd_mul hentry hcof
      simpa [B, mul_assoc, mul_left_comm, mul_comm] using
        dvd_mul_of_dvd_right hmul ((-1 : R) ^ (j : Nat))

private theorem diagPrefixProduct_dvd_minor {m n k : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hOff : offDiagZero A) (hChain : diagChain A)
    (hk : k ≤ Nat.min m n) :
    ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
      diagPrefixProduct A k hk ∣ _root_.Matrix.det (A.submatrix r c) := by
  induction k generalizing m n A with
  | zero =>
      intro r c
      simpa [diagPrefixProduct_zero (A := A) hk] using
        (one_dvd (_root_.Matrix.det (A.submatrix r c)))
  | succ k ih =>
      cases m with
      | zero =>
          have : False := by simpa using hk
          exact this.elim
      | succ m =>
          cases n with
          | zero =>
              have : False := by simpa using hk
              exact this.elim
          | succ n =>
              have hkTail : k ≤ Nat.min m n := by
                refine le_min_iff.mpr ?_
                constructor
                · exact Nat.le_of_succ_le_succ (le_trans hk (Nat.min_le_left _ _))
                · exact Nat.le_of_succ_le_succ (le_trans hk (Nat.min_le_right _ _))
              by_cases hzero : A 0 0 = 0
              · have hLowerZero : lowerRight A = 0 :=
                  lowerRight_eq_zero_of_head_zero hOff hChain hzero
                have hAzero : A = 0 := by
                  ext i j
                  refine Fin.cases ?_ ?_ i
                  · refine Fin.cases ?_ ?_ j
                    · simpa using hzero
                    · intro j
                      exact hOff 0 j.succ (by simp)
                  · intro i
                    refine Fin.cases ?_ ?_ j
                    · exact hOff i.succ 0 (by simp)
                    · intro j
                      simpa [lowerRight] using congrFun (congrFun hLowerZero i) j
                have hdiagZero :
                    diagEntry A k (lt_of_lt_of_le (Nat.lt_succ_self k) hk) = 0 :=
                  diagEntry_eq_zero_of_head_zero hChain hzero k
                    (lt_of_lt_of_le (Nat.lt_succ_self k) hk)
                have hprefixZero :
                    diagPrefixProduct A (k + 1) hk = 0 := by
                  rw [diagPrefixProduct_succ A k hk]
                  simp [hdiagZero]
                intro r c
                have hdetZero : _root_.Matrix.det (A.submatrix r c) = 0 := by
                  simpa [hAzero] using
                    (_root_.Matrix.det_zero (R := R) (n := Fin (k + 1))
                      (by infer_instance : Nonempty (Fin (k + 1))))
                rw [hprefixZero, hdetZero]
              · have hTail : ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
                    diagPrefixProduct (lowerRight A) k hkTail ∣
                      _root_.Matrix.det ((lowerRight A).submatrix r c) :=
                  ih (A := lowerRight A) (offDiagZero_lowerRight hOff)
                    (diagChain_lowerRight hChain) hkTail
                exact diagPrefixProduct_dvd_minor_step (A := A) hOff hChain hzero hkTail hTail
private theorem invariantFactors_length_le_min {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) :
    (invariantFactors A).length ≤ Nat.min m n := by
  induction m generalizing n with
  | zero =>
      simp [invariantFactors]
  | succ m ih =>
      cases n with
      | zero =>
          simp [invariantFactors]
      | succ n =>
          by_cases h0 : normalize (A 0 0) = 0
          · simp [invariantFactors, h0]
          · rw [invariantFactors]
            simp [h0]
            have hlen : (invariantFactors (lowerRight A)).length ≤ Nat.min m n :=
              ih (lowerRight A)
            exact ⟨le_trans hlen (Nat.min_le_left _ _), le_trans hlen (Nat.min_le_right _ _)⟩

private theorem lt_min_of_succ_lt_min_succ {a b k : Nat}
    (hk : k + 1 < Nat.min (a + 1) (b + 1)) :
    k < Nat.min a b := by
  exact lt_min_iff.mpr
    ⟨Nat.lt_of_succ_lt_succ (Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)),
      Nat.lt_of_succ_lt_succ (Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _))⟩

private theorem diagEntry_ne_zero_of_lt_invariantFactors_length {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A) :
    ∀ k, k < (invariantFactors A).length ->
      ∀ hk : k < Nat.min m n, diagEntry A k hk ≠ 0 := by
  intro k
  induction hA generalizing k with
  | emptyRows A =>
      intro hkLen
      simp at hkLen
  | emptyCols A =>
      intro hkLen
      simp at hkLen
  | zeroLead A hzero hrow hcol hLowerZero =>
      intro hkLen
      simp [invariantFactors, hzero] at hkLen
  | pivot A hpivot hnorm hrow hcol hLower hdiv ih =>
      intro hkLen hk
      rw [invariantFactors_pivot hpivot hnorm] at hkLen
      cases k with
      | zero =>
          simpa [diagEntry] using hpivot
      | succ k =>
          have hkLen' : k < (invariantFactors (lowerRight A)).length := by
            simpa using hkLen
          have hk' : k < Nat.min _ _ := lt_min_of_succ_lt_min_succ hk
          have hne := ih k hkLen' hk'
          simpa [diagEntry_lowerRight (A := A) k hk'] using hne

private theorem diagEntry_eq_zero_of_invariantFactors_length_le {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A) :
    ∀ k, (invariantFactors A).length ≤ k ->
      ∀ hk : k < Nat.min m n, diagEntry A k hk = 0 := by
  intro k
  induction hA generalizing k with
  | emptyRows A =>
      intro hkLen hk
      simpa using hk
  | emptyCols A =>
      intro hkLen hk
      simpa using hk
  | zeroLead A hzero hrow hcol hLowerZero =>
      intro hkLen hk
      cases k with
      | zero =>
          simpa [diagEntry] using hzero
      | succ k =>
          have hk' : k < Nat.min _ _ := lt_min_of_succ_lt_min_succ hk
          rw [← diagEntry_lowerRight (A := A) k hk']
          simp [hLowerZero, diagEntry]
  | pivot A hpivot hnorm hrow hcol hLower hdiv ih =>
      intro hkLen hk
      rw [invariantFactors_pivot hpivot hnorm] at hkLen
      cases k with
      | zero =>
          cases hkLen
      | succ k =>
          have hkLen' : (invariantFactors (lowerRight A)).length ≤ k := by
            simpa using hkLen
          have hk' : k < Nat.min _ _ := lt_min_of_succ_lt_min_succ hk
          rw [← diagEntry_lowerRight (A := A) k hk']
          exact ih k hkLen' hk'
private theorem diagEntry_dvd_of_diagChain {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hChain : diagChain A) :
    ∀ i j, i ≤ j -> ∀ hi : i < Nat.min m n, ∀ hj : j < Nat.min m n,
      diagEntry A i hi ∣ diagEntry A j hj := by
  intro i j hij hi hj
  revert i j hij hi hj
  induction m generalizing n with
  | zero =>
      intro i j hij hi hj
      simpa using hi
  | succ m ih =>
      cases n with
      | zero =>
          intro i j hij hi hj
          simpa using hi
      | succ n =>
          intro i j hij hi hj
          cases i with
          | zero =>
              cases j with
              | zero =>
                  simpa [diagEntry] using dvd_rfl (A 0 0)
              | succ j =>
                  have hj' : j < Nat.min m n := lt_min_of_succ_lt_min_succ hj
                  simpa [diagEntry] using headDiag_dvd_diagEntry_of_diagChain hChain j hj'
          | succ i =>
              cases j with
              | zero =>
                  cases Nat.not_succ_le_zero _ hij
              | succ j =>
                  have hi' : i < Nat.min m n := lt_min_of_succ_lt_min_succ hi
                  have hj' : j < Nat.min m n := lt_min_of_succ_lt_min_succ hj
                  rw [← diagEntry_lowerRight (A := A) i hi', ← diagEntry_lowerRight (A := A) j hj']
                  exact ih (A := lowerRight A) (diagChain_lowerRight hChain) i j
                    (Nat.succ_le_succ_iff.mp hij) hi' hj'
private def initialEmbedding {k m : Nat} (hk : k ≤ m) : Fin k ↪ Fin m where
  toFun := fun i => ⟨i.1, Nat.lt_of_lt_of_le i.is_lt hk⟩
  inj' := by
    intro i j hij
    cases i
    cases j
    cases hij
    rfl

private theorem det_leadingMinor_eq_diagPrefixProduct {m n k : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hOff : offDiagZero A) (hk : k ≤ Nat.min m n) :
    _root_.Matrix.det
        (A.submatrix
          (initialEmbedding (Nat.le_trans hk (Nat.min_le_left _ _)))
          (initialEmbedding (Nat.le_trans hk (Nat.min_le_right _ _)))) =
      diagPrefixProduct A k hk := by
  let r : Fin k ↪ Fin m :=
    initialEmbedding (Nat.le_trans hk (Nat.min_le_left _ _))
  let c : Fin k ↪ Fin n :=
    initialEmbedding (Nat.le_trans hk (Nat.min_le_right _ _))
  have hDiag :
      A.submatrix r c =
        _root_.Matrix.diagonal (fun i : Fin k => diagEntry A i.1 (lt_of_lt_of_le i.is_lt hk)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [r, c, initialEmbedding, diagEntry]
    · rw [_root_.Matrix.diagonal_apply_ne _ hij]
      have hijVal : i.1 ≠ j.1 := by
        intro hEq
        exact hij (Fin.ext hEq)
      exact hOff (r i) (c j) (by simpa [r, c, initialEmbedding] using hijVal)
  rw [hDiag, _root_.Matrix.det_diagonal, diagPrefixProduct]

private theorem diagPrefixProduct_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hNorm : diagNormalized A) :
    ∀ k (hk : k ≤ Nat.min m n),
      normalize (diagPrefixProduct A k hk) = diagPrefixProduct A k hk
  | 0, hk => by
      simp [diagPrefixProduct_zero (A := A) hk]
  | k + 1, hk => by
      rw [diagPrefixProduct_succ A k hk, normalize.map_mul,
        diagPrefixProduct_normalized hNorm k (Nat.le_trans (Nat.le_succ k) hk),
        ← hNorm k (lt_of_lt_of_le (Nat.lt_succ_self k) hk)]

private theorem diagPrefixProduct_ne_zero_of_le_invariantFactors_length {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A) :
    ∀ k, k ≤ (invariantFactors A).length ->
      ∀ hk : k ≤ Nat.min m n, diagPrefixProduct A k hk ≠ 0
  | 0, hlen, hk => by
      simp [diagPrefixProduct_zero (A := A) hk]
  | k + 1, hlen, hk => by
      rw [diagPrefixProduct_succ A k hk]
      apply mul_ne_zero
      · exact diagPrefixProduct_ne_zero_of_le_invariantFactors_length hA k
          (Nat.le_trans (Nat.le_succ k) hlen)
          (Nat.le_trans (Nat.le_succ k) hk)
      · exact diagEntry_ne_zero_of_lt_invariantFactors_length hA k
          (Nat.lt_of_succ_le hlen)
          (lt_of_lt_of_le (Nat.lt_succ_self k) hk)

private theorem diagPrefixProduct_eq_zero_of_invariantFactors_length_lt {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A) :
    ∀ k, (invariantFactors A).length < k ->
      ∀ hk : k ≤ Nat.min m n, diagPrefixProduct A k hk = 0
  | 0, hlt, hk => by
      exact (Nat.not_lt_zero _ hlt).elim
  | k + 1, hlt, hk => by
      have hDiagZero :
          diagEntry A k (lt_of_lt_of_le (Nat.lt_succ_self k) hk) = 0 :=
        diagEntry_eq_zero_of_invariantFactors_length_le hA k
          (Nat.lt_succ_iff.mp hlt)
          (lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      rw [diagPrefixProduct_succ A k hk]
      simp [hDiagZero]

private theorem diagPrefixProduct_eq_of_two_sided_equiv {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A)
    (hB : IsSmithNormalFormFin B)
    {U : _root_.Matrix (Fin m) (Fin m) R}
    {V : _root_.Matrix (Fin n) (Fin n) R}
    (hU : NormalForms.Matrix.Certificates.Unimodular U)
    (hV : NormalForms.Matrix.Certificates.Unimodular V)
    (hEq : U * A * V = B) :
    ∀ k (hk : k ≤ Nat.min m n),
      diagPrefixProduct A k hk = diagPrefixProduct B k hk := by
  rcases isSmithNormalFormFin_toDiag hA with ⟨hAOff, hANorm, hAChain⟩
  rcases isSmithNormalFormFin_toDiag hB with ⟨hBOff, hBNorm, hBChain⟩
  intro k hk
  have hAminors :
      ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
        diagPrefixProduct A k hk ∣ _root_.Matrix.det (A.submatrix r c) :=
    diagPrefixProduct_dvd_minor (A := A) hAOff hAChain hk
  have hLeft :
      ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
        diagPrefixProduct A k hk ∣ _root_.Matrix.det ((U * A).submatrix r c) :=
    minor_dvd_of_left_mul (k := k) (U := U) (M := A) (d := diagPrefixProduct A k hk) hAminors
  have hRight :
      ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
        diagPrefixProduct A k hk ∣ _root_.Matrix.det (((U * A) * V).submatrix r c) :=
    minor_dvd_of_right_mul (k := k) (M := U * A) (N := V) (d := diagPrefixProduct A k hk) hLeft
  have hAB : diagPrefixProduct A k hk ∣ diagPrefixProduct B k hk := by
    have hMinor :
        diagPrefixProduct A k hk ∣
          _root_.Matrix.det
            (B.submatrix
              (initialEmbedding (Nat.le_trans hk (Nat.min_le_left _ _)))
              (initialEmbedding (Nat.le_trans hk (Nat.min_le_right _ _)))) := by
      rw [← hEq]
      simpa [_root_.Matrix.mul_assoc] using
        hRight
          (initialEmbedding (Nat.le_trans hk (Nat.min_le_left _ _)))
          (initialEmbedding (Nat.le_trans hk (Nat.min_le_right _ _)))
    simpa [det_leadingMinor_eq_diagPrefixProduct (A := B) hBOff hk] using hMinor
  have hEqInv : U⁻¹ * B * V⁻¹ = A := by
    calc
      U⁻¹ * B * V⁻¹ = U⁻¹ * (U * A * V) * V⁻¹ := by rw [hEq]
      _ = U⁻¹ * (U * (A * V)) * V⁻¹ := by simp [_root_.Matrix.mul_assoc]
      _ = (A * V) * V⁻¹ := by
        rw [_root_.Matrix.nonsing_inv_mul_cancel_left (A := U) (B := A * V) hU]
      _ = A := by
        rw [_root_.Matrix.mul_nonsing_inv_cancel_right (A := V) (B := A) hV]
  have hBminors :
      ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
        diagPrefixProduct B k hk ∣ _root_.Matrix.det (B.submatrix r c) :=
    diagPrefixProduct_dvd_minor (A := B) hBOff hBChain hk
  have hLeftInv :
      ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
        diagPrefixProduct B k hk ∣ _root_.Matrix.det ((U⁻¹ * B).submatrix r c) :=
    minor_dvd_of_left_mul (k := k) (U := U⁻¹) (M := B) (d := diagPrefixProduct B k hk) hBminors
  have hRightInv :
      ∀ r : Fin k ↪ Fin m, ∀ c : Fin k ↪ Fin n,
        diagPrefixProduct B k hk ∣ _root_.Matrix.det (((U⁻¹ * B) * V⁻¹).submatrix r c) :=
    minor_dvd_of_right_mul (k := k) (M := U⁻¹ * B) (N := V⁻¹)
      (d := diagPrefixProduct B k hk) hLeftInv
  have hBA : diagPrefixProduct B k hk ∣ diagPrefixProduct A k hk := by
    have hMinor :
        diagPrefixProduct B k hk ∣
          _root_.Matrix.det
            (A.submatrix
              (initialEmbedding (Nat.le_trans hk (Nat.min_le_left _ _)))
              (initialEmbedding (Nat.le_trans hk (Nat.min_le_right _ _)))) := by
      rw [← hEqInv]
      simpa [_root_.Matrix.mul_assoc] using
        hRightInv
          (initialEmbedding (Nat.le_trans hk (Nat.min_le_left _ _)))
          (initialEmbedding (Nat.le_trans hk (Nat.min_le_right _ _)))
    simpa [det_leadingMinor_eq_diagPrefixProduct (A := A) hAOff hk] using hMinor
  exact dvd_antisymm_of_normalize_eq
    (diagPrefixProduct_normalized hANorm k hk)
    (diagPrefixProduct_normalized hBNorm k hk)
    hAB hBA

private theorem invariantFactors_length_eq_of_two_sided_equiv {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A)
    (hB : IsSmithNormalFormFin B)
    {U : _root_.Matrix (Fin m) (Fin m) R}
    {V : _root_.Matrix (Fin n) (Fin n) R}
    (hU : NormalForms.Matrix.Certificates.Unimodular U)
    (hV : NormalForms.Matrix.Certificates.Unimodular V)
    (hEq : U * A * V = B) :
    (invariantFactors A).length = (invariantFactors B).length := by
  have hAB : (invariantFactors A).length ≤ (invariantFactors B).length := by
    by_contra hNot
    have hlt : (invariantFactors B).length < (invariantFactors A).length := Nat.lt_of_not_ge hNot
    have hk : (invariantFactors A).length ≤ Nat.min m n := invariantFactors_length_le_min A
    have hPrefixEq := diagPrefixProduct_eq_of_two_sided_equiv hA hB hU hV hEq
      (invariantFactors A).length hk
    have hANe := diagPrefixProduct_ne_zero_of_le_invariantFactors_length hA
      (invariantFactors A).length (le_rfl : (invariantFactors A).length ≤ (invariantFactors A).length) hk
    have hBZero := diagPrefixProduct_eq_zero_of_invariantFactors_length_lt hB
      (invariantFactors A).length hlt hk
    exact hANe (hPrefixEq.trans hBZero)
  have hBA : (invariantFactors B).length ≤ (invariantFactors A).length := by
    by_contra hNot
    have hlt : (invariantFactors A).length < (invariantFactors B).length := Nat.lt_of_not_ge hNot
    have hk : (invariantFactors B).length ≤ Nat.min m n := invariantFactors_length_le_min B
    have hPrefixEq := diagPrefixProduct_eq_of_two_sided_equiv hA hB hU hV hEq
      (invariantFactors B).length hk
    have hBNe := diagPrefixProduct_ne_zero_of_le_invariantFactors_length hB
      (invariantFactors B).length (le_rfl : (invariantFactors B).length ≤ (invariantFactors B).length) hk
    have hAZero := diagPrefixProduct_eq_zero_of_invariantFactors_length_lt hA
      (invariantFactors B).length hlt hk
    exact hBNe (hPrefixEq.symm.trans hAZero)
  exact le_antisymm hAB hBA

private theorem diagEntry_eq_of_two_sided_equiv {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A)
    (hB : IsSmithNormalFormFin B)
    {U : _root_.Matrix (Fin m) (Fin m) R}
    {V : _root_.Matrix (Fin n) (Fin n) R}
    (hU : NormalForms.Matrix.Certificates.Unimodular U)
    (hV : NormalForms.Matrix.Certificates.Unimodular V)
    (hEq : U * A * V = B) :
    ∀ k (hk : k < Nat.min m n),
      diagEntry A k hk = diagEntry B k hk := by
  have hLenEq := invariantFactors_length_eq_of_two_sided_equiv hA hB hU hV hEq
  intro k hk
  by_cases hkLen : k < (invariantFactors A).length
  · have hkSucc : k + 1 ≤ Nat.min m n := Nat.succ_le_of_lt hk
    have hkPrev : k ≤ Nat.min m n := Nat.le_trans (Nat.le_succ k) hkSucc
    have hSucc := diagPrefixProduct_eq_of_two_sided_equiv hA hB hU hV hEq (k + 1) hkSucc
    have hPrev := diagPrefixProduct_eq_of_two_sided_equiv hA hB hU hV hEq k hkPrev
    have hPrevNe := diagPrefixProduct_ne_zero_of_le_invariantFactors_length hA k
      (Nat.le_of_lt hkLen) hkPrev
    rw [diagPrefixProduct_succ A k hkSucc, diagPrefixProduct_succ B k hkSucc] at hSucc
    rw [← hPrev] at hSucc
    exact mul_left_cancel₀ hPrevNe hSucc
  · have hkLenLe : (invariantFactors A).length ≤ k := Nat.le_of_not_gt hkLen
    have hAZero : diagEntry A k hk = 0 :=
      diagEntry_eq_zero_of_invariantFactors_length_le hA k hkLenLe hk
    have hkLenLeB : (invariantFactors B).length ≤ k := by
      simpa [hLenEq] using hkLenLe
    have hBZero : diagEntry B k hk = 0 :=
      diagEntry_eq_zero_of_invariantFactors_length_le hB k hkLenLeB hk
    exact hAZero.trans hBZero.symm

theorem isSmithNormalFormFin_unique_of_two_sided_equiv {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A)
    (hB : IsSmithNormalFormFin B)
    {U : _root_.Matrix (Fin m) (Fin m) R}
    {V : _root_.Matrix (Fin n) (Fin n) R}
    (hU : NormalForms.Matrix.Certificates.Unimodular U)
    (hV : NormalForms.Matrix.Certificates.Unimodular V)
    (hEq : U * A * V = B) :
    A = B := by
  rcases isSmithNormalFormFin_toDiag hA with ⟨hAOff, _, _⟩
  rcases isSmithNormalFormFin_toDiag hB with ⟨hBOff, _, _⟩
  ext i j
  by_cases hij : i.1 = j.1
  · have hk : i.1 < Nat.min m n := by
      exact lt_min_iff.mpr ⟨i.is_lt, by simpa [hij] using j.is_lt⟩
    have hDiag := diagEntry_eq_of_two_sided_equiv hA hB hU hV hEq i.1 hk
    have hi : i = ⟨i.1, Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)⟩ := by
      ext
      rfl
    have hj : j = ⟨i.1, Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _)⟩ := by
      ext
      simpa [hij]
    have hAij : A i j = diagEntry A i.1 hk := by
      cases i with
      | mk iv hi' =>
          cases j with
          | mk jv hj' =>
              simp at hij
              subst hij
              simp [diagEntry]
    have hBij : diagEntry B i.1 hk = B i j := by
      cases i with
      | mk iv hi' =>
          cases j with
          | mk jv hj' =>
              simp at hij
              subst hij
              simp [diagEntry]
    calc
      A i j = diagEntry A i.1 hk := hAij
      _ = diagEntry B i.1 hk := hDiag
      _ = B i j := hBij
  · exact (hAOff i j hij).trans (hBOff i j hij).symm

/-- Convert the diagonal Smith specification into the recursive internal Smith predicate. -/
theorem isSmithNormalFormDiag_toFin {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormDiag A) :
    IsSmithNormalFormFin A := by
  induction m generalizing n with
  | zero =>
      exact IsSmithNormalFormFin.emptyRows A
  | succ m ih =>
      cases n with
      | zero =>
          exact IsSmithNormalFormFin.emptyCols A
      | succ n =>
          rcases hA with ⟨hOff, hNorm, hChain⟩
          by_cases hzero : A 0 0 = 0
          · refine IsSmithNormalFormFin.zeroLead A hzero ?_ ?_ ?_
            · intro j
              exact hOff 0 j.succ (by simp)
            · intro i
              exact hOff i.succ 0 (by simp)
            · exact lowerRight_eq_zero_of_head_zero hOff hChain hzero
          · refine IsSmithNormalFormFin.pivot A hzero ?_ ?_ ?_ ?_ ?_
            · have h00 : 0 < Nat.min (m + 1) (n + 1) := by simp
              simpa [diagEntry] using hNorm 0 h00
            · intro j
              exact hOff 0 j.succ (by simp)
            · intro i
              exact hOff i.succ 0 (by simp)
            · exact ih (n := n) (A := lowerRight A)
                (isSmithNormalFormDiag_lowerRight ⟨hOff, hNorm, hChain⟩)
            · intro i j
              by_cases hij : i.1 = j.1
              · have hk : j.1 < Nat.min m n := by
                  exact lt_min_iff.mpr ⟨by simpa [hij] using i.is_lt, j.is_lt⟩
                have hdiag : A 0 0 ∣ diagEntry A (j.1 + 1) (succ_lt_min_succ hk) :=
                  headDiag_dvd_diagEntry_of_diagChain hChain j.1 hk
                have hrow :
                    i.succ = ⟨j.1 + 1, Nat.succ_lt_succ (by simpa [hij] using i.is_lt)⟩ := by
                  ext
                  simp [hij]
                rw [hrow]
                simpa [diagEntry] using hdiag
              · rw [hOff i.succ j.succ (by simpa using hij)]
                exact dvd_zero (A 0 0)

/-- Internal Smith-normal-form matrices are uniquely determined by their invariant factors. -/
theorem isSmithNormalFormFin_eq_of_invariantFactors_eq {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormFin A)
    (hB : IsSmithNormalFormFin B)
    (hInv : invariantFactors A = invariantFactors B) :
    A = B := by
  induction hA with
  | emptyRows A =>
      ext i
      exact Fin.elim0 i
  | emptyCols A =>
      ext i j
      exact Fin.elim0 j
  | zeroLead A hzero hrow hcol hLowerZero =>
      cases hB with
      | zeroLead B hzero₂ hrow₂ hcol₂ hLowerZero₂ =>
          ext i j
          cases i using Fin.cases with
          | zero =>
              cases j using Fin.cases with
              | zero =>
                  exact hzero.trans hzero₂.symm
              | succ j =>
                  exact (hrow j).trans (hrow₂ j).symm
          | succ i =>
              cases j using Fin.cases with
              | zero =>
                  exact (hcol i).trans (hcol₂ i).symm
              | succ j =>
                  have hAij : A i.succ j.succ = 0 := by
                    simpa [lowerRight] using congrFun (congrFun hLowerZero i) j
                  have hBij : B i.succ j.succ = 0 := by
                    simpa [lowerRight] using congrFun (congrFun hLowerZero₂ i) j
                  exact hAij.trans hBij.symm
      | pivot B hpivot₂ hnorm₂ _ _ _ _ =>
          have hAInv : invariantFactors A = [] := invariantFactors_zeroLead hzero
          have hBInv : invariantFactors B = B 0 0 :: invariantFactors (lowerRight B) :=
            invariantFactors_pivot hpivot₂ hnorm₂
          rw [hAInv, hBInv] at hInv
          cases hInv
  | pivot A hpivot hnorm hrow hcol hLower hdiv ih =>
      cases hB with
      | zeroLead B hzero₂ _ _ _ =>
          have hAInv : invariantFactors A = A 0 0 :: invariantFactors (lowerRight A) :=
            invariantFactors_pivot hpivot hnorm
          have hBInv : invariantFactors B = [] := invariantFactors_zeroLead hzero₂
          rw [hAInv, hBInv] at hInv
          cases hInv
      | pivot B hpivot₂ hnorm₂ hrow₂ hcol₂ hLower₂ hdiv₂ =>
          have hAInv : invariantFactors A = A 0 0 :: invariantFactors (lowerRight A) :=
            invariantFactors_pivot hpivot hnorm
          have hBInv : invariantFactors B = B 0 0 :: invariantFactors (lowerRight B) :=
            invariantFactors_pivot hpivot₂ hnorm₂
          rw [hAInv, hBInv] at hInv
          have hHead : A 0 0 = B 0 0 := (List.cons.inj hInv).1
          have hTail : invariantFactors (lowerRight A) = invariantFactors (lowerRight B) :=
            (List.cons.inj hInv).2
          have hLowerEq : lowerRight A = lowerRight B := ih hLower₂ hTail
          ext i j
          cases i using Fin.cases with
          | zero =>
              cases j using Fin.cases with
              | zero =>
                  exact hHead
              | succ j =>
                  exact (hrow j).trans (hrow₂ j).symm
          | succ i =>
              cases j using Fin.cases with
              | zero =>
                  exact (hcol i).trans (hcol₂ i).symm
              | succ j =>
                  exact congrFun (congrFun hLowerEq i) j

/-- Diagonal Smith-normal-form matrices are uniquely determined by their invariant factors. -/
theorem isSmithNormalFormDiag_eq_of_invariantFactors_eq {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix (Fin m) (Fin n) R}
    (hA : IsSmithNormalFormDiag A)
    (hB : IsSmithNormalFormDiag B)
    (hInv : invariantFactors A = invariantFactors B) :
    A = B := by
  exact isSmithNormalFormFin_eq_of_invariantFactors_eq
    (isSmithNormalFormDiag_toFin hA)
    (isSmithNormalFormDiag_toFin hB)
    hInv

end Internal

theorem isSmithNormalForm_unique_of_two_sided_equiv {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix m n R}
    (hA : IsSmithNormalForm A)
    (hB : IsSmithNormalForm B)
    {U : _root_.Matrix m m R}
    {V : _root_.Matrix n n R}
    (hU : NormalForms.Matrix.Certificates.Unimodular U)
    (hV : NormalForms.Matrix.Certificates.Unimodular V)
    (hEq : U * A * V = B) :
    A = B := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  have hEqFin :
      _root_.Matrix.reindex em em U *
          _root_.Matrix.reindex em en A *
          _root_.Matrix.reindex en en V =
        _root_.Matrix.reindex em en B := by
    calc
      _root_.Matrix.reindex em em U *
          _root_.Matrix.reindex em en A *
          _root_.Matrix.reindex en en V
          = _root_.Matrix.reindex em en (U * A) *
              _root_.Matrix.reindex en en V := by
              simpa [Matrix.reindexLinearEquiv, _root_.Matrix.mul_assoc] using
                congrArg (fun X => X * _root_.Matrix.reindex en en V)
                  (Matrix.reindexLinearEquiv_mul R R em em en U A)
      _ = _root_.Matrix.reindex em en ((U * A) * V) := by
            simpa [Matrix.reindexLinearEquiv] using
              (Matrix.reindexLinearEquiv_mul R R em en en (U * A) V)
      _ = _root_.Matrix.reindex em en B := by
            simpa [_root_.Matrix.mul_assoc] using congrArg (_root_.Matrix.reindex em en) hEq
  have hUniqueFin :
      _root_.Matrix.reindex em en A =
        _root_.Matrix.reindex em en B := by
    unfold IsSmithNormalForm at hA hB
    exact Internal.isSmithNormalFormFin_unique_of_two_sided_equiv
      (Internal.isSmithNormalFormDiag_toFin hA)
      (Internal.isSmithNormalFormDiag_toFin hB)
      (unimodular_reindex em hU)
      (unimodular_reindex en hV)
      hEqFin
  ext i j
  simpa [em, en] using congrFun (congrFun hUniqueFin (em i)) (en j)

/-- Smith-normal-form matrices are uniquely determined by their invariant factors. -/
theorem isSmithNormalForm_eq_of_invariantFactors_eq {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A B : _root_.Matrix m n R}
    (hA : IsSmithNormalForm A)
    (hB : IsSmithNormalForm B)
    (hInv : smithInvariantFactors A = smithInvariantFactors B) :
    A = B := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  have hEqFin :
      _root_.Matrix.reindex em en A =
        _root_.Matrix.reindex em en B := by
    exact Internal.isSmithNormalFormDiag_eq_of_invariantFactors_eq hA hB <|
      by simpa [smithInvariantFactors, em, en] using hInv
  ext i j
  simpa [em, en] using congrFun (congrFun hEqFin (em i)) (en j)

theorem SNFResult.eq_of_invariantFactors_eq {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R}
    (result₁ result₂ : SNFResult A)
    (hInv : result₁.invariantFactors = result₂.invariantFactors) :
    result₁.S = result₂.S :=
  isSmithNormalForm_eq_of_invariantFactors_eq result₁.isSmith result₂.isSmith hInv

end NormalForms.Matrix.Smith





































