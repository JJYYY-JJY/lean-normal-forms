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
















