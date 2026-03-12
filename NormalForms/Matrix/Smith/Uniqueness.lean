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







