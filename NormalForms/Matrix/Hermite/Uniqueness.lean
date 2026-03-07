import NormalForms.Matrix.Hermite.Basic

/-!
# Hermite Normal Form Correctness and Uniqueness

Public correctness extraction and uniqueness for row-style Hermite normal forms.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Certificates

theorem hermiteNormalForm_isHermite {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix m n R} {result : HNFResult A}
    (_hresult : hermiteNormalForm A = some result) :
    IsHermiteNormalForm result.H := by
  exact result.isHermite


theorem hnf_lower_row_firstCol_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : IsHermiteNormalFormFin A) :
    ∀ i : Fin m, A i.succ 0 = 0 := by
  cases hA with
  | zeroCol A hzero hTail =>
      intro i
      exact hzero i.succ
  | pivot A hpivot hnorm hbelow hLower hreduced =>
      exact hbelow


theorem hnf_rowAbove_reduced_at_pivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} (hA : IsHermiteNormalFormFin A) :
    ∀ {i j : Fin m} (hij : i < j) {p : Fin n},
      firstNonzero? (fun k : Fin n => A j k) = some p ->
      A i p = A i p % A j p := by
  induction hA with
  | emptyRows A =>
      intro i
      exact Fin.elim0 i
  | emptyCols A =>
      intro i j hij p
      exact Fin.elim0 p
  | zeroCol A hzero hTail ih =>
      intro i j hij p hrow
      cases p using Fin.cases with
      | zero =>
          have hj0 := hzero j
          simp [firstNonzero?, hj0] at hrow
      | succ p =>
          have hj0 := hzero j
          rw [firstNonzero?, hj0] at hrow
          cases htail : firstNonzero? (fun k : Fin _ => A j k.succ) with
          | none =>
              simp [htail] at hrow
          | some q =>
              have hqp : q = p := by
                simpa [htail] using hrow
              simpa [hqp, tailCols] using ih hij htail
  | pivot A hpivot hnorm hbelow hLower hreduced ih =>
      intro i j hij p hrow
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              exact False.elim (lt_irrefl _ hij)
          | succ j =>
              cases p using Fin.cases with
              | zero =>
                  have hj0 := hbelow j
                  simp [firstNonzero?, hj0] at hrow
              | succ p =>
                  have hj0 := hbelow j
                  rw [firstNonzero?, hj0] at hrow
                  cases htail : firstNonzero? (fun k : Fin _ => A j.succ k.succ) with
                  | none =>
                      simp [htail] at hrow
                  | some q =>
                      have hqp : q = p := by
                        simpa [htail] using hrow
                      simpa [htail, hqp] using hreduced j
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exact False.elim (Nat.not_lt_zero _ hij)
          | succ j =>
              have hij' : i < j := Fin.succ_lt_succ_iff.mp hij
              cases p using Fin.cases with
              | zero =>
                  have hj0 := hbelow j
                  simp [firstNonzero?, hj0] at hrow
              | succ p =>
                  have hj0 := hbelow j
                  rw [firstNonzero?, hj0] at hrow
                  cases htail : firstNonzero? (fun k : Fin _ => A j.succ k.succ) with
                  | none =>
                      simp [htail] at hrow
                  | some q =>
                      have hqp : q = p := by
                        simpa [htail] using hrow
                      simpa [hqp, lowerRight] using ih hij' htail


private theorem lowerLeft_zero_of_mul_eq_pivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {U : _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    {A B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hpivot : A 0 0 ≠ 0)
    (hbelowA : ∀ i : Fin m, A i.succ 0 = 0)
    (hbelowB : ∀ i : Fin m, B i.succ 0 = 0)
    (hEq : U * A = B) :
    ∀ i : Fin m, U i.succ 0 = 0 := by
  intro i
  have hEntry := congrFun (congrFun hEq i.succ) 0
  rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ, hbelowB i] at hEntry
  have hMul : U i.succ 0 * A 0 0 = 0 := by
    simpa [hbelowA] using hEntry
  exact (mul_eq_zero.mp hMul).resolve_right hpivot


private theorem lowerRight_mul_of_lowerLeftZero {m n : Nat} {R : Type _}
    [CommRing R]
    {U : _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hU0 : ∀ i : Fin m, U i.succ 0 = 0) :
    lowerRight (U * A) = lowerRight U * lowerRight A := by
  ext i j
  rw [lowerRight, _root_.Matrix.mul_apply, _root_.Matrix.mul_apply, Fin.sum_univ_succ]
  simp [lowerRight, hU0]


private theorem lowerRight_unimodular_of_lowerLeftZero {m : Nat} {R : Type _}
    [CommRing R]
    {U : _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hU : Unimodular U)
    (hU0 : ∀ i : Fin m, U i.succ 0 = 0) :
    Unimodular (lowerRight U) := by
  have hmul : lowerRight U * lowerRight U⁻¹ = (1 : _root_.Matrix (Fin m) (Fin m) R) := by
    calc
      lowerRight U * lowerRight U⁻¹ = lowerRight (U * U⁻¹) := by
        symm
        exact lowerRight_mul_of_lowerLeftZero (A := U⁻¹) hU0
      _ = lowerRight (1 : _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R) := by
        simpa using congrArg lowerRight (_root_.Matrix.mul_nonsing_inv U hU)
      _ = 1 := by
        ext i j
        by_cases h : i = j
        · subst h
          simp [lowerRight]
        · simp [lowerRight, h]
  simpa [Unimodular] using
    (_root_.Matrix.isUnit_det_of_right_inverse
      (A := lowerRight U)
      (B := lowerRight U⁻¹)
      hmul)


private theorem topRow_eq_of_eq_add_lowerRows {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A B : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (hA : IsHermiteNormalFormFin A)
    (hB : IsHermiteNormalFormFin B)
    (hLowerRows : ∀ i : Fin m, A i.succ = B i.succ)
    (c : Fin m → R)
    (hcomb : ∀ j : Fin (n + 1),
      B 0 j = A 0 j + ∑ i : Fin m, c i * A i.succ j) :
    A 0 = B 0 := by
  classical
  let active : Fin m → Prop := fun i =>
    c i ≠ 0 ∧ (firstNonzero? (fun j : Fin n => A i.succ j.succ)).isSome
  let S : Finset (Fin m) := Finset.univ.filter active
  have hEmpty : S = ∅ := by
    by_contra hS
    have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    let i0 : Fin m := S.min' hSnonempty
    have hi0mem : i0 ∈ S := Finset.min'_mem S hSnonempty
    have hi0active : active i0 := by
      simpa [S] using hi0mem
    have hi0c : c i0 ≠ 0 := hi0active.1
    rcases Option.isSome_iff_exists.mp hi0active.2 with ⟨p, hp⟩
    have hi0col0 : A i0.succ 0 = 0 := hnf_lower_row_firstCol_zero hA i0
    have hi0col0B : B i0.succ 0 = 0 := by
      simpa [hLowerRows i0] using hi0col0
    have hpFullA : firstNonzero? (fun j : Fin (n + 1) => A i0.succ j) = some p.succ := by
      rw [firstNonzero?, hi0col0]
      simpa [hp]
    have hpFullB : firstNonzero? (fun j : Fin (n + 1) => B i0.succ j) = some p.succ := by
      rw [firstNonzero?, hi0col0B]
      have hpB : firstNonzero? (fun j : Fin n => B i0.succ j.succ) = some p := by
        simpa [hLowerRows i0] using hp
      simpa [hpB]
    have hsum :
        ∑ i : Fin m, c i * A i.succ p.succ = c i0 * A i0.succ p.succ := by
      refine Finset.sum_eq_single i0 ?_ ?_
      · intro j _ hjneq
        by_cases hjmem : j ∈ S
        · have hmin : i0 ≤ j := Finset.min'_le S j hjmem
          have hlt : i0 < j := lt_of_le_of_ne hmin (Ne.symm hjneq)
          have hrowzero : A j.succ p.succ = 0 := by
            exact hnf_rowBelow_zero_at_pivot hA
              (i := i0.succ)
              (j := j.succ)
              (p := p.succ)
              (show i0.succ < j.succ from Fin.succ_lt_succ_iff.mpr hlt)
              hpFullA
          simp [hrowzero]
        · have hjnotactive : ¬ active j := by
            simpa [S] using hjmem
          by_cases hcj : c j = 0
          · simp [hcj]
          · have hnotSome :
              ¬ (firstNonzero? (fun k : Fin n => A j.succ k.succ)).isSome := by
              intro hsome
              exact hjnotactive ⟨hcj, hsome⟩
            have hnone : firstNonzero? (fun k : Fin n => A j.succ k.succ) = none :=
              Option.not_isSome_iff_eq_none.mp hnotSome
            have hrowzero : A j.succ p.succ = 0 := by
              exact firstNonzero?_eq_none (fun k : Fin n => A j.succ k.succ) hnone p
            simp [hrowzero]
      · intro hi0notmem
        exact False.elim (hi0notmem (by simp))
    have hEqp : B 0 p.succ = A 0 p.succ + c i0 * A i0.succ p.succ := by
      simpa [hsum] using hcomb p.succ
    have hAred : A 0 p.succ = A 0 p.succ % A i0.succ p.succ := by
      exact hnf_rowAbove_reduced_at_pivot hA (i := 0) (j := i0.succ) (by simp) hpFullA
    have hBred : B 0 p.succ = B 0 p.succ % A i0.succ p.succ := by
      simpa [hLowerRows i0] using
        (hnf_rowAbove_reduced_at_pivot hB (i := 0) (j := i0.succ) (by simp) hpFullB)
    have hdiv : A i0.succ p.succ ∣ B 0 p.succ - A 0 p.succ := by
      refine ⟨c i0, ?_⟩
      rw [hEqp, add_sub_cancel_left, mul_comm]
    have hsame : A 0 p.succ = B 0 p.succ := by
      let hCanon : CanonicalMod R := inferInstance
      exact hCanon.reduced_eq_of_dvd_sub hAred hBred hdiv
    have htermzero : c i0 * A i0.succ p.succ = 0 := by
      have htmp : A 0 p.succ + c i0 * A i0.succ p.succ = A 0 p.succ := by
        simpa [hsame] using hEqp.symm
      have : A 0 p.succ + c i0 * A i0.succ p.succ = A 0 p.succ + 0 := by
        simpa using htmp
      exact add_left_cancel this
    have hpnz : A i0.succ p.succ ≠ 0 := by
      exact firstNonzero?_some_ne_zero (fun j : Fin n => A i0.succ j.succ) hp
    have : c i0 = 0 := (mul_eq_zero.mp htermzero).resolve_right hpnz
    exact hi0c this
  have hNoActive : ∀ i : Fin m, ¬ active i := by
    intro i hactive
    have : i ∈ S := by
      simpa [S] using hactive
    simpa [hEmpty] using this
  ext j
  have hsumzero : ∑ i : Fin m, c i * A i.succ j = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    by_cases hci : c i = 0
    · simp [hci]
    · have hnone : firstNonzero? (fun k : Fin n => A i.succ k.succ) = none := by
        have hnotSome :
            ¬ (firstNonzero? (fun k : Fin n => A i.succ k.succ)).isSome := by
          intro hsome
          exact hNoActive i ⟨hci, hsome⟩
        exact Option.not_isSome_iff_eq_none.mp hnotSome
      cases j using Fin.cases with
      | zero =>
          simp [hci, hnf_lower_row_firstCol_zero hA i]
      | succ j =>
          have hrowzero : A i.succ j.succ = 0 := by
            exact firstNonzero?_eq_none (fun k : Fin n => A i.succ k.succ) hnone j
          simp [hci, hrowzero]
  have hEqj := hcomb j
  rw [hsumzero, add_zero] at hEqj
  exact hEqj.symm


theorem isHermiteNormalFormFin_unique_of_left_equiv {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R] :
    ∀ {H₁ : _root_.Matrix (Fin m) (Fin n) R},
      IsHermiteNormalFormFin H₁ ->
      ∀ {H₂ : _root_.Matrix (Fin m) (Fin n) R},
        IsHermiteNormalFormFin H₂ ->
        ∀ {U : _root_.Matrix (Fin m) (Fin m) R},
          Unimodular U -> U * H₁ = H₂ -> H₁ = H₂ := by
  intro H₁ hH₁
  induction hH₁ with
  | emptyRows A =>
      intro H₂ hH₂ U hU hEq
      ext i
      exact Fin.elim0 i
  | emptyCols A =>
      intro H₂ hH₂ U hU hEq
      ext i j
      exact Fin.elim0 j
  | zeroCol A hzero hTail ih =>
      intro H₂ hH₂ U hU hEq
      cases hH₂ with
      | zeroCol B hzero₂ hTail₂ =>
          ext i j
          cases j using Fin.cases with
          | zero =>
              exact (hzero i).trans (hzero₂ i).symm
          | succ j =>
              have hTailEq :
                  tailCols A = tailCols H₂ := by
                apply ih hTail₂ hU
                calc
                  U * tailCols A = tailCols (U * A) := by
                    symm
                    simpa using tailCols_mul U A
                  _ = tailCols H₂ := by simpa [hEq]
              exact congrFun (congrFun hTailEq i) j
      | pivot B hpivot₂ hnorm₂ hbelow₂ hLower₂ hreduced₂ =>
          have hzeroMul : ∀ i, (U * A) i 0 = 0 := firstCol_zero_mul U A hzero
          have : H₂ 0 0 = 0 := by
            simpa [hEq] using hzeroMul 0
          exact False.elim (hpivot₂ this)
  | pivot A hpivot hnorm hbelow hLower hreduced ih =>
      intro H₂ hH₂ U hU hEq
      cases hH₂ with
      | zeroCol H₂ hzero₂ hTail₂ =>
          have hInvEq : U⁻¹ * H₂ = A := by
            calc
              U⁻¹ * H₂ = U⁻¹ * (U * A) := by rw [hEq]
              _ = (U⁻¹ * U) * A := by rw [_root_.Matrix.mul_assoc]
              _ = A := by
                rw [_root_.Matrix.nonsing_inv_mul _ hU]
                simpa using (_root_.Matrix.one_mul A)
          have hzeroMul : ∀ i, (U⁻¹ * H₂) i 0 = 0 := firstCol_zero_mul U⁻¹ H₂ hzero₂
          have : A 0 0 = 0 := by
            simpa [hInvEq] using hzeroMul 0
          exact False.elim (hpivot this)
      | pivot H₂ hpivot₂ hnorm₂ hbelow₂ hLower₂ hreduced₂ =>
          have hA_hnf : IsHermiteNormalFormFin A :=
            .pivot A hpivot hnorm hbelow hLower hreduced
          have hH₂_hnf : IsHermiteNormalFormFin H₂ :=
            .pivot H₂ hpivot₂ hnorm₂ hbelow₂ hLower₂ hreduced₂
          have hU0 := lowerLeft_zero_of_mul_eq_pivot hpivot hbelow hbelow₂ hEq
          have hInvEq : U⁻¹ * H₂ = A := by
            calc
              U⁻¹ * H₂ = U⁻¹ * (U * A) := by rw [hEq]
              _ = (U⁻¹ * U) * A := by rw [_root_.Matrix.mul_assoc]
              _ = A := by
                rw [_root_.Matrix.nonsing_inv_mul _ hU]
                simpa using (_root_.Matrix.one_mul A)
          have hInv0 := lowerLeft_zero_of_mul_eq_pivot hpivot₂ hbelow₂ hbelow hInvEq
          have hLowerMul : lowerRight U * lowerRight A = lowerRight H₂ := by
            simpa [hEq] using (lowerRight_mul_of_lowerLeftZero (A := A) hU0).symm
          have hLowerUnimod : Unimodular (lowerRight U) :=
            lowerRight_unimodular_of_lowerLeftZero hU hU0
          have hLowerEq : lowerRight A = lowerRight H₂ :=
            ih hLower₂ hLowerUnimod hLowerMul
          have hU00Mul : U 0 0 * U⁻¹ 0 0 = 1 := by
            have hMul := congrFun (congrFun (_root_.Matrix.mul_nonsing_inv U hU) 0) 0
            rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ] at hMul
            simpa [hInv0] using hMul
          have hInvU00Mul : U⁻¹ 0 0 * U 0 0 = 1 := by
            have hMul := congrFun (congrFun (_root_.Matrix.nonsing_inv_mul U hU) 0) 0
            rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ] at hMul
            simpa [hU0] using hMul
          have hU00Unit : IsUnit (U 0 0) := by
            exact ⟨⟨U 0 0, U⁻¹ 0 0, hU00Mul, hInvU00Mul⟩, rfl⟩
          have hTopLeft : H₂ 0 0 = U 0 0 * A 0 0 := by
            have hEntry := congrFun (congrFun hEq 0) 0
            rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ] at hEntry
            simpa [hbelow] using hEntry.symm
          have hAssoc : Associated (H₂ 0 0) (A 0 0) := by
            rw [hTopLeft]
            exact associated_unit_mul_left (A 0 0) (U 0 0) hU00Unit
          have h00 : A 0 0 = H₂ 0 0 := by
            exact hAssoc.symm.eq_of_normalized hnorm.symm hnorm₂.symm
          have hU00One : U 0 0 = 1 := by
            have hMulEq : U 0 0 * A 0 0 = A 0 0 := by
              simpa [h00] using hTopLeft.symm
            have hZero : (U 0 0 - 1) * A 0 0 = 0 := by
              rw [sub_mul, one_mul, hMulEq, sub_self]
            have : U 0 0 - 1 = 0 := (mul_eq_zero.mp hZero).resolve_right hpivot
            exact sub_eq_zero.mp this
          have hLowerRows : ∀ i : Fin _, A i.succ = H₂ i.succ := by
            intro i
            ext j
            cases j using Fin.cases with
            | zero =>
                exact (hbelow i).trans (hbelow₂ i).symm
            | succ j =>
                exact congrFun (congrFun hLowerEq i) j
          have hComb :
              ∀ j : Fin _,
                H₂ 0 j = A 0 j + ∑ i : Fin _ , U 0 i.succ * A i.succ j := by
            intro j
            have hEntry := congrFun (congrFun hEq 0) j
            rw [_root_.Matrix.mul_apply, Fin.sum_univ_succ] at hEntry
            simpa [hU00One, add_comm, add_left_comm, add_assoc] using hEntry.symm
          have hTopRow : A 0 = H₂ 0 :=
            topRow_eq_of_eq_add_lowerRows hA_hnf hH₂_hnf hLowerRows
              (fun i => U 0 i.succ) hComb
          ext i j
          cases i using Fin.cases with
          | zero =>
              exact congrFun hTopRow j
          | succ i =>
              cases j using Fin.cases with
              | zero =>
                  exact (hbelow i).trans (hbelow₂ i).symm
              | succ j =>
                  exact congrFun (congrFun hLowerEq i) j


theorem isHermiteNormalForm_unique_of_left_equiv {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {H₁ H₂ : _root_.Matrix m n R}
    (hH₁ : IsHermiteNormalForm H₁)
    (hH₂ : IsHermiteNormalForm H₂)
    {U : _root_.Matrix m m R}
    (hU : Unimodular U)
    (hEq : U * H₁ = H₂) :
    H₁ = H₂ := by
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  have hEqFin :
      _root_.Matrix.reindex em em U *
          _root_.Matrix.reindex em en H₁ =
        _root_.Matrix.reindex em en H₂ := by
    simpa [Matrix.reindexLinearEquiv] using
      (Matrix.reindexLinearEquiv_mul R R em em en U H₁).trans <|
        by simpa [Matrix.reindexLinearEquiv] using congrArg (_root_.Matrix.reindex em en) hEq
  have hUniqueFin :
      _root_.Matrix.reindex em en H₁ =
        _root_.Matrix.reindex em en H₂ :=
    isHermiteNormalFormFin_unique_of_left_equiv hH₁ hH₂
      (unimodular_reindex em hU) hEqFin
  ext i j
  simpa [em, en] using congrFun (congrFun hUniqueFin (em i)) (en j)

end NormalForms.Matrix.Hermite
