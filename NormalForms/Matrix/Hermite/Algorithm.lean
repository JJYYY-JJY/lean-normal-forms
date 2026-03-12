import NormalForms.Matrix.Hermite.Bezout

/-!
# Hermite Normal Form Algorithm

Internal recursive Hermite kernel together with the local transport lemmas it uses.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates

@[simp] theorem lowerRight_applyRowOperation_addToTop {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 1))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i : Fin m) (c : R) :
    lowerRight (applyRowOperation A (.add i.succ 0 c)) = lowerRight A := by
  ext r s
  simp [lowerRight, applyRowOperation]


@[simp] theorem applyRowOperation_addToTop_succ {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 1))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (i j : Fin m) (c : R) :
    applyRowOperation A (.add i.succ 0 c) j.succ = A j.succ := by
  ext s
  simp [applyRowOperation]


theorem hnf_rowBelow_zero_at_pivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R} (hA : IsHermiteNormalFormFin A) :
    ∀ {i j : Fin m} (hij : i < j) {p : Fin n},
      firstNonzero? (fun k : Fin n => A i k) = some p -> A j p = 0 := by
  induction hA with
  | emptyRows A =>
      intro i
      exact Fin.elim0 i
  | emptyCols A =>
      intro i j hij p
      exact Fin.elim0 p
  | zeroCol A hzero hTail ih =>
      intro i j hij p hsome
      cases p using Fin.cases with
      | zero =>
          have h0i := hzero i
          simp [firstNonzero?, h0i] at hsome
      | succ p =>
          have h0i := hzero i
          rw [firstNonzero?, h0i] at hsome
          cases htaili : firstNonzero? (fun k : Fin _ => A i k.succ) with
          | none =>
              simp [htaili] at hsome
          | some q =>
              simp [htaili] at hsome
              subst hsome
              exact ih hij htaili
  | pivot A hpivot hnorm hbelow hLower hreduced ih =>
      intro i j hij p hsome
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero =>
              exact False.elim (lt_irrefl _ hij)
          | succ j =>
              have hp : 0 = p := by
                simpa [firstNonzero?, hpivot] using hsome
              subst hp
              exact hbelow j
      | succ i =>
          cases j using Fin.cases with
          | zero =>
              exact False.elim (Nat.not_lt_zero _ hij)
          | succ j =>
              have hij' : i < j := Fin.succ_lt_succ_iff.mp hij
              cases p using Fin.cases with
              | zero =>
                  have h0i := hbelow i
                  simp [firstNonzero?, h0i] at hsome
              | succ p =>
                  have h0i := hbelow i
                  rw [firstNonzero?, h0i] at hsome
                  cases htaili : firstNonzero? (fun k : Fin _ => A i.succ k.succ) with
                  | none =>
                      simp [htaili] at hsome
                  | some q =>
                      simp [htaili] at hsome
                      subst hsome
                      exact ih hij' htaili


@[simp] theorem applyRowOperation_swap_succ_one_top {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 2))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin (m + 1)) :
    applyRowOperation A (.swap i.succ (1 : Fin (m + 2))) 0 = A 0 := by
  ext j
  have h0i : ¬ (0 : Fin (m + 2)) = i.succ := by
    intro hEq
    exact Fin.succ_ne_zero i hEq.symm
  have h01 : (0 : Fin (m + 2)) ≠ (1 : Fin (m + 2)) := by simp
  simp [applyRowOperation, h0i, h01]


@[simp] theorem applyRowOperation_swap_succ_one_rowOne {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 2))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin (m + 1)) :
    applyRowOperation A (.swap i.succ (1 : Fin (m + 2))) 1 = A i.succ := by
  cases i using Fin.cases with
  | zero =>
      ext j
      simp [applyRowOperation]
  | succ i =>
      ext j
      have hne : (1 : Fin (m + 2)) ≠ i.succ.succ := by
        intro hEq
        have hval : (1 : Nat) = i.1.succ.succ := by
          simpa using congrArg Fin.val hEq
        simp at hval
      simp [applyRowOperation, hne]


@[simp] theorem applyRowOperation_swap_succ_one_target {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 2))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i : Fin (m + 1)) :
    applyRowOperation A (.swap i.succ (1 : Fin (m + 2))) i.succ = A 1 := by
  ext j
  simp [applyRowOperation]


@[simp] theorem applyRowOperation_swap_succ_one_other {m n : Nat} {R : Type _}
    [DecidableEq (Fin (m + 2))] [Add R] [Mul R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin n) R) (i j : Fin (m + 1))
    (hj0 : j ≠ 0) (hji : j ≠ i) :
    applyRowOperation A (.swap i.succ (1 : Fin (m + 2))) j.succ = A j.succ := by
  ext s
  have hjeq1 : (j.succ : Fin (m + 2)) ≠ 1 := by
    intro h
    apply hj0
    apply Fin.ext
    exact Nat.succ.inj <| by simpa using congrArg Fin.val h
  have hjeqi : j.succ ≠ i.succ := by
    intro h
    apply hji
    apply Fin.ext
    exact Nat.succ.inj <| by simpa using congrArg Fin.val h
  simp [applyRowOperation, hjeqi, hjeq1]


private theorem zeroHermite {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] :
    IsHermiteNormalFormFin (0 : _root_.Matrix (Fin m) (Fin n) R) := by
  induction n generalizing m with
  | zero =>
      exact IsHermiteNormalFormFin.emptyCols _
  | succ n ih =>
      cases m with
      | zero =>
          exact IsHermiteNormalFormFin.emptyRows _
      | succ m =>
          refine IsHermiteNormalFormFin.zeroCol _ ?_ ?_
          · intro i
            simp
          · simpa [tailCols] using (ih (m := m + 1))


namespace Internal

structure FinHNFResult {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) where
  U : _root_.Matrix (Fin m) (Fin m) R
  H : _root_.Matrix (Fin m) (Fin n) R
  left_mul : U * A = H
  unimodular : Unimodular U
  isHermite : IsHermiteNormalFormFin H


def clearFirstColumnStep {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) : LeftTransform A :=
  if hzero : t.B i.succ 0 = 0 then
    t
  else
    let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
    let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
    tBez.trans
      (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
        (normUnit (tBez.B 0 0)).isUnit)


def clearFirstColumnLoop {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R} :
    (k : Nat) -> k ≤ m + 1 -> LeftTransform A -> LeftTransform A
  | 0, _, t => t
  | k + 1, hk, t =>
      let t' := clearFirstColumnLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      clearFirstColumnStep i t'


def topReductionCoeff {m n : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R) (i : Fin (m + 1)) (j : Fin n) : R :=
  -(A 0 j.succ / A i.succ j.succ)


def reduceTopRowStep {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) : LeftTransform A :=
  match hrow : firstNonzero? (fun j : Fin n => t.B i.succ j.succ) with
  | none => t
  | some j =>
      t.trans <|
        LeftTransform.add t.B i.succ 0 (topReductionCoeff t.B i j) (by simp)


def reduceTopRowLoop {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R} :
    (k : Nat) -> k ≤ m + 1 -> LeftTransform A -> LeftTransform A
  | 0, _, t => t
  | k + 1, hk, t =>
      let t' := reduceTopRowLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      reduceTopRowStep i t'


theorem applyRowOperation_reduceTop_pivot {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R)
    (i : Fin (m + 1)) (j : Fin n) :
    applyRowOperation A (.add i.succ 0 (topReductionCoeff A i j)) 0 j.succ =
      A 0 j.succ % A i.succ j.succ := by
  simpa [applyRowOperation, topReductionCoeff, EuclideanDomain.mod_eq_sub_mul_div, sub_eq_add_neg,
    mul_comm, mul_left_comm, mul_assoc]


theorem clearFirstColumnStep_topLeft_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) (htop : t.B 0 0 ≠ 0) :
    (clearFirstColumnStep i t).B 0 0 ≠ 0 := by
  by_cases hzero : t.B i.succ 0 = 0
  · simp [clearFirstColumnStep, hzero, htop]
  · let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
    let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
    let tNorm := tBez.trans
      (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
        (normUnit (tBez.B 0 0)).isUnit)
    have htop' : tSwap.B 0 0 = t.B 0 0 := by
      simp [tSwap, LeftTransform.swap, LeftTransform.trans]
    have hrow' : tSwap.B 1 0 = t.B i.succ 0 := by
      simp [tSwap, LeftTransform.swap, LeftTransform.trans]
    have hdet :
        tBez.B 0 0 =
          EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0) := by
      calc
        tBez.B 0 0 = EuclideanDomain.gcd (tSwap.B 0 0) (tSwap.B 1 0) := by
          simpa [tBez, LeftTransform.topBezout, LeftTransform.trans] using
            topBezoutMatrix_mul_topLeft (m := m) (n := n) (A := tSwap.B)
        _ = EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0) := by
          rw [htop', hrow']
    have hnormTop :
        tNorm.B 0 0 = normalize (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0)) := by
      calc
        tNorm.B 0 0 = normalize (tBez.B 0 0) := by
          simp [tNorm, LeftTransform.unitSmul, LeftTransform.trans, applyRowOperation,
            normalize_apply, mul_comm]
        _ = normalize (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0)) := by
          rw [hdet]
    have hgcdNe : EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0) ≠ 0 := by
      intro hg
      exact htop ((EuclideanDomain.gcd_eq_zero_iff.mp hg).1)
    have hclear : clearFirstColumnStep i t = tNorm := by
      simp [clearFirstColumnStep, hzero, tNorm, tBez, tSwap]
    rw [hclear, hnormTop]
    exact fun hg => hgcdNe (normalize_eq_zero.mp hg)


theorem clearFirstColumnStep_topLeft_eq_normalize_gcd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) (hentry : t.B i.succ 0 ≠ 0) :
    (clearFirstColumnStep i t).B 0 0 =
      normalize (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0)) := by
  let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
  let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
  let tNorm := tBez.trans
    (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
      (normUnit (tBez.B 0 0)).isUnit)
  have htop' : tSwap.B 0 0 = t.B 0 0 := by
    simp [tSwap, LeftTransform.swap, LeftTransform.trans]
  have hrow' : tSwap.B 1 0 = t.B i.succ 0 := by
    simp [tSwap, LeftTransform.swap, LeftTransform.trans]
  have hdet :
      tBez.B 0 0 = EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0) := by
    calc
      tBez.B 0 0 = EuclideanDomain.gcd (tSwap.B 0 0) (tSwap.B 1 0) := by
        simpa [tBez, LeftTransform.topBezout, LeftTransform.trans] using
          topBezoutMatrix_mul_topLeft (m := m) (n := n) (A := tSwap.B)
      _ = EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0) := by
        rw [htop', hrow']
  have hnormTop :
      tNorm.B 0 0 = normalize (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0)) := by
    calc
      tNorm.B 0 0 = normalize (tBez.B 0 0) := by
        simp [tNorm, LeftTransform.unitSmul, LeftTransform.trans, applyRowOperation,
          normalize_apply, mul_comm]
      _ = normalize (EuclideanDomain.gcd (t.B 0 0) (t.B i.succ 0)) := by
        rw [hdet]
  have hclear : clearFirstColumnStep i t = tNorm := by
    simp [clearFirstColumnStep, hentry, tNorm, tBez, tSwap]
  rw [hclear, hnormTop]


theorem clearFirstColumnStep_topLeft_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A)
    (hnorm : t.B 0 0 = normalize (t.B 0 0)) :
    (clearFirstColumnStep i t).B 0 0 = normalize ((clearFirstColumnStep i t).B 0 0) := by
  by_cases hzero : t.B i.succ 0 = 0
  · simpa [clearFirstColumnStep, hzero] using hnorm
  · let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
    let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
    let tNorm := tBez.trans
      (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
        (normUnit (tBez.B 0 0)).isUnit)
    have hnormTop : tNorm.B 0 0 = normalize (tBez.B 0 0) := by
      simp [tNorm, LeftTransform.unitSmul, LeftTransform.trans, applyRowOperation,
        normalize_apply, mul_comm]
    have hclear : clearFirstColumnStep i t = tNorm := by
      simp [clearFirstColumnStep, hzero, tNorm, tBez, tSwap]
    rw [hclear, hnormTop]
    simpa using (normalize_idem (tBez.B 0 0)).symm


theorem clearFirstColumnStep_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A)
    (hprefix : ∀ j : Fin (m + 1), j.1 < i.1 -> t.B j.succ 0 = 0) :
    ∀ j : Fin (m + 1), j.1 < i.1.succ -> (clearFirstColumnStep i t).B j.succ 0 = 0 := by
  intro j hj
  by_cases hzero : t.B i.succ 0 = 0
  · have hj' : j.1 < i.1 ∨ j.1 = i.1 := by
      exact Nat.lt_succ_iff_lt_or_eq.mp hj
    rcases hj' with hj' | hEq
    · simpa [clearFirstColumnStep, hzero] using hprefix j hj'
    · have : j = i := Fin.ext hEq
      subst this
      simpa [clearFirstColumnStep, hzero]
  · let tSwap := t.trans (LeftTransform.swap t.B i.succ (1 : Fin (m + 2)))
    let tBez := tSwap.trans (LeftTransform.topBezout tSwap.B)
    let tNorm := tBez.trans
      (LeftTransform.unitSmul tBez.B 0 (normUnit (tBez.B 0 0) : R)
        (normUnit (tBez.B 0 0)).isUnit)
    have hbelowEq (r : Fin (m + 1)) : tNorm.B r.succ 0 = tBez.B r.succ 0 := by
      simp [tNorm, LeftTransform.unitSmul, LeftTransform.trans, applyRowOperation]
    have hclear : clearFirstColumnStep i t = tNorm := by
      simp [clearFirstColumnStep, hzero, tNorm, tBez, tSwap]
    have hrowOneZero : tBez.B 1 0 = 0 := by
      simpa [tBez, tSwap, LeftTransform.topBezout, LeftTransform.trans] using
        topBezoutMatrix_mul_rowOneFirstCol (m := m) (n := n) (A := tSwap.B)
    have hj' : j.1 < i.1 ∨ j.1 = i.1 := by
      exact Nat.lt_succ_iff_lt_or_eq.mp hj
    rcases hj' with hj' | hEq
    · cases j using Fin.cases with
      | zero =>
          calc
            (clearFirstColumnStep i t).B 1 0 = tNorm.B 1 0 := by simpa [hclear]
            _ = tBez.B 1 0 := hbelowEq 0
            _ = 0 := hrowOneZero
      | succ j =>
          have hswapEq : tSwap.B j.succ.succ 0 = t.B j.succ.succ 0 := by
            simpa [tSwap, LeftTransform.swap, LeftTransform.trans] using
              congrFun
                (applyRowOperation_swap_succ_one_other t.B i j.succ (by simp)
                  (ne_of_lt hj')) 0
          have hswapZero : tSwap.B j.succ.succ 0 = 0 := by
            rw [hswapEq]
            exact hprefix j.succ hj'
          have hbezoutZero : tBez.B j.succ.succ 0 = 0 := by
            simpa [tBez, tSwap, LeftTransform.topBezout, LeftTransform.trans] using
              (Bezout_preserves_zeros (m := m) (n := n) (a := tSwap.B 0 0) (b := tSwap.B 1 0)
                (A := tSwap.B) j hswapZero)
          calc
            (clearFirstColumnStep i t).B j.succ.succ 0 = tNorm.B j.succ.succ 0 := by
              simpa [hclear]
            _ = tBez.B j.succ.succ 0 := hbelowEq j.succ
            _ = 0 := hbezoutZero
    · have : j = i := Fin.ext hEq
      subst j
      cases i using Fin.cases with
      | zero =>
          calc
            (clearFirstColumnStep 0 t).B 1 0 = tNorm.B 1 0 := by simpa [hclear]
            _ = tBez.B 1 0 := hbelowEq 0
            _ = 0 := hrowOneZero
      | succ i =>
          have hrowOneBefore : t.B 1 0 = 0 := by
            exact hprefix 0 (by simpa using i.succ.is_lt)
          have hswapEq : tSwap.B i.succ.succ 0 = t.B 1 0 := by
            simpa [tSwap, LeftTransform.swap, LeftTransform.trans] using
              congrFun (applyRowOperation_swap_succ_one_target t.B i.succ) 0
          have hswapZero : tSwap.B i.succ.succ 0 = 0 := by
            rw [hswapEq]
            exact hrowOneBefore
          have hbezoutZero : tBez.B i.succ.succ 0 = 0 := by
            simpa [tBez, tSwap, LeftTransform.topBezout, LeftTransform.trans] using
              (Bezout_preserves_zeros (m := m) (n := n) (a := tSwap.B 0 0) (b := tSwap.B 1 0)
                (A := tSwap.B) i hswapZero)
          calc
            (clearFirstColumnStep i.succ t).B i.succ.succ 0 = tNorm.B i.succ.succ 0 := by
              simpa [hclear]
            _ = tBez.B i.succ.succ 0 := hbelowEq i.succ
            _ = 0 := hbezoutZero


theorem clearFirstColumnLoop_topLeft_ne_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (htop : t.B 0 0 ≠ 0) :
    (clearFirstColumnLoop k hk t).B 0 0 ≠ 0 := by
  induction k generalizing t with
  | zero =>
      simpa [clearFirstColumnLoop] using htop
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have htop' : t'.B 0 0 ≠ 0 := by
        simpa [t', hk'] using ih hk' t htop
      simpa [clearFirstColumnLoop, hk', t'] using
        clearFirstColumnStep_topLeft_ne_zero i t' htop'


theorem clearFirstColumnLoop_topLeft_normalized {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (hnorm : t.B 0 0 = normalize (t.B 0 0)) :
    (clearFirstColumnLoop k hk t).B 0 0 = normalize ((clearFirstColumnLoop k hk t).B 0 0) := by
  induction k generalizing t with
  | zero =>
      simpa [clearFirstColumnLoop] using hnorm
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have hnorm' : t'.B 0 0 = normalize (t'.B 0 0) := by
        simpa [t', hk'] using ih hk' t hnorm
      simpa [clearFirstColumnLoop, hk', t'] using
        clearFirstColumnStep_topLeft_normalized i t' hnorm'


theorem clearFirstColumnLoop_prefix_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A) :
    ∀ j : Fin (m + 1), j.1 < k -> (clearFirstColumnLoop k hk t).B j.succ 0 = 0 := by
  induction k generalizing t with
  | zero =>
      intro j hj
      exact False.elim (Nat.not_lt_zero _ hj)
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := clearFirstColumnLoop k (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)) t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      intro j hj
      have hprefix : ∀ j' : Fin (m + 1), j'.1 < i.1 -> t'.B j'.succ 0 = 0 := by
        intro j' hj'
        simpa [t', hk'] using ih hk' t j' hj'
      simpa [clearFirstColumnLoop, hk', t'] using
        clearFirstColumnStep_prefix_zero i t' hprefix j hj


theorem reduceTopRowStep_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) (hzero : t.B i.succ 0 = 0) :
    (reduceTopRowStep i t).B 0 0 = t.B 0 0 := by
  unfold reduceTopRowStep
  cases hrow : firstNonzero? (fun j : Fin n => t.B i.succ j.succ) with
  | none =>
      rfl
  | some j =>
      simp [hrow, LeftTransform.add, LeftTransform.trans,
        applyRowOperation, topReductionCoeff, hzero]


theorem reduceTopRowStep_lowerRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i j : Fin (m + 1)) (t : LeftTransform A) :
    (reduceTopRowStep i t).B j.succ = t.B j.succ := by
  unfold reduceTopRowStep
  cases hrow : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) with
  | none =>
      rfl
  | some p =>
      ext s
      simp [hrow, LeftTransform.add, LeftTransform.trans, applyRowOperation]


theorem reduceTopRowStep_topEntry_eq_of_source_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) (c : Fin (n + 1))
    (hsrc : t.B i.succ c = 0) :
    (reduceTopRowStep i t).B 0 c = t.B 0 c := by
  unfold reduceTopRowStep
  cases hrow : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) with
  | none =>
      rfl
  | some p =>
      simp [hrow, LeftTransform.add, LeftTransform.trans,
        applyRowOperation, topReductionCoeff, hsrc]


theorem reduceTopRowStep_current_reduced {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i : Fin (m + 1)) (t : LeftTransform A) {j : Fin n}
    (hrow : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) = some j) :
    (reduceTopRowStep i t).B 0 j.succ =
      (reduceTopRowStep i t).B 0 j.succ % t.B i.succ j.succ := by
  unfold reduceTopRowStep
  rw [hrow]
  change applyRowOperation t.B (.add i.succ 0 (topReductionCoeff t.B i j)) 0 j.succ =
    applyRowOperation t.B (.add i.succ 0 (topReductionCoeff t.B i j)) 0 j.succ % t.B i.succ j.succ
  rw [applyRowOperation_reduceTop_pivot t.B i j]
  rw [CanonicalMod.mod_mod]


theorem reduceTopRowStep_preserves_reduced {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (i r : Fin (m + 1)) (t : LeftTransform A) {q : Fin n}
    (hrow : firstNonzero? (fun s : Fin n => t.B r.succ s.succ) = some q)
    (hreduced : t.B 0 q.succ = t.B 0 q.succ % t.B r.succ q.succ)
    (hsrcZero : t.B i.succ q.succ = 0) :
    (reduceTopRowStep i t).B 0 q.succ =
      (reduceTopRowStep i t).B 0 q.succ % t.B r.succ q.succ := by
  have htop := reduceTopRowStep_topEntry_eq_of_source_zero i t q.succ hsrcZero
  have hrowEq : (reduceTopRowStep i t).B r.succ q.succ = t.B r.succ q.succ := by
    exact congrFun (reduceTopRowStep_lowerRow i r t) q.succ
  simpa [htop, hrowEq] using hreduced


theorem reduceTopRowLoop_lowerRight {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A) :
    lowerRight (reduceTopRowLoop k hk t).B = lowerRight t.B := by
  induction k generalizing t with
  | zero =>
      simp [reduceTopRowLoop]
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      change lowerRight (reduceTopRowStep i t').B = lowerRight t.B
      cases hrow : firstNonzero? (fun s : Fin n => t'.B i.succ s.succ) with
      | none =>
          unfold reduceTopRowStep
          rw [hrow]
          simpa [t'] using ih hk' t
      | some p =>
          unfold reduceTopRowStep
          rw [hrow]
          simpa [LeftTransform.add, LeftTransform.trans,
            lowerRight_applyRowOperation_addToTop, t'] using ih hk' t


theorem reduceTopRowLoop_lowerRow {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A) (j : Fin (m + 1)) :
    (reduceTopRowLoop k hk t).B j.succ = t.B j.succ := by
  induction k generalizing t with
  | zero =>
      simp [reduceTopRowLoop]
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      change (reduceTopRowStep i t').B j.succ = t.B j.succ
      calc
        (reduceTopRowStep i t').B j.succ = t'.B j.succ := reduceTopRowStep_lowerRow i j t'
        _ = t.B j.succ := by simpa [t', hk'] using ih hk' t


theorem reduceTopRowLoop_below_zero {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (hzero : ∀ i : Fin (m + 1), t.B i.succ 0 = 0) :
    ∀ i : Fin (m + 1), (reduceTopRowLoop k hk t).B i.succ 0 = 0 := by
  induction k generalizing t with
  | zero =>
      intro i
      simp [reduceTopRowLoop, hzero]
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have hzero' : ∀ j : Fin (m + 1), t'.B j.succ 0 = 0 := by
        simpa [t', hk'] using ih hk' t hzero
      intro j
      change (reduceTopRowStep i t').B j.succ 0 = 0
      rw [show (reduceTopRowStep i t').B j.succ 0 = t'.B j.succ 0 by
        exact congrFun (reduceTopRowStep_lowerRow i j t') 0]
      exact hzero' j


theorem reduceTopRowLoop_topLeft {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (hzero : ∀ i : Fin (m + 1), t.B i.succ 0 = 0) :
    (reduceTopRowLoop k hk t).B 0 0 = t.B 0 0 := by
  induction k generalizing t with
  | zero =>
      simp [reduceTopRowLoop]
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have hzero' : ∀ j : Fin (m + 1), t'.B j.succ 0 = 0 := by
        simpa [t', hk'] using reduceTopRowLoop_below_zero k hk' t hzero
      change (reduceTopRowStep i t').B 0 0 = t.B 0 0
      calc
        (reduceTopRowStep i t').B 0 0 = t'.B 0 0 := reduceTopRowStep_topLeft i t' (hzero' i)
        _ = t.B 0 0 := by simpa [t', hk'] using ih hk' t hzero


theorem reduceTopRowLoop_reduced_prefix {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) R}
    (k : Nat) (hk : k ≤ m + 1) (t : LeftTransform A)
    (hLower : IsHermiteNormalFormFin (lowerRight t.B))
    (hzero : ∀ i : Fin (m + 1), t.B i.succ 0 = 0) :
    ∀ i : Fin (m + 1), i.1 < k ->
      match firstNonzero? (fun s : Fin n => t.B i.succ s.succ) with
      | none => True
      | some j =>
          (reduceTopRowLoop k hk t).B 0 j.succ =
            (reduceTopRowLoop k hk t).B 0 j.succ % t.B i.succ j.succ := by
  induction k generalizing t with
  | zero =>
      intro i hi
      exact False.elim (Nat.not_lt_zero _ hi)
  | succ k ih =>
      let hk' : k ≤ m + 1 := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let t' := reduceTopRowLoop k hk' t
      let iCurr : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      have hloop : reduceTopRowLoop (k + 1) hk t = reduceTopRowStep iCurr t' := by
        rfl
      have hLowerEq : lowerRight t'.B = lowerRight t.B := by
        simpa [t', hk'] using reduceTopRowLoop_lowerRight k hk' t
      have hLower' : IsHermiteNormalFormFin (lowerRight t'.B) := by
        rw [hLowerEq]
        exact hLower
      have hzero' : ∀ i : Fin (m + 1), t'.B i.succ 0 = 0 := by
        simpa [t', hk'] using reduceTopRowLoop_below_zero k hk' t hzero
      intro i hi
      have hRowEq : t'.B i.succ = t.B i.succ := by
        simpa [t', hk'] using reduceTopRowLoop_lowerRow k hk' t i
      have hi' : i.1 < k ∨ i.1 = k := Nat.lt_succ_iff_lt_or_eq.mp hi
      rcases hi' with hi' | hEq
      · cases hcurr : firstNonzero? (fun s : Fin n => t'.B iCurr.succ s.succ) with
        | none =>
            rw [hloop, reduceTopRowStep, hcurr]
            simpa [t'] using ih hk' t hLower hzero i hi'
        | some p =>
            cases hrow : firstNonzero? (fun s : Fin n => t'.B i.succ s.succ) with
            | none =>
                have hrow' : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) = none := by
                  simpa [hRowEq] using hrow
                rw [hrow']
                simp
            | some q =>
                have hrow' : firstNonzero? (fun s : Fin n => t.B i.succ s.succ) = some q := by
                  simpa [hRowEq] using hrow
                have hsrcZero : t'.B iCurr.succ q.succ = 0 := by
                  exact hnf_rowBelow_zero_at_pivot hLower'
                    (by simpa [iCurr] using hi') hrow
                have hprev :
                    t'.B 0 q.succ = t'.B 0 q.succ % t'.B i.succ q.succ := by
                  have hprev' := ih hk' t hLower hzero i hi'
                  simpa [t', hk', hrow', hRowEq] using hprev'
                have hden : t'.B i.succ q.succ = t.B i.succ q.succ := by
                  exact congrFun hRowEq q.succ
                rw [hrow', hloop]
                simpa [hden] using
                  reduceTopRowStep_preserves_reduced iCurr i t' hrow hprev hsrcZero
      · have : i = iCurr := Fin.ext hEq
        subst this
        have hRowEqCurr : t'.B iCurr.succ = t.B iCurr.succ := by
          simpa [t', hk'] using reduceTopRowLoop_lowerRow k hk' t iCurr
        cases hrow : firstNonzero? (fun s : Fin n => t'.B iCurr.succ s.succ) with
        | none =>
            have hrow' : firstNonzero? (fun s : Fin n => t.B iCurr.succ s.succ) = none := by
              simpa [hRowEqCurr] using hrow
            rw [hrow']
            simp
        | some q =>
            have hrow' : firstNonzero? (fun s : Fin n => t.B iCurr.succ s.succ) = some q := by
              simpa [hRowEqCurr] using hrow
            have hden : t'.B iCurr.succ q.succ = t.B iCurr.succ q.succ := by
              exact congrFun hRowEqCurr q.succ
            rw [hrow', hloop]
            simpa [hRowEqCurr] using reduceTopRowStep_current_reduced iCurr t' hrow


def hermiteNormalFormFin {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix (Fin m) (Fin n) R) : FinHNFResult A := by
  induction n generalizing m with
  | zero =>
      refine
        { U := 1
          H := A
          left_mul := by simp
          unimodular := unimodular_one
          isHermite := IsHermiteNormalFormFin.emptyCols _ }
  | succ n ih =>
      cases m with
      | zero =>
          refine
            { U := 1
              H := A
              left_mul := by simp
              unimodular := unimodular_one
              isHermite := IsHermiteNormalFormFin.emptyRows _ }
      | succ m =>
          by_cases hcol : firstNonzero? (fun i : Fin (m + 1) => A i 0) = none
          · let tailRes := ih (m := m + 1) (tailCols A)
            refine
              { U := tailRes.U
                H := tailRes.U * A
                left_mul := by rfl
                unimodular := tailRes.unimodular
                isHermite := ?_ }
            refine IsHermiteNormalFormFin.zeroCol _ ?_ ?_
            · exact firstCol_zero_mul tailRes.U A (firstNonzero?_eq_none (fun i : Fin (m + 1) => A i 0) hcol)
            · simpa [tailCols_mul, tailRes.left_mul] using tailRes.isHermite
          · cases m with
            | zero =>
                have h00 : A 0 0 ≠ 0 := by
                  cases hfirst : firstNonzero? (fun i : Fin 1 => A i 0) with
                  | none =>
                      exact False.elim (hcol hfirst)
                  | some i =>
                      cases i using Fin.cases with
                      | zero =>
                          simpa using firstNonzero?_some_ne_zero (fun i : Fin 1 => A i 0) hfirst
                      | succ i =>
                          exact Fin.elim0 i
                let tNorm :=
                  LeftTransform.unitSmul A 0 (normUnit (A 0 0) : R) (normUnit (A 0 0)).isUnit
                have hNormEq : tNorm.B 0 0 = normalize (A 0 0) := by
                  simp [tNorm, LeftTransform.unitSmul, applyRowOperation, normalize_apply, mul_comm]
                refine
                  { U := tNorm.U
                    H := tNorm.B
                    left_mul := tNorm.left_mul
                    unimodular := tNorm.unimodular
                    isHermite := ?_ }
                refine IsHermiteNormalFormFin.pivot _ ?_ ?_ ?_ ?_ ?_
                · rw [hNormEq]
                  exact mt normalize_eq_zero.mp h00
                · rw [hNormEq]
                  exact (normalize_idem (A 0 0)).symm
                · intro i
                  exact Fin.elim0 i
                · exact IsHermiteNormalFormFin.emptyRows _
                · intro i
                  exact Fin.elim0 i
            | succ m =>
                cases hfirst : firstNonzero? (fun i : Fin (m + 2) => A i 0) with
                | none =>
                    exact False.elim (hcol hfirst)
                | some i =>
                    let tSwap := LeftTransform.swap A i 0
                    let tNorm :=
                      tSwap.trans <|
                        LeftTransform.unitSmul tSwap.B 0 (normUnit (tSwap.B 0 0) : R)
                          (normUnit (tSwap.B 0 0)).isUnit
                    have hi0 : A i 0 ≠ 0 := firstNonzero?_some_ne_zero (fun i : Fin (m + 2) => A i 0) hfirst
                    have hNormEq : tNorm.B 0 0 = normalize (A i 0) := by
                      by_cases hi : i = 0
                      · subst hi
                        simp [tNorm, tSwap, LeftTransform.unitSmul, LeftTransform.swap,
                          LeftTransform.trans, applyRowOperation, normalize_apply, mul_comm]
                      · simp [tNorm, tSwap, LeftTransform.unitSmul, LeftTransform.swap,
                          LeftTransform.trans, applyRowOperation, normalize_apply, mul_comm,
                          show ¬ (0 : Fin (m + 2)) = i by simpa [eq_comm] using hi]
                    have hNormTopNonzero : tNorm.B 0 0 ≠ 0 := by
                      rw [hNormEq]
                      exact mt normalize_eq_zero.mp hi0
                    have hNormTopNormalized : tNorm.B 0 0 = normalize (tNorm.B 0 0) := by
                      rw [hNormEq]
                      exact (normalize_idem (A i 0)).symm
                    let tClear :=
                      clearFirstColumnLoop (A := A) (m := m) (n := n) (m + 1) le_rfl tNorm
                    let lowerRes := ih (m := m + 1) (lowerRight tClear.B)
                    let tLift :=
                      LeftTransform.diagLift tClear.B lowerRes.U lowerRes.unimodular
                    let tAfterLift := tClear.trans tLift
                    let tFinal :=
                      reduceTopRowLoop (A := A) (m := m) (n := n) (m + 1) le_rfl tAfterLift
                    have hClearTopNonzero : tClear.B 0 0 ≠ 0 := by
                      exact clearFirstColumnLoop_topLeft_ne_zero (m + 1) le_rfl tNorm hNormTopNonzero
                    have hClearTopNormalized : tClear.B 0 0 = normalize (tClear.B 0 0) := by
                      exact clearFirstColumnLoop_topLeft_normalized (m + 1) le_rfl tNorm hNormTopNormalized
                    have hClearBelow : ∀ r : Fin (m + 1), tClear.B r.succ 0 = 0 := by
                      intro r
                      exact clearFirstColumnLoop_prefix_zero (m + 1) le_rfl tNorm r r.is_lt
                    have hAfterLiftLower : lowerRight tAfterLift.B = lowerRes.H := by
                      simp [tAfterLift, tLift, LeftTransform.diagLift, LeftTransform.trans,
                        lowerRight_diagLiftMatrix_mul, lowerRes.left_mul]
                    have hAfterLiftTop : tAfterLift.B 0 0 = tClear.B 0 0 := by
                      simp [tAfterLift, tLift, LeftTransform.diagLift, LeftTransform.trans,
                        diagLiftMatrix_mul_topRow]
                    have hAfterLiftBelow : ∀ r : Fin (m + 1), tAfterLift.B r.succ 0 = 0 := by
                      intro r
                      simp [tAfterLift, tLift, LeftTransform.diagLift, LeftTransform.trans,
                        _root_.Matrix.mul_apply, diagLiftMatrix, hClearBelow, Fin.sum_univ_succ]
                    have hFinalTop : tFinal.B 0 0 = tAfterLift.B 0 0 := by
                      exact reduceTopRowLoop_topLeft (m + 1) le_rfl tAfterLift hAfterLiftBelow
                    have hFinalBelow : ∀ r : Fin (m + 1), tFinal.B r.succ 0 = 0 := by
                      exact reduceTopRowLoop_below_zero (m + 1) le_rfl tAfterLift hAfterLiftBelow
                    have hFinalLower : lowerRight tFinal.B = lowerRes.H := by
                      rw [reduceTopRowLoop_lowerRight (m + 1) le_rfl tAfterLift, hAfterLiftLower]
                    have hFinalReduced :
                        ∀ r : Fin (m + 1),
                          match firstNonzero? (fun s : Fin n => tFinal.B r.succ s.succ) with
                          | none => True
                          | some j =>
                              tFinal.B 0 j.succ = tFinal.B 0 j.succ % tFinal.B r.succ j.succ := by
                      intro r
                      have hLowerHNF : IsHermiteNormalFormFin (lowerRight tAfterLift.B) := by
                        simpa [hAfterLiftLower] using lowerRes.isHermite
                      have hRowEq : tFinal.B r.succ = tAfterLift.B r.succ := by
                        exact reduceTopRowLoop_lowerRow (m + 1) le_rfl tAfterLift r
                      simpa [hRowEq, reduceTopRowLoop_lowerRight (m + 1) le_rfl tAfterLift] using
                        reduceTopRowLoop_reduced_prefix (m + 1) le_rfl tAfterLift hLowerHNF
                          hAfterLiftBelow r r.is_lt
                    refine
                      { U := tFinal.U
                        H := tFinal.B
                        left_mul := tFinal.left_mul
                        unimodular := tFinal.unimodular
                        isHermite := ?_ }
                    refine IsHermiteNormalFormFin.pivot _ ?_ ?_ ?_ ?_ ?_
                    · rw [hFinalTop, hAfterLiftTop]
                      exact hClearTopNonzero
                    · rw [hFinalTop, hAfterLiftTop]
                      exact hClearTopNormalized
                    · exact hFinalBelow
                    · simpa [hFinalLower] using lowerRes.isHermite
                    · exact hFinalReduced

end Internal

end NormalForms.Matrix.Hermite
