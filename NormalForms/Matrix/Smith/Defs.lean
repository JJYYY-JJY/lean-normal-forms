import NormalForms.Matrix.Certificates
import NormalForms.Matrix.Hermite.Defs

/-!
# Smith Normal Form Definitions
Internal Smith predicates, invariant-factor readers, and the
lightweight public specification wrappers.
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


def firstNonzeroEntry? {m n : Nat} {R : Type _}
    [Zero R] [DecidableEq R] :
    _root_.Matrix (Fin m) (Fin n) R -> Option (Fin m × Fin n)
  | A =>
      let rec goRows : (k : Nat) -> k ≤ m -> Option (Fin m × Fin n)
        | 0, _ => none
        | k + 1, hk =>
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            match goRows k hk' with
            | some p => some p
            | none =>
                let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                match firstNonzero? (fun j : Fin n => A i j) with
                | none => none
                | some j => some (i, j)
      goRows m (Nat.le_refl _)


theorem firstNonzeroEntry?_eq_none {m n : Nat} {R : Type _}
    [Zero R] [DecidableEq R] :
    ∀ (A : _root_.Matrix (Fin m) (Fin n) R),
      firstNonzeroEntry? A = none -> A = 0
  | A, hnone => by
      ext i j
      unfold firstNonzeroEntry? at hnone
      have hnone' : firstNonzeroEntry?.goRows A m (Nat.le_refl m) = none := by
        simpa [firstNonzeroEntry?] using hnone
      clear hnone
      let rowWitness : ∀ k (hk : k ≤ m),
          firstNonzeroEntry?.goRows A k hk = none ->
            ∀ i' : Fin m, i'.1 < k -> ∀ j' : Fin n, A i' j' = 0 := by
        intro k
        induction k with
        | zero =>
            intro hk hgo i' hi
            exact False.elim (Nat.not_lt_zero _ hi)
        | succ k ih =>
            intro hk hgo i' hi j'
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            have hsplit :
                (match firstNonzeroEntry?.goRows A k hk' with
                | some p => some p
                | none =>
                    let i0 : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                    match firstNonzero? (fun s : Fin n => A i0 s) with
                    | none => none
                    | some j0 => some (i0, j0)) = none := by
              simpa [firstNonzeroEntry?] using hgo
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hEq
            · have hgo' : firstNonzeroEntry?.goRows A k hk' = none := by
                cases hgoRows : firstNonzeroEntry?.goRows A k hk' with
                | none =>
                    rfl
                | some p =>
                    simp [hgoRows] at hsplit
              exact ih hk' hgo' i' hi' j'
            · have : i' = ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ := Fin.ext hEq
              subst this
              cases hrow : firstNonzero? (fun s : Fin n => A ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ s) with
              | none =>
                  exact firstNonzero?_eq_none _ hrow j'
              | some p =>
                  have : False := by
                    cases hgoRows : firstNonzeroEntry?.goRows A k hk' with
                    | none =>
                        simp [hgoRows, hrow] at hsplit
                    | some q =>
                        simp [hgoRows] at hsplit
                  exact False.elim this
      exact rowWitness m (Nat.le_refl m) hnone' i i.is_lt j


theorem firstNonzeroEntry?_some_ne_zero {m n : Nat} {R : Type _}
    [Zero R] [DecidableEq R] :
    ∀ (A : _root_.Matrix (Fin m) (Fin n) R) {p : Fin m × Fin n},
      firstNonzeroEntry? A = some p -> A p.1 p.2 ≠ 0
  | A, p, hsome => by
      unfold firstNonzeroEntry? at hsome
      have hsome' : firstNonzeroEntry?.goRows A m (Nat.le_refl m) = some p := by
        simpa [firstNonzeroEntry?] using hsome
      clear hsome
      let rowWitness : ∀ k (hk : k ≤ m) {p : Fin m × Fin n},
          firstNonzeroEntry?.goRows A k hk = some p -> A p.1 p.2 ≠ 0 := by
        intro k
        induction k with
        | zero =>
            intro hk p h
            simpa [firstNonzeroEntry?.goRows] using h
        | succ k ih =>
            intro hk p h
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            cases hgo : firstNonzeroEntry?.goRows A k hk' with
            | some q =>
                simp [firstNonzeroEntry?.goRows, hgo] at h
                cases h
                exact ih hk' hgo
            | none =>
                let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                cases hrow : firstNonzero? (fun j : Fin n => A i j) with
                | none =>
                    have : none = some p := by
                      simpa [firstNonzeroEntry?.goRows, hgo, i, hrow] using h
                    cases this
                | some j =>
                    have h' : some (i, j) = some p := by
                      simpa [firstNonzeroEntry?.goRows, hgo, i, hrow] using h
                    cases h'
                    exact firstNonzero?_some_ne_zero (fun s : Fin n => A i s) hrow
      exact rowWitness m (Nat.le_refl m) hsome'


def firstUndivisible? {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    {n : Nat} -> R -> (Fin n -> R) -> Option (Fin n)
  | 0, _, _ => none
  | _ + 1, d, row =>
      if hmod : row 0 % d = 0 then
        Option.map Fin.succ (firstUndivisible? d fun j => row j.succ)
      else
        some 0


theorem firstUndivisible?_eq_none {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    {n : Nat} -> (d : R) -> (row : Fin n -> R) ->
      firstUndivisible? d row = none -> ∀ i, d ∣ row i
  | 0, _, _, _, i => Fin.elim0 i
  | _ + 1, d, row, hnone, i => by
      by_cases hmod : row 0 % d = 0
      · rw [firstUndivisible?, hmod] at hnone
        have htail : firstUndivisible? d (fun k => row k.succ) = none := by
          simpa using hnone
        cases i using Fin.cases with
        | zero =>
            exact (EuclideanDomain.mod_eq_zero).1 hmod
        | succ j =>
            exact firstUndivisible?_eq_none d (fun k => row k.succ) htail j
      · simp [firstUndivisible?, hmod] at hnone


theorem firstUndivisible?_some_not_dvd {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    {n : Nat} -> (d : R) -> (row : Fin n -> R) -> {i : Fin n} ->
      firstUndivisible? d row = some i -> ¬ d ∣ row i
  | 0, _, _, i, _ => Fin.elim0 i
  | _ + 1, d, row, i, hsome => by
      by_cases hmod : row 0 % d = 0
      · rw [firstUndivisible?, hmod] at hsome
        cases i using Fin.cases with
        | zero =>
            simp at hsome
        | succ j =>
            cases htail : firstUndivisible? d (fun k => row k.succ) with
            | none =>
                simp [htail] at hsome
            | some j' =>
                simp [htail] at hsome
                subst hsome
                exact firstUndivisible?_some_not_dvd d (fun k => row k.succ) htail
      · cases i using Fin.cases with
        | zero =>
            simpa [EuclideanDomain.mod_eq_zero] using hmod
        | succ j =>
            have hzero : firstUndivisible? d row = some (0 : Fin (_ + 1)) := by
              simp [firstUndivisible?, hmod]
            have : (0 : Fin (_ + 1)) = j.succ := by
              simpa using hzero.symm.trans hsome
            exact False.elim (Fin.succ_ne_zero _ this.symm)


def firstUndivisibleLowerRight? {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R -> R -> Option (Fin m × Fin n)
  | A, d =>
      let rec goRows : (k : Nat) -> k ≤ m -> Option (Fin m × Fin n)
        | 0, _ => none
        | k + 1, hk =>
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            match goRows k hk' with
            | some p => some p
            | none =>
                let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                Option.map (fun j : Fin n => (i, j))
                  (firstUndivisible? d (fun j : Fin n => A i.succ j.succ))
      goRows m (Nat.le_refl _)


theorem firstUndivisibleLowerRight?_eq_none {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    ∀ (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (d : R),
      firstUndivisibleLowerRight? A d = none ->
        ∀ i : Fin m, ∀ j : Fin n, d ∣ A i.succ j.succ
  | A, d, hnone => by
      unfold firstUndivisibleLowerRight? at hnone
      have hnone' : firstUndivisibleLowerRight?.goRows A d m (Nat.le_refl m) = none := by
        simpa [firstUndivisibleLowerRight?] using hnone
      clear hnone
      let rowWitness : ∀ k (hk : k ≤ m),
          firstUndivisibleLowerRight?.goRows A d k hk = none ->
            ∀ i' : Fin m, i'.1 < k -> ∀ j' : Fin n, d ∣ A i'.succ j'.succ := by
        intro k
        induction k with
        | zero =>
            intro hk hgo i' hi
            exact False.elim (Nat.not_lt_zero _ hi)
        | succ k ih =>
            intro hk hgo i' hi j'
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hEq
            · have hgo' : firstUndivisibleLowerRight?.goRows A d k hk' = none := by
                cases hgoRows : firstUndivisibleLowerRight?.goRows A d k hk' with
                | none =>
                    rfl
                | some p =>
                    have : some p = none := by
                      simpa [firstUndivisibleLowerRight?.goRows, hgoRows] using hgo
                    cases this
              exact ih hk' hgo' i' hi' j'
            · let i0 : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
              have : i' = i0 := Fin.ext hEq
              subst this
              cases hgoRows : firstUndivisibleLowerRight?.goRows A d k hk' with
              | some p =>
                  have : False := by
                    simp [firstUndivisibleLowerRight?.goRows, hgoRows] at hgo
                  exact False.elim this
              | none =>
                  cases hrow : firstUndivisible? d (fun s : Fin n => A i0.succ s.succ) with
                  | none =>
                      exact firstUndivisible?_eq_none d (fun s : Fin n => A i0.succ s.succ) hrow j'
                  | some p =>
                      have : False := by
                        have hrowNone :
                            firstUndivisible? d (fun s : Fin n => A i0.succ s.succ) = none := by
                          simpa [firstUndivisibleLowerRight?.goRows, hgoRows] using hgo
                        have : some p = none := hrow.symm.trans hrowNone
                        cases this
                      exact False.elim this
      intro i j
      exact rowWitness m (Nat.le_refl m) hnone' i i.is_lt j


theorem firstUndivisibleLowerRight?_some_not_dvd {m n : Nat} {R : Type _}
    [EuclideanDomain R] [DecidableEq R] :
    ∀ (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R) (d : R)
      {p : Fin m × Fin n},
      firstUndivisibleLowerRight? A d = some p ->
        ¬ d ∣ A p.1.succ p.2.succ
  | A, d, p, hsome => by
      unfold firstUndivisibleLowerRight? at hsome
      have hsome' : firstUndivisibleLowerRight?.goRows A d m (Nat.le_refl m) = some p := by
        simpa [firstUndivisibleLowerRight?] using hsome
      clear hsome
      let rowWitness : ∀ k (hk : k ≤ m) {p : Fin m × Fin n},
          firstUndivisibleLowerRight?.goRows A d k hk = some p ->
            ¬ d ∣ A p.1.succ p.2.succ := by
        intro k
        induction k with
        | zero =>
            intro hk p h
            simpa [firstUndivisibleLowerRight?.goRows] using h
        | succ k ih =>
            intro hk p h
            let hk' : k ≤ m := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
            cases hgo : firstUndivisibleLowerRight?.goRows A d k hk' with
            | some q =>
                simp [firstUndivisibleLowerRight?.goRows, hgo] at h
                cases h
                exact ih hk' hgo
            | none =>
                let i : Fin m := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
                cases hrow : firstUndivisible? d (fun j : Fin n => A i.succ j.succ) with
                | none =>
                    have hnone :
                        firstUndivisibleLowerRight?.goRows A d (k + 1) hk = none := by
                      simpa [firstUndivisibleLowerRight?.goRows, hgo, hrow]
                    rw [hnone] at h
                    cases h
                | some j =>
                    have h' := h
                    simp [firstUndivisibleLowerRight?.goRows, hgo] at h'
                    rcases h' with ⟨a, ha, hp⟩
                    have ha' : a = j := by
                      have hs : some a = some j := by
                        simpa [i] using ha.symm.trans hrow
                      exact Option.some.inj hs
                    subst a
                    have hp' : p = (i, j) := hp.symm
                    cases hp'
                    exact firstUndivisible?_some_not_dvd d (fun s : Fin n => A i.succ s.succ) hrow
      exact rowWitness m (Nat.le_refl m) hsome'

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

def smithColumnSpan {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R]
    (A : _root_.Matrix m n R) : Submodule R (m -> R) :=
  LinearMap.range A.mulVecLin


/-- Read normalized nonzero diagonal entries from a Smith matrix, truncating at the first `0`.

The public wrapper works for arbitrary finite index types by reindexing to
`Fin`. We intentionally avoid a companion `[simp]` bridge lemma for `Fin`
matrices, since expanding `Fintype.equivFin` aggressively can make elaboration
pathologically slow.
-/
noncomputable def smithInvariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) : List R :=
  Internal.invariantFactors
    (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)

/-- Public Smith-normal-form predicate.

Like `smithInvariantFactors`, this wrapper is defined by reindexing to the
internal `Fin` predicate. Callers should not expect `simp` to compute through
that bridge automatically; use the internal predicate for concrete executable
smoke checks, and use this public predicate for API-level statements.
-/
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




end NormalForms.Matrix.Smith
