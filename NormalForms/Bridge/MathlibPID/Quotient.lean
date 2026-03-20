import NormalForms.Bridge.MathlibPID.Basic
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# PID Quotient Bridge

Semantic bridge theorems between the executable Smith layer and mathlib's
module-theoretic quotient decompositions.
-/

namespace NormalForms.Bridge.MathlibPID

open scoped Matrix DirectSum

open NormalForms.Matrix.Smith

private noncomputable def pidExecutableResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) : NormalForms.Matrix.Smith.SNFResult A :=
  Classical.choose (NormalForms.Matrix.Smith.smithNormalForm_exists A)

noncomputable def pidExecutableInvariantFactorCount {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) : Nat :=
  (pidExecutableResult A).invariantFactors.length

noncomputable def pidExecutableInvariantFactorFn {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    Fin (pidExecutableInvariantFactorCount A) → R :=
  fun i => (pidExecutableResult A).invariantFactors.get i

@[simp] theorem pidExecutableResult_spec {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    NormalForms.Matrix.Smith.smithNormalForm A = some (pidExecutableResult A) :=
  Classical.choose_spec (NormalForms.Matrix.Smith.smithNormalForm_exists A)

@[simp] theorem pidExecutableInvariantFactorCount_eq_length {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    pidExecutableInvariantFactorCount A = (pidExecutableResult A).invariantFactors.length :=
  rfl

@[simp] theorem pidExecutableResult_eq_of_hresult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    {A : _root_.Matrix m n R} {result : NormalForms.Matrix.Smith.SNFResult A}
    (hresult : NormalForms.Matrix.Smith.smithNormalForm A = some result) :
    pidExecutableResult A = result := by
  have hchosen := pidExecutableResult_spec A
  rw [hresult] at hchosen
  injection hchosen with hEq
  exact hEq.symm

noncomputable def pidExecutableQuotientEquivOfResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    ((m -> R) ⧸ pidSmithColumnSpan A) ≃ₗ[R]
      ((m -> R) ⧸ pidSmithColumnSpan (pidExecutableResult A).S) := by
  let result := pidExecutableResult A
  let hresult : NormalForms.Matrix.Smith.smithNormalForm A = some result :=
    pidExecutableResult_spec A
  let hU := NormalForms.Matrix.Smith.smithNormalForm_leftUnimodular hresult
  let hV := NormalForms.Matrix.Smith.smithNormalForm_rightUnimodular hresult
  let e : (m -> R) ≃ₗ[R] (m -> R) := pidUnimodularMulVecEquiv result.U hU
  have hspan :
      Submodule.map (e : (m -> R) →ₗ[R] (m -> R)) (pidSmithColumnSpan A) =
        pidSmithColumnSpan result.S := by
    calc
      Submodule.map (e : (m -> R) →ₗ[R] (m -> R)) (pidSmithColumnSpan A)
          = pidSmithColumnSpan (result.U * A) := by
              simpa [e, pidUnimodularMulVecEquiv] using
                (pidSmithColumnSpan_mul_left_unimodular (A := A) (U := result.U) hU).symm
      _ = pidSmithColumnSpan (result.U * A * result.V) := by
            simpa [Matrix.mul_assoc] using
              (pidSmithColumnSpan_mul_right_unimodular (A := result.U * A) (V := result.V) hV).symm
      _ = pidSmithColumnSpan result.S := by
            simp [result.two_sided_mul]
  exact Submodule.Quotient.equiv _ _ e hspan

private theorem invariantFactors_length_le_min {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) :
    (NormalForms.Matrix.Smith.Internal.invariantFactors A).length ≤ Nat.min m n := by
  induction m generalizing n with
  | zero =>
      simp [NormalForms.Matrix.Smith.Internal.invariantFactors]
  | succ m ih =>
      cases n with
      | zero =>
          simp [NormalForms.Matrix.Smith.Internal.invariantFactors]
      | succ n =>
          by_cases h0 : normalize (A 0 0) = 0
          · simp [NormalForms.Matrix.Smith.Internal.invariantFactors, h0]
          · rw [NormalForms.Matrix.Smith.Internal.invariantFactors]
            have hlen :
                (NormalForms.Matrix.Smith.Internal.invariantFactors
                  (NormalForms.Matrix.Hermite.lowerRight A)).length ≤
                  Nat.min m n :=
              ih (NormalForms.Matrix.Hermite.lowerRight A)
            simpa [h0, Nat.add_min_add_right] using Nat.succ_le_succ hlen

private theorem lt_min_of_succ_lt_min_succ {a b k : Nat}
    (hk : k + 1 < Nat.min (a + 1) (b + 1)) :
    k < Nat.min a b := by
  exact lt_min_iff.mpr
    ⟨Nat.lt_of_succ_lt_succ (Nat.lt_of_lt_of_le hk (Nat.min_le_left _ _)),
      Nat.lt_of_succ_lt_succ (Nat.lt_of_lt_of_le hk (Nat.min_le_right _ _))⟩

private theorem succ_lt_min_succ {a b k : Nat}
    (hk : k < Nat.min a b) :
    k + 1 < Nat.min (a + 1) (b + 1) := by
  exact lt_min_iff.mpr
    ⟨Nat.succ_lt_succ (lt_of_lt_of_le hk (Nat.min_le_left _ _)),
      Nat.succ_lt_succ (lt_of_lt_of_le hk (Nat.min_le_right _ _))⟩

private theorem diagEntry_lowerRight {m n : Nat} {R : Type _}
    {A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) R}
    (k : Nat) (hk : k < Nat.min m n) :
    NormalForms.Matrix.Smith.Internal.diagEntry
        (NormalForms.Matrix.Hermite.lowerRight A) k hk =
      NormalForms.Matrix.Smith.Internal.diagEntry A (k + 1)
        (succ_lt_min_succ hk) := by
  simp [NormalForms.Matrix.Smith.Internal.diagEntry, NormalForms.Matrix.Hermite.lowerRight]

private theorem diagEntry_ne_zero_of_lt_invariantFactors_length {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : NormalForms.Matrix.Smith.Internal.IsSmithNormalFormFin A) :
    ∀ k, k < (NormalForms.Matrix.Smith.Internal.invariantFactors A).length →
      ∀ hk : k < Nat.min m n, NormalForms.Matrix.Smith.Internal.diagEntry A k hk ≠ 0 := by
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
      simp [NormalForms.Matrix.Smith.Internal.invariantFactors, hzero] at hkLen
  | pivot A hpivot hnorm hrow hcol hLower hdiv ih =>
      intro hkLen hk
      rw [NormalForms.Matrix.Smith.Internal.invariantFactors_pivot hpivot hnorm] at hkLen
      cases k with
      | zero =>
          simpa [NormalForms.Matrix.Smith.Internal.diagEntry] using hpivot
      | succ k =>
          have hkLen' :
              k < (NormalForms.Matrix.Smith.Internal.invariantFactors
                (NormalForms.Matrix.Hermite.lowerRight A)).length := by
            simpa using hkLen
          have hk' : k < Nat.min _ _ := lt_min_of_succ_lt_min_succ hk
          have hne := ih k hkLen' hk'
          simpa [diagEntry_lowerRight (A := A) k hk'] using hne

private theorem diagEntry_eq_zero_of_invariantFactors_length_le {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (hA : NormalForms.Matrix.Smith.Internal.IsSmithNormalFormFin A) :
    ∀ k, (NormalForms.Matrix.Smith.Internal.invariantFactors A).length ≤ k →
      ∀ hk : k < Nat.min m n, NormalForms.Matrix.Smith.Internal.diagEntry A k hk = 0 := by
  intro k
  induction hA generalizing k with
  | emptyRows A =>
      intro hkLen hk
      simp at hk
  | emptyCols A =>
      intro hkLen hk
      simp at hk
  | zeroLead A hzero hrow hcol hLowerZero =>
      intro hkLen hk
      cases k with
      | zero =>
          simpa [NormalForms.Matrix.Smith.Internal.diagEntry] using hzero
      | succ k =>
          have hk' : k < Nat.min _ _ := lt_min_of_succ_lt_min_succ hk
          rw [← diagEntry_lowerRight (A := A) k hk']
          simp [hLowerZero, NormalForms.Matrix.Smith.Internal.diagEntry]
  | pivot A hpivot hnorm hrow hcol hLower hdiv ih =>
      intro hkLen hk
      rw [NormalForms.Matrix.Smith.Internal.invariantFactors_pivot hpivot hnorm] at hkLen
      cases k with
      | zero =>
          cases hkLen
      | succ k =>
          have hkLen' :
              (NormalForms.Matrix.Smith.Internal.invariantFactors
                (NormalForms.Matrix.Hermite.lowerRight A)).length ≤ k := by
            simpa using hkLen
          have hk' : k < Nat.min _ _ := lt_min_of_succ_lt_min_succ hk
          rw [← diagEntry_lowerRight (A := A) k hk']
          exact ih k hkLen' hk'

private def smithDiagEntryOrZero {m n : Nat} {R : Type _} [Zero R]
    (S : _root_.Matrix (Fin m) (Fin n) R) (i : Fin m) : R :=
  if h : i.1 < n then S i ⟨i.1, h⟩ else 0

private def smithCoordSubmodule {m n : Nat} {R : Type _}
    [CommRing R]
    (S : _root_.Matrix (Fin m) (Fin n) R) : Fin m → Submodule R R :=
  fun i => Ideal.span ({smithDiagEntryOrZero S i} : Set R)

private theorem smithColumnSpan_eq_pi_of_isSmithFin {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {S : _root_.Matrix (Fin m) (Fin n) R}
    (hS : NormalForms.Matrix.Smith.Internal.IsSmithNormalFormFin S) :
    LinearMap.range S.mulVecLin = Submodule.pi Set.univ (smithCoordSubmodule S) := by
  rcases NormalForms.Matrix.Smith.Internal.isSmithNormalFormFin_toDiag hS with ⟨hOff, _, _⟩
  refine le_antisymm ?_ ?_
  · rintro x ⟨v, rfl⟩
    rw [Submodule.mem_pi]
    intro i hi
    by_cases h : i.1 < n
    · let j : Fin n := ⟨i.1, h⟩
      have hmul : (_root_.Matrix.mulVec S v) i = S i j * v j := by
        classical
        rw [_root_.Matrix.mulVec, dotProduct]
        calc
          ∑ x, S i x * v x = ∑ x, if x = j then S i j * v j else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x _
            by_cases hx : x = j
            · simp [hx]
            · have hij : i.1 ≠ x.1 := by
                intro hEq
                apply hx
                ext
                simpa [j] using hEq.symm
              simp [hx, hOff i x hij]
          _ = S i j * v j := by
            simp
      rw [smithCoordSubmodule, smithDiagEntryOrZero, dif_pos h]
      change (_root_.Matrix.mulVec S v) i ∈ Ideal.span ({S i ⟨i.1, h⟩} : Set R)
      rw [hmul]
      exact Ideal.mem_span_singleton'.2 ⟨v j, by rw [mul_comm]⟩
    · rw [smithCoordSubmodule, smithDiagEntryOrZero, dif_neg h]
      rw [Ideal.mem_span_singleton, zero_dvd_iff]
      change (_root_.Matrix.mulVec S v) i = 0
      rw [_root_.Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero ?_
      intro j _
      have hij : i.1 ≠ j.1 := by
        intro hEq
        apply h
        exact hEq ▸ j.is_lt
      simp [hOff i j hij]
  · intro x hx
    rw [Submodule.mem_pi] at hx
    choose c hc using fun i : Fin m =>
      Ideal.mem_span_singleton'.1 (hx i (by simp))
    let v : Fin n → R := fun j =>
      if h : j.1 < m then c ⟨j.1, h⟩ else 0
    refine ⟨v, ?_⟩
    ext i
    by_cases h : i.1 < n
    · let j : Fin n := ⟨i.1, h⟩
      have hjm : j.1 < m := i.is_lt
      have hvj : v j = c i := by
        simp [v, j, hjm]
      change (_root_.Matrix.mulVec S v) i = x i
      classical
      rw [_root_.Matrix.mulVec, dotProduct]
      calc
        ∑ x_1, S i x_1 * v x_1 = ∑ x_1, if x_1 = j then S i j * v j else 0 := by
          refine Finset.sum_congr rfl ?_
          intro x_1 _
          by_cases hx : x_1 = j
          · simp [hx]
          · have hij : i.1 ≠ x_1.1 := by
              intro hEq
              apply hx
              ext
              simpa [j] using hEq.symm
            simp [hx, hOff i x_1 hij]
        _ = S i j * v j := by
          simp
        _ = x i := by
          simpa [smithCoordSubmodule, smithDiagEntryOrZero, h, j, hvj, mul_comm] using hc i
    · have hxi : x i = 0 := by
        have hmem : x i ∈ Ideal.span ({smithDiagEntryOrZero S i} : Set R) := hx i (by simp)
        simpa [smithDiagEntryOrZero, h] using (hc i).symm
      change (_root_.Matrix.mulVec S v) i = x i
      rw [_root_.Matrix.mulVec, dotProduct]
      rw [hxi]
      refine Finset.sum_eq_zero ?_
      intro j _
      have hij : i.1 ≠ j.1 := by
        intro hEq
        apply h
        exact hEq ▸ j.is_lt
      simp [hOff i j hij]

private noncomputable def pidExecutableResultFinMatrix {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    _root_.Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) R :=
  _root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) (pidExecutableResult A).S

private theorem pidExecutableResultFin_isSmith {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormFin (pidExecutableResultFinMatrix A) := by
  exact
    NormalForms.Matrix.Smith.Internal.isSmithNormalFormDiag_toFin
      (pidExecutableResult A).isSmith

noncomputable def pidExecutableQuotientEquivPiCoords {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    ((m -> R) ⧸ pidSmithColumnSpan A) ≃ₗ[R]
      (∀ i : Fin (Fintype.card m),
        R ⧸ smithCoordSubmodule (pidExecutableResultFinMatrix A) i) := by
  let result := pidExecutableResult A
  let Sfin := pidExecutableResultFinMatrix A
  let eRow : (m -> R) ≃ₗ[R] (Fin (Fintype.card m) -> R) :=
    LinearEquiv.funCongrLeft R R (Fintype.equivFin m).symm
  let eCol : (Fin (Fintype.card n) -> R) ≃ₗ[R] (n -> R) :=
    LinearEquiv.funCongrLeft R R (Fintype.equivFin n)
  have hspanFin :
      Submodule.map (eRow : (m -> R) →ₗ[R] (Fin (Fintype.card m) -> R))
          (pidSmithColumnSpan result.S) =
        LinearMap.range Sfin.mulVecLin := by
    have hlin :
        Sfin.mulVecLin =
          (eRow : (m -> R) →ₗ[R] (Fin (Fintype.card m) -> R)) ∘ₗ
            result.S.mulVecLin ∘ₗ
              (eCol : (Fin (Fintype.card n) -> R) →ₗ[R] (n -> R)) := by
      simpa [Sfin, eRow, eCol] using
        (Matrix.mulVecLin_reindex (Fintype.equivFin m) (Fintype.equivFin n) result.S)
    unfold pidSmithColumnSpan NormalForms.Matrix.Smith.smithColumnSpan
    rw [hlin, LinearMap.range_comp]
    have hsurj : Function.Surjective (eCol : (Fin (Fintype.card n) -> R) →ₗ[R] (n -> R)) :=
      eCol.surjective
    rw [LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr hsurj)]
  have hpi :
      LinearMap.range Sfin.mulVecLin =
        Submodule.pi Set.univ (smithCoordSubmodule Sfin) :=
    smithColumnSpan_eq_pi_of_isSmithFin (pidExecutableResultFin_isSmith A)
  exact (pidExecutableQuotientEquivOfResult A).trans <|
    (Submodule.Quotient.equiv _ _ eRow hspanFin).trans <|
      (Submodule.quotEquivOfEq _ _ hpi).trans <|
        Submodule.quotientPi _

private noncomputable def sumPiLequivProdPi {R α β : Type _}
    [Semiring R]
    {φ : α ⊕ β → Type _}
    [∀ s, AddCommMonoid (φ s)]
    [∀ s, Module R (φ s)] :
    ((s : α ⊕ β) → φ s) ≃ₗ[R]
      ((a : α) → φ (Sum.inl a)) × ((b : β) → φ (Sum.inr b)) where
  toFun f := (fun a => f (Sum.inl a), fun b => f (Sum.inr b))
  invFun fg := fun s =>
    match s with
    | Sum.inl a => fg.1 a
    | Sum.inr b => fg.2 b
  map_add' _ _ := by ext s <;> rfl
  map_smul' _ _ := by ext s <;> rfl
  left_inv f := by
    funext s
    cases s <;> rfl
  right_inv fg := by
    cases fg
    rfl

private noncomputable def splitRowEquiv {m k : Nat} (hkm : k ≤ m) :
    Fin k ⊕ Fin (m - k) ≃ Fin m :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hkm))

private theorem splitRowEquiv_apply_inl {m k : Nat} (hkm : k ≤ m) (i : Fin k) :
    (splitRowEquiv hkm (Sum.inl i)).1 = i.1 := by
  simp [splitRowEquiv, finSumFinEquiv_apply_left]

private theorem splitRowEquiv_apply_inl_eq_castLE {m k : Nat} (hkm : k ≤ m) (i : Fin k) :
    splitRowEquiv hkm (Sum.inl i) = Fin.castLE hkm i := by
  ext
  simp [splitRowEquiv, finSumFinEquiv_apply_left]

private theorem splitRowEquiv_apply_inr {m k : Nat} (hkm : k ≤ m) (j : Fin (m - k)) :
    (splitRowEquiv hkm (Sum.inr j)).1 = k + j.1 := by
  simp [splitRowEquiv, finSumFinEquiv_apply_right]

private theorem pidExecutableInvariantFactorCount_eq_internal_length {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    pidExecutableInvariantFactorCount A =
      (NormalForms.Matrix.Smith.Internal.invariantFactors
        (pidExecutableResultFinMatrix A)).length := by
  rfl

private theorem pidExecutableInvariantFactorCount_le_card_rows {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    pidExecutableInvariantFactorCount A ≤ Fintype.card m := by
  rw [pidExecutableInvariantFactorCount_eq_internal_length]
  exact le_trans
    (invariantFactors_length_le_min (pidExecutableResultFinMatrix A))
    (Nat.min_le_left _ _)

private theorem pidExecutableInvariantFactorCount_le_card_cols {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    pidExecutableInvariantFactorCount A ≤ Fintype.card n := by
  rw [pidExecutableInvariantFactorCount_eq_internal_length]
  exact le_trans
    (invariantFactors_length_le_min (pidExecutableResultFinMatrix A))
    (Nat.min_le_right _ _)

private theorem invariantFactors_get_eq_diagEntry {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {S : _root_.Matrix (Fin m) (Fin n) R}
    (hS : NormalForms.Matrix.Smith.Internal.IsSmithNormalFormFin S) :
    ∀ k (hkLen : k < (NormalForms.Matrix.Smith.Internal.invariantFactors S).length)
      (hk : k < Nat.min m n),
      (NormalForms.Matrix.Smith.Internal.invariantFactors S).get ⟨k, hkLen⟩ =
        NormalForms.Matrix.Smith.Internal.diagEntry S k hk := by
  induction hS with
  | emptyRows A =>
      intro k hkLen
      simp at hkLen
  | emptyCols A =>
      intro k hkLen
      simp at hkLen
  | zeroLead A hzero hrow hcol hLowerZero =>
      intro k hkLen
      simp [NormalForms.Matrix.Smith.Internal.invariantFactors, hzero] at hkLen
  | pivot A hpivot hnorm hrow hcol hLower hdiv ih =>
      intro k hkLen hk
      cases k with
      | zero =>
          simp [NormalForms.Matrix.Smith.Internal.invariantFactors_pivot hpivot hnorm,
            NormalForms.Matrix.Smith.Internal.diagEntry]
      | succ k =>
          have hkLen' :
              k < (NormalForms.Matrix.Smith.Internal.invariantFactors
                (NormalForms.Matrix.Hermite.lowerRight A)).length := by
            simpa
              [NormalForms.Matrix.Smith.Internal.invariantFactors_pivot hpivot hnorm]
              using hkLen
          have hk' : k < Nat.min _ _ := lt_min_of_succ_lt_min_succ hk
          simpa [NormalForms.Matrix.Smith.Internal.invariantFactors_pivot hpivot hnorm,
            diagEntry_lowerRight (A := A) k hk'] using ih k hkLen' hk'

private theorem pidExecutableInvariantFactorFn_eq_diagEntry {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) (i : Fin (pidExecutableInvariantFactorCount A)) :
    pidExecutableInvariantFactorFn A i =
      NormalForms.Matrix.Smith.Internal.diagEntry (pidExecutableResultFinMatrix A) i.1
        (lt_of_lt_of_le i.is_lt
          (invariantFactors_length_le_min (pidExecutableResultFinMatrix A))) := by
  have hi :
      i.1 <
        (NormalForms.Matrix.Smith.Internal.invariantFactors
          (pidExecutableResultFinMatrix A)).length := by
    change i.1 < pidExecutableInvariantFactorCount A
    exact i.is_lt
  simpa
    [pidExecutableInvariantFactorFn, pidExecutableInvariantFactorCount_eq_internal_length,
      pidExecutableResultFinMatrix, NormalForms.Matrix.Smith.SNFResult.invariantFactors,
      NormalForms.Matrix.Smith.smithInvariantFactors] using
    invariantFactors_get_eq_diagEntry (pidExecutableResultFin_isSmith A) i.1 hi
      (lt_of_lt_of_le i.is_lt (invariantFactors_length_le_min (pidExecutableResultFinMatrix A)))

private theorem smithDiagEntryOrZero_eq_factorFn_of_lt {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) (i : Fin (pidExecutableInvariantFactorCount A)) :
    smithDiagEntryOrZero
        (pidExecutableResultFinMatrix A)
        (splitRowEquiv (pidExecutableInvariantFactorCount_le_card_rows A) (Sum.inl i)) =
      pidExecutableInvariantFactorFn A i := by
  let hkm := pidExecutableInvariantFactorCount_le_card_rows A
  have hiCol : i.1 < Fintype.card n :=
    lt_of_lt_of_le i.is_lt (pidExecutableInvariantFactorCount_le_card_cols A)
  rw [splitRowEquiv_apply_inl_eq_castLE hkm i]
  have hrow :
      (Fin.castLE hkm i : Fin (Fintype.card m)) =
        ⟨i.1, lt_of_lt_of_le i.is_lt hkm⟩ := by
    ext
    rfl
  calc
    smithDiagEntryOrZero (pidExecutableResultFinMatrix A) (Fin.castLE hkm i)
        = NormalForms.Matrix.Smith.Internal.diagEntry (pidExecutableResultFinMatrix A) i.1
            (lt_of_lt_of_le i.is_lt
              (invariantFactors_length_le_min (pidExecutableResultFinMatrix A))) := by
                simp
                  [smithDiagEntryOrZero, hiCol, NormalForms.Matrix.Smith.Internal.diagEntry, hrow]
    _ = pidExecutableInvariantFactorFn A i := (pidExecutableInvariantFactorFn_eq_diagEntry A i).symm

private theorem smithCoordSubmodule_eq_factorSubmodule_of_lt {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) (i : Fin (pidExecutableInvariantFactorCount A)) :
    smithCoordSubmodule
        (pidExecutableResultFinMatrix A)
        (splitRowEquiv (pidExecutableInvariantFactorCount_le_card_rows A) (Sum.inl i)) =
      Ideal.span ({pidExecutableInvariantFactorFn A i} : Set R) := by
  rw [smithCoordSubmodule, smithDiagEntryOrZero_eq_factorFn_of_lt (A := A) i]

private theorem smithDiagEntryOrZero_eq_zero_of_ge {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R)
    (j : Fin (Fintype.card m - pidExecutableInvariantFactorCount A)) :
    smithDiagEntryOrZero
        (pidExecutableResultFinMatrix A)
        (splitRowEquiv (pidExecutableInvariantFactorCount_le_card_rows A) (Sum.inr j)) = 0 := by
  let Sfin := pidExecutableResultFinMatrix A
  let hkm := pidExecutableInvariantFactorCount_le_card_rows A
  let idx := splitRowEquiv hkm (Sum.inr j)
  have hidx : idx.1 = pidExecutableInvariantFactorCount A + j.1 :=
    splitRowEquiv_apply_inr hkm j
  have hlenle :
      (NormalForms.Matrix.Smith.Internal.invariantFactors Sfin).length ≤ idx.1 := by
    rw [← pidExecutableInvariantFactorCount_eq_internal_length (A := A), hidx]
    exact Nat.le_add_right _ _
  by_cases hCol : idx.1 < Fintype.card n
  · have hk : idx.1 < Nat.min (Fintype.card m) (Fintype.card n) := by
      exact lt_min_iff.mpr ⟨idx.is_lt, hCol⟩
    have hzero :=
      diagEntry_eq_zero_of_invariantFactors_length_le
        (pidExecutableResultFin_isSmith A) idx.1 hlenle hk
    rw [smithDiagEntryOrZero, dif_pos hCol]
    simpa [NormalForms.Matrix.Smith.Internal.diagEntry] using hzero
  · rw [smithDiagEntryOrZero, dif_neg hCol]

private theorem smithCoordSubmodule_eq_bot_of_ge {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R)
    (j : Fin (Fintype.card m - pidExecutableInvariantFactorCount A)) :
    smithCoordSubmodule
        (pidExecutableResultFinMatrix A)
        (splitRowEquiv (pidExecutableInvariantFactorCount_le_card_rows A) (Sum.inr j)) =
      ⊥ := by
  rw [smithCoordSubmodule, smithDiagEntryOrZero_eq_zero_of_ge (A := A) j]
  simp

noncomputable def pidExecutableQuotientEquivPiSpanProd {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) :
    ((m → R) ⧸ pidSmithColumnSpan A) ≃ₗ[R]
      (((i : Fin (pidExecutableInvariantFactorCount A)) →
          R ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set R)) ×
        (Fin (Fintype.card m - pidExecutableInvariantFactorCount A) → R)) := by
  let k := pidExecutableInvariantFactorCount A
  let M := Fintype.card m
  let Sfin := pidExecutableResultFinMatrix A
  let hkm : k ≤ M := pidExecutableInvariantFactorCount_le_card_rows A
  let eSplit :
      (∀ i : Fin M, R ⧸ smithCoordSubmodule Sfin i) ≃ₗ[R]
        ((s : Fin k ⊕ Fin (M - k)) →
          R ⧸ smithCoordSubmodule Sfin (splitRowEquiv hkm s)) :=
    (LinearEquiv.piCongrLeft R
      (fun i : Fin M => R ⧸ smithCoordSubmodule Sfin i)
      (splitRowEquiv hkm)).symm
  let eSum :
      ((s : Fin k ⊕ Fin (M - k)) →
        R ⧸ smithCoordSubmodule Sfin (splitRowEquiv hkm s)) ≃ₗ[R]
        (((i : Fin k) →
            R ⧸ smithCoordSubmodule Sfin (splitRowEquiv hkm (Sum.inl i))) ×
          ((j : Fin (M - k)) →
            R ⧸ smithCoordSubmodule Sfin (splitRowEquiv hkm (Sum.inr j)))) :=
    sumPiLequivProdPi
  let eLeft :
      (((i : Fin k) →
          R ⧸ smithCoordSubmodule Sfin (splitRowEquiv hkm (Sum.inl i)))) ≃ₗ[R]
        ((i : Fin k) → R ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set R)) :=
    LinearEquiv.piCongrRight fun i =>
      Submodule.quotEquivOfEq _ _
        (smithCoordSubmodule_eq_factorSubmodule_of_lt A i)
  let eRight :
      (((j : Fin (M - k)) →
          R ⧸ smithCoordSubmodule Sfin (splitRowEquiv hkm (Sum.inr j)))) ≃ₗ[R]
        (Fin (M - k) → R) :=
    LinearEquiv.piCongrRight fun j =>
      Submodule.quotEquivOfEqBot _
        (smithCoordSubmodule_eq_bot_of_ge A j)
  exact (pidExecutableQuotientEquivPiCoords A).trans <|
    eSplit.trans <|
      eSum.trans <|
        LinearEquiv.prodCongr eLeft eRight

noncomputable def pidExecutableQuotientEquivPiZModProd {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) :
    ((m → Int) ⧸ pidSmithColumnSpan A) ≃+
      (((i : Fin (pidExecutableInvariantFactorCount A)) →
          ZMod (pidExecutableInvariantFactorFn A i).natAbs) ×
        (Fin (Fintype.card m - pidExecutableInvariantFactorCount A) → Int)) := by
  let eTors :
      ((i : Fin (pidExecutableInvariantFactorCount A)) →
          Int ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set Int)) ≃+
        ((i : Fin (pidExecutableInvariantFactorCount A)) →
          ZMod (pidExecutableInvariantFactorFn A i).natAbs) :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (pidExecutableInvariantFactorFn A i))
  exact
    (pidExecutableQuotientEquivPiSpanProd A).toAddEquiv.trans <|
      AddEquiv.prodCongr eTors (AddEquiv.refl _)

noncomputable def pidExecutableQuotientEquivPiSpan {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R)
    (hcount : pidExecutableInvariantFactorCount A = Fintype.card m) :
    ((m → R) ⧸ pidSmithColumnSpan A) ≃ₗ[R]
      ((i : Fin (pidExecutableInvariantFactorCount A)) →
        R ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set R)) := by
  let tors :=
    ((i : Fin (pidExecutableInvariantFactorCount A)) →
      R ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set R))
  have hzero : Fintype.card m - (pidExecutableResult A).invariantFactors.length = 0 := by
    rw [← pidExecutableInvariantFactorCount_eq_length (A := A), hcount]
    simp
  have hzeroBase : Fintype.card m - pidExecutableInvariantFactorCount A = 0 := by
    simpa [pidExecutableInvariantFactorCount_eq_length (A := A)] using hzero
  let eFree : (Fin (Fintype.card m - pidExecutableInvariantFactorCount A) → R) ≃ₗ[R] (Fin 0 → R) :=
    LinearEquiv.funCongrLeft R R (finCongr hzeroBase.symm)
  let eTail :
      (tors × (Fin (Fintype.card m - pidExecutableInvariantFactorCount A) → R)) ≃ₗ[R] tors :=
    ((LinearEquiv.prodCongr (LinearEquiv.refl R tors) eFree).trans
      (LinearEquiv.prodUnique (R := R) (M := tors) (M₂ := Fin 0 → R))
  )
  exact (pidExecutableQuotientEquivPiSpanProd A).trans eTail

noncomputable def pidExecutableQuotientEquivPiZMod {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int)
    (hcount : pidExecutableInvariantFactorCount A = Fintype.card m) :
    ((m → Int) ⧸ pidSmithColumnSpan A) ≃+
      ((i : Fin (pidExecutableInvariantFactorCount A)) →
        ZMod (pidExecutableInvariantFactorFn A i).natAbs) := by
  let eTors :
      ((i : Fin (pidExecutableInvariantFactorCount A)) →
          Int ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set Int)) ≃+
        ((i : Fin (pidExecutableInvariantFactorCount A)) →
          ZMod (pidExecutableInvariantFactorFn A i).natAbs) :=
    AddEquiv.piCongrRight fun i => ↑(Int.quotientSpanEquivZMod (pidExecutableInvariantFactorFn A i))
  exact (pidExecutableQuotientEquivPiSpan A hcount).toAddEquiv.trans eTors

noncomputable def pidExecutableQuotientEquivDirectSum {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R)
    (hcount : pidExecutableInvariantFactorCount A = Fintype.card m) :
    ((m → R) ⧸ pidSmithColumnSpan A) ≃ₗ[R]
      ⨁ i : Fin (pidExecutableInvariantFactorCount A),
        R ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set R) := by
  exact
    (pidExecutableQuotientEquivPiSpan A hcount).trans
      (DirectSum.linearEquivFunOnFintype _ _ _).symm

noncomputable def pidFullRankMathlibQuotientEquivExecutable {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R)
    (hfull_mathlib : Module.finrank R (pidSmithColumnSpan A) = Fintype.card m)
    (hcount : pidExecutableInvariantFactorCount A = Fintype.card m) :
    ((i : m) → R ⧸ Ideal.span ({pidFullRankSmithNormalFormCoeffs A hfull_mathlib i} : Set R)) ≃ₗ[R]
      ((i : Fin (pidExecutableInvariantFactorCount A)) →
        R ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set R)) := by
  let b := Pi.basisFun R m
  let hfull' : Module.finrank R (pidSmithColumnSpan A) = Module.finrank R (m → R) := by
    simpa [Module.finrank_eq_card_basis b] using hfull_mathlib
  exact ((pidSmithColumnSpan A).quotientEquivPiSpan b hfull').symm.trans
    (pidExecutableQuotientEquivPiSpan A hcount)

noncomputable def pidFullRankMathlibDirectSumEquivExecutable {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R)
    (hfull_mathlib : Module.finrank R (pidSmithColumnSpan A) = Fintype.card m)
    (hcount : pidExecutableInvariantFactorCount A = Fintype.card m) :
    (⨁ i : m, R ⧸ Ideal.span ({pidFullRankSmithNormalFormCoeffs A hfull_mathlib i} : Set R)) ≃ₗ[R]
      ⨁ i : Fin (pidExecutableInvariantFactorCount A),
        R ⧸ Ideal.span ({pidExecutableInvariantFactorFn A i} : Set R) := by
  let b := Pi.basisFun R m
  let hfull' : Module.finrank R (pidSmithColumnSpan A) = Module.finrank R (m → R) := by
    simpa [Module.finrank_eq_card_basis b] using hfull_mathlib
  exact
    ((Submodule.quotientEquivDirectSum (F := R) b (N := pidSmithColumnSpan A) hfull').symm).trans
      (pidExecutableQuotientEquivDirectSum A hcount)

noncomputable def pidFullRankMathlibPiZModEquivExecutable {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int)
    (hfull_mathlib : Module.finrank Int (pidSmithColumnSpan A) = Fintype.card m)
    (hcount : pidExecutableInvariantFactorCount A = Fintype.card m) :
    ((i : m) → ZMod (pidFullRankSmithNormalFormCoeffs A hfull_mathlib i).natAbs) ≃+
      ((i : Fin (pidExecutableInvariantFactorCount A)) →
        ZMod (pidExecutableInvariantFactorFn A i).natAbs) := by
  let b := Pi.basisFun Int m
  let hfull' : Module.finrank Int (pidSmithColumnSpan A) = Module.finrank Int (m → Int) := by
    simpa [Module.finrank_eq_card_basis b] using hfull_mathlib
  exact ((pidSmithColumnSpan A).quotientEquivPiZMod b hfull').symm.trans
    (pidExecutableQuotientEquivPiZMod A hcount)

end NormalForms.Bridge.MathlibPID
