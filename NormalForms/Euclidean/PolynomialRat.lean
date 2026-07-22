/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Euclidean.ComputableOps
public import Mathlib.Algebra.Polynomial.FieldDivision
public import NormalForms.Euclidean.Rat

/-!
# Constructive Euclidean operations for rational polynomials

Mathlib's polynomial theory is intentionally noncomputable over an arbitrary
coefficient semiring.  This module supplies a rational-coefficient runtime
implementation and proves every operation equal to the standard polynomial
semantics.
-/

namespace NormalForms

namespace PolynomialRatRuntime

open Polynomial

@[implicit_reducible] private def cleanFieldRat : Field Rat :=
  ConstructiveRat.field
@[implicit_reducible] private def cleanCommRingRat : CommRing Rat :=
  cleanFieldRat.toCommRing
@[implicit_reducible] private def cleanRingRat : Ring Rat :=
  cleanCommRingRat.toRing
@[implicit_reducible] private def cleanCommSemiringRat : CommSemiring Rat :=
  cleanCommRingRat.toCommSemiring
@[implicit_reducible] public def cleanSemiringRat : Semiring Rat :=
  cleanCommSemiringRat.toSemiring
@[implicit_reducible] private def cleanDivisionRingRat : DivisionRing Rat :=
  cleanFieldRat.toDivisionRing
@[implicit_reducible] private def cleanCommGroupWithZeroRat :
    CommGroupWithZero Rat where
  mul := cleanFieldRat.mul
  mul_assoc := cleanFieldRat.mul_assoc
  one := cleanFieldRat.one
  one_mul := cleanFieldRat.one_mul
  mul_one := cleanFieldRat.mul_one
  npow := cleanFieldRat.npow
  npow_zero := cleanFieldRat.npow_zero
  npow_succ := cleanFieldRat.npow_succ
  mul_comm := cleanFieldRat.mul_comm
  zero := cleanFieldRat.zero
  zero_mul := cleanFieldRat.zero_mul
  mul_zero := cleanFieldRat.mul_zero
  inv := cleanFieldRat.inv
  div := cleanFieldRat.div
  zpow := cleanFieldRat.zpow
  div_eq_mul_inv := cleanFieldRat.div_eq_mul_inv
  zpow_zero' := cleanFieldRat.zpow_zero'
  zpow_succ' := cleanFieldRat.zpow_succ'
  zpow_neg' := cleanFieldRat.zpow_neg'
  exists_pair_ne := cleanFieldRat.exists_pair_ne
  inv_zero := cleanFieldRat.inv_zero
  mul_inv_cancel := cleanFieldRat.mul_inv_cancel

/-- Rational polynomials whose hidden semiring parameter is choice-free. -/
public abbrev RuntimePolynomial :=
  @Polynomial Rat cleanSemiringRat

local instance (priority := 3000) : Field Rat := cleanFieldRat
local instance (priority := 3001) : CommGroupWithZero Rat :=
  cleanCommGroupWithZeroRat
local instance (priority := 3001) : CommRing Rat := cleanCommRingRat
local instance (priority := 3001) : Ring Rat := cleanRingRat
local instance (priority := 3001) : CommSemiring Rat :=
  cleanCommSemiringRat
local instance (priority := 3001) : Semiring Rat := cleanSemiringRat
local instance (priority := 3001) : DivisionRing Rat :=
  cleanDivisionRingRat
local instance (priority := 3001) : AddCommGroup Rat :=
  cleanCommRingRat.toAddCommGroup
local instance (priority := 3001) : AddGroup Rat :=
  cleanCommRingRat.toAddCommGroup.toAddGroup
local instance (priority := 3001) : AddCommMonoid Rat :=
  cleanCommRingRat.toAddCommGroup.toAddCommMonoid
local instance (priority := 3001) : AddMonoid Rat :=
  cleanCommRingRat.toAddCommGroup.toAddCommMonoid.toAddMonoid
local instance (priority := 3001) : CommMonoid Rat :=
  cleanCommSemiringRat.toCommMonoid
local instance (priority := 3001) : Monoid Rat :=
  cleanCommSemiringRat.toCommMonoid.toMonoid
local instance (priority := 3002) : Zero Rat := cleanSemiringRat.toZero
local instance (priority := 3002) : One Rat := cleanSemiringRat.toOne
local instance (priority := 3002) : Add Rat := cleanSemiringRat.toAdd
local instance (priority := 3002) : Mul Rat := cleanSemiringRat.toMul
local instance (priority := 3002) : NSMul Rat := cleanSemiringRat.toNSMul
local instance (priority := 3002) : NPow Rat := cleanSemiringRat.toNPow
local instance (priority := 3002) : NatCast Rat :=
  cleanSemiringRat.toNatCast
local instance (priority := 3002) : Neg Rat := cleanRingRat.toNeg
local instance (priority := 3002) : Sub Rat := cleanRingRat.toSub
local instance (priority := 3002) : ZSMul Rat := cleanRingRat.toZSMul
local instance (priority := 3002) : IntCast Rat :=
  cleanRingRat.toIntCast
local instance (priority := 3002) : Inv Rat :=
  cleanDivisionRingRat.toInv
local instance (priority := 3002) : Div Rat :=
  cleanDivisionRingRat.toDiv
local instance (priority := 3002) : ZPow Rat :=
  cleanDivisionRingRat.toZPow
local instance (priority := 3002) : NNRatCast Rat :=
  cleanDivisionRingRat.toNNRatCast
local instance (priority := 3002) : RatCast Rat :=
  cleanDivisionRingRat.toRatCast
local instance (priority := 3002) : Pow Rat Nat :=
  @NPow.toPow Rat cleanSemiringRat.toNPow
local instance (priority := 3002) : Pow Rat Int :=
  @ZPow.toPow Rat cleanDivisionRingRat.toZPow
@[implicit_reducible] local instance (priority := 3003) : OfNat Rat 0 :=
  @Zero.toOfNat0 Rat cleanSemiringRat.toZero
@[implicit_reducible] local instance (priority := 3003) : OfNat Rat 1 :=
  @One.toOfNat1 Rat cleanSemiringRat.toOne

private theorem rat_mul_ne_zero_runtime {a b : Rat}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro hab
  apply ha
  calc
    a = a * 1 := (cleanFieldRat.mul_one a).symm
    _ = a * (b * b⁻¹) := by
      rw [cleanFieldRat.mul_inv_cancel b hb]
    _ = (a * b) * b⁻¹ :=
      (cleanFieldRat.mul_assoc a b b⁻¹).symm
    _ = 0 * b⁻¹ := congrArg (fun x => x * b⁻¹) hab
    _ = 0 := cleanFieldRat.zero_mul _

private theorem rat_inv_one_runtime : (1 : Rat)⁻¹ = 1 := by
  calc
    (1 : Rat)⁻¹ = 1 * (1 : Rat)⁻¹ :=
      (cleanFieldRat.one_mul _).symm
    _ = 1 := cleanFieldRat.mul_inv_cancel 1 one_ne_zero

private theorem rat_inv_mul_runtime (a b : Rat) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  cases decEq a 0 with
  | isTrue ha =>
      subst a
      rw [cleanFieldRat.zero_mul, cleanFieldRat.inv_zero,
        cleanFieldRat.mul_zero]
  | isFalse ha =>
      cases decEq b 0 with
      | isTrue hb =>
          subst b
          rw [cleanFieldRat.mul_zero, cleanFieldRat.inv_zero,
            cleanFieldRat.zero_mul]
      | isFalse hb =>
          have hab : a * b ≠ 0 :=
            rat_mul_ne_zero_runtime ha hb
          have hright : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
            calc
              (a * b) * (b⁻¹ * a⁻¹) =
                  a * (b * (b⁻¹ * a⁻¹)) :=
                    cleanFieldRat.mul_assoc _ _ _
              _ = a * ((b * b⁻¹) * a⁻¹) := by
                rw [cleanFieldRat.mul_assoc b b⁻¹ a⁻¹]
              _ = a * (a⁻¹ * (b * b⁻¹)) := by
                rw [cleanFieldRat.mul_comm (b * b⁻¹) a⁻¹]
              _ = (a * a⁻¹) * (b * b⁻¹) :=
                (cleanFieldRat.mul_assoc _ _ _).symm
              _ = 1 := by
                rw [cleanFieldRat.mul_inv_cancel a ha,
                  cleanFieldRat.mul_inv_cancel b hb,
                  cleanFieldRat.one_mul]
          calc
            (a * b)⁻¹ = (a * b)⁻¹ * 1 :=
              (cleanFieldRat.mul_one _).symm
            _ = (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) := by
              rw [hright]
            _ = ((a * b)⁻¹ * (a * b)) * (b⁻¹ * a⁻¹) :=
              (cleanFieldRat.mul_assoc _ _ _).symm
            _ = ((a * b) * (a * b)⁻¹) * (b⁻¹ * a⁻¹) := by
              rw [cleanFieldRat.mul_comm (a * b)⁻¹ (a * b)]
            _ = b⁻¹ * a⁻¹ := by
              rw [cleanFieldRat.mul_inv_cancel (a * b) hab,
                cleanFieldRat.one_mul]

private def rawCoeff (p : RuntimePolynomial) (n : Nat) : Rat :=
  p.toFinsupp.coeff.toFun n

private def rawSupport (p : RuntimePolynomial) : Finset Nat :=
  p.toFinsupp.coeff.support

private def supportMax (s : Finset Nat) : Nat :=
  Finset.fold Nat.max 0 id s

private def natRangeData :
    (n : Nat) → {s : Finset Nat // ∀ k, k ∈ s ↔ k < n}
  | 0 => ⟨∅, by
      intro k
      constructor
      · intro hk
        exact False.elim (Finset.notMem_empty k hk)
      · intro hk
        exact False.elim (Nat.not_lt_zero k hk)⟩
  | n + 1 =>
      let prev := natRangeData n
      have hn : n ∉ prev.1 := by
        intro hmem
        exact Nat.lt_irrefl n ((prev.2 n).1 hmem)
      ⟨prev.1.cons n hn, by
        intro k
        constructor
        · intro hk
          rcases Finset.mem_cons.mp hk with hkn | hk
          · rw [hkn]
            exact Nat.lt_succ_self n
          · exact Nat.lt_trans ((prev.2 k).1 hk) (Nat.lt_succ_self n)
        · intro hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hkn
          · exact Finset.mem_cons_of_mem ((prev.2 k).2 hk)
          · rw [hkn]
            exact Finset.mem_cons_self n prev.1⟩

private def natRange (n : Nat) : Finset Nat :=
  (natRangeData n).1

private theorem mem_natRange {n k : Nat} :
    k ∈ natRange n ↔ k < n :=
  (natRangeData n).2 k

private theorem supportMax_le {s : Finset Nat} {k : Nat} :
    supportMax s ≤ k ↔ ∀ n ∈ s, n ≤ k := by
  induction s using Finset.induction with
  | empty => simp [supportMax]
  | @insert a s ha ih =>
      rw [supportMax, Finset.fold_insert ha, Nat.max_le]
      change a ≤ k ∧ supportMax s ≤ k ↔ ∀ n ∈ insert a s, n ≤ k
      rw [ih]
      simp only [Finset.mem_insert, forall_eq_or_imp]

private theorem supportMax_mem {s : Finset Nat} (hs : s.Nonempty) :
    supportMax s ∈ s := by
  induction s using Finset.induction with
  | empty =>
      rcases hs with ⟨n, hn⟩
      simp at hn
  | @insert a s ha ih =>
      rw [supportMax, Finset.fold_insert ha]
      change max a (supportMax s) ∈ insert a s
      by_cases hs' : s.Nonempty
      · by_cases hle : a ≤ supportMax s
        · rw [max_eq_right hle]
          exact Finset.mem_insert_of_mem (ih hs')
        · rw [max_eq_left (Nat.le_of_not_ge hle)]
          exact Finset.mem_insert_self a s
      · have hzero : supportMax s = 0 := by
          apply Nat.eq_zero_of_le_zero
          exact supportMax_le.mpr fun n hn => False.elim (hs' ⟨n, hn⟩)
        rw [hzero, max_eq_left (Nat.zero_le a)]
        exact Finset.mem_insert_self a s

@[simp] private theorem rawCoeff_eq_coeff (p : RuntimePolynomial) (n : Nat) :
    rawCoeff p n = p.coeff n :=
  Polynomial.toFinsupp_apply p n

public def natDegree (p : RuntimePolynomial) : Nat :=
  supportMax (rawSupport p)

public def leadingCoeff (p : RuntimePolynomial) : Rat :=
  rawCoeff p (natDegree p)

public def isZeroB (p : RuntimePolynomial) : Bool :=
  decide ((rawSupport p).card = 0)

theorem natDegree_eq (p : RuntimePolynomial) :
    natDegree p = p.natDegree := by
  by_cases hs : rawSupport p = ∅
  · have hpSupport : p.support = ∅ := by
      rw [← show rawSupport p = p.support by
        exact Polynomial.support_toFinsupp p]
      exact hs
    rw [natDegree, hs]
    change 0 = p.natDegree
    rw [Polynomial.natDegree, Polynomial.degree, hpSupport]
    rfl
  · have hsne : (rawSupport p).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hs
    have hmax : supportMax (rawSupport p) = (rawSupport p).max' hsne := by
      apply le_antisymm
      · exact (rawSupport p).le_max' _ (supportMax_mem hsne)
      · exact (rawSupport p).max'_le hsne _ <|
          supportMax_le.mp (Nat.le_refl _)
    rw [natDegree, hmax, Polynomial.natDegree, Polynomial.degree]
    change (rawSupport p).max' hsne =
      WithBot.unbotD 0 (rawSupport p).max
    rw [← Finset.coe_max' hsne]
    rfl

theorem leadingCoeff_eq (p : RuntimePolynomial) :
    leadingCoeff p = p.leadingCoeff := by
  rw [leadingCoeff, Polynomial.leadingCoeff, natDegree_eq,
    rawCoeff_eq_coeff]

private def finsuppOfCandidates (s : Finset Nat) (f : Nat → Rat)
    (hf : ∀ n, f n ≠ 0 → n ∈ s) : Nat →₀ Rat where
  support := s.filter fun n => decide (f n ≠ 0)
  toFun := f
  mem_support_toFun := by
    intro n
    simp only [Finset.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hf n h, h⟩⟩

private def ofCoeffs (s : Finset Nat) (f : Nat → Rat)
    (hf : ∀ n, f n ≠ 0 → n ∈ s) : RuntimePolynomial :=
  .ofFinsupp (.ofCoeff (finsuppOfCandidates s f hf))

public def zero : RuntimePolynomial :=
  ofCoeffs ∅ (fun _ => 0) (by simp)

@[simp] theorem isZeroB_eq_true_iff (p : RuntimePolynomial) :
    isZeroB p = true ↔ p = zero := by
  rw [isZeroB, decide_eq_true_eq, Finset.card_eq_zero]
  constructor
  · intro h
    apply Polynomial.coeff_injective
    funext n
    have hn : n ∉ rawSupport p := by
      rw [h]
      simp
    have hp : rawCoeff p n = 0 := by
      cases decEq (rawCoeff p n) 0 with
      | isTrue hzero => exact hzero
      | isFalse hne =>
          exact False.elim (hn (Finsupp.mem_support_iff.mpr hne))
    rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, hp]
    rfl
  · intro h
    subst p
    rfl

private theorem rawSupport_nonempty {p : RuntimePolynomial} (hp : p ≠ zero) :
    (rawSupport p).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hs
  apply hp
  apply (isZeroB_eq_true_iff p).mp
  rw [isZeroB, decide_eq_true_eq, Finset.card_eq_zero]
  exact hs

private theorem natDegree_mem_rawSupport {p : RuntimePolynomial} (hp : p ≠ zero) :
    natDegree p ∈ rawSupport p := by
  unfold natDegree
  exact supportMax_mem (rawSupport_nonempty hp)

private theorem leadingCoeff_ne_zero_runtime {p : RuntimePolynomial} (hp : p ≠ zero) :
    leadingCoeff p ≠ 0 := by
  unfold leadingCoeff
  exact Finsupp.mem_support_iff.mp (natDegree_mem_rawSupport hp)

private theorem rawCoeff_eq_zero_of_natDegree_lt
    (p : RuntimePolynomial) {n : Nat} (hdeg : natDegree p < n) :
    rawCoeff p n = 0 := by
  by_contra hn
  have hmem : n ∈ rawSupport p :=
    Finsupp.mem_support_iff.mpr hn
  have hle : n ≤ natDegree p :=
    supportMax_le.mp (Nat.le_refl _) n hmem
  exact (Nat.not_le_of_lt hdeg) hle

public def one : RuntimePolynomial :=
  ofCoeffs {0} (fun n => if n = 0 then 1 else 0) (by
    intro n hn
    by_cases h : n = 0
    · simp [h]
    · exact False.elim (hn (by simp [h])))

public def C (a : Rat) : RuntimePolynomial :=
  ofCoeffs {0} (fun n => if n = 0 then a else 0) (by
    intro n hn
    by_cases h : n = 0
    · simp [h]
    · exact False.elim (hn (by simp [h])))

public def X : RuntimePolynomial :=
  ofCoeffs {1} (fun n => if n = 1 then 1 else 0) (by
    intro n hn
    by_cases h : n = 1
    · simp [h]
    · exact False.elim (hn (by simp [h])))

@[simp] private theorem rawCoeff_zero (n : Nat) :
    rawCoeff zero n = 0 :=
  rfl

@[simp] private theorem rawCoeff_one (n : Nat) :
    rawCoeff one n = if n = 0 then 1 else 0 :=
  rfl

@[simp] private theorem rawCoeff_C (a : Rat) (n : Nat) :
    rawCoeff (C a) n = if n = 0 then a else 0 :=
  rfl

private def scale (p : RuntimePolynomial) (a : Rat) : RuntimePolynomial :=
  ofCoeffs (rawSupport p) (fun n => rawCoeff p n * a) (by
    intro n hn
    apply Finsupp.mem_support_iff.mpr
    intro hp
    change rawCoeff p n = 0 at hp
    exact hn (by rw [hp, zero_mul]))

@[simp] private theorem rawCoeff_scale (p : RuntimePolynomial) (a : Rat) (n : Nat) :
    rawCoeff (scale p a) n = rawCoeff p n * a :=
  rfl

private theorem rawSupport_scale {p : RuntimePolynomial} {a : Rat} (ha : a ≠ 0) :
    rawSupport (scale p a) = rawSupport p := by
  apply Finset.ext
  intro n
  change
    n ∈ (scale p a).toFinsupp.coeff.support ↔
      n ∈ p.toFinsupp.coeff.support
  rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  change rawCoeff (scale p a) n ≠ 0 ↔ rawCoeff p n ≠ 0
  rw [rawCoeff_scale]
  exact ⟨fun h hp => h (by rw [hp, zero_mul]),
    fun hp => rat_mul_ne_zero_runtime hp ha⟩

private theorem natDegree_scale {p : RuntimePolynomial} {a : Rat} (ha : a ≠ 0) :
    natDegree (scale p a) = natDegree p := by
  unfold natDegree
  rw [rawSupport_scale ha]

private theorem leadingCoeff_scale {p : RuntimePolynomial} {a : Rat} (ha : a ≠ 0) :
    leadingCoeff (scale p a) = leadingCoeff p * a := by
  unfold leadingCoeff
  rw [natDegree_scale ha, rawCoeff_scale]

private def monomial (a : Rat) (d : Nat) : RuntimePolynomial :=
  ofCoeffs {d} (fun n => if n = d then a else 0) (by
    intro n hn
    by_cases h : n = d
    · simp [h]
    · exact False.elim (hn (by simp [h])))

@[simp] private theorem rawCoeff_monomial (a : Rat) (d n : Nat) :
    rawCoeff (monomial a d) n = if n = d then a else 0 :=
  rfl

private theorem rawSupport_monomial {a : Rat} (ha : a ≠ 0) (d : Nat) :
    rawSupport (monomial a d) = {d} := by
  apply Finset.ext
  intro n
  change
    n ∈ (monomial a d).toFinsupp.coeff.support ↔
      n ∈ ({d} : Finset Nat)
  rw [Finsupp.mem_support_iff]
  change (if n = d then a else 0) ≠ 0 ↔ n ∈ ({d} : Finset Nat)
  by_cases h : n = d <;> simp [h, ha]

private theorem natDegree_monomial {a : Rat} (ha : a ≠ 0) (d : Nat) :
    natDegree (monomial a d) = d := by
  unfold natDegree
  rw [rawSupport_monomial ha]
  simp [supportMax]

private theorem leadingCoeff_monomial {a : Rat} (ha : a ≠ 0) (d : Nat) :
    leadingCoeff (monomial a d) = a := by
  unfold leadingCoeff
  rw [natDegree_monomial ha, rawCoeff_monomial]
  simp

public def add (p q : RuntimePolynomial) : RuntimePolynomial :=
  ofCoeffs (natRange (max (natDegree p) (natDegree q) + 1))
    (fun n => rawCoeff p n + rawCoeff q n) (by
      intro n hn
      apply mem_natRange.mpr
      apply Nat.lt_of_not_ge
      intro hbound
      have hp : rawCoeff p n = 0 :=
        rawCoeff_eq_zero_of_natDegree_lt p (by omega)
      have hq : rawCoeff q n = 0 :=
        rawCoeff_eq_zero_of_natDegree_lt q (by omega)
      apply hn
      rw [hp, hq]
      exact cleanCommRingRat.add_zero 0)

public def neg (p : RuntimePolynomial) : RuntimePolynomial :=
  ofCoeffs (rawSupport p) (fun n => -rawCoeff p n) (by
      intro n hn
      apply Finsupp.mem_support_iff.mpr
      intro hp
      exact hn (neg_eq_zero.mpr hp))

private theorem nodup_range_runtime :
    ∀ n : Nat, (List.range n).Nodup
  | 0 => .nil
  | n + 1 => by
      rw [List.range_succ_eq_map]
      apply List.Nodup.cons
      · intro hmem
        rcases List.mem_map.mp hmem with ⟨k, _, hk⟩
        exact Nat.noConfusion hk
      · exact (nodup_range_runtime n).map Nat.succ_injective

private theorem nodup_antidiagonal_runtime (n : Nat) :
    (List.Nat.antidiagonal n).Nodup := by
  unfold List.Nat.antidiagonal
  exact (nodup_range_runtime (n + 1)).map fun _ _ h =>
    (Prod.mk.inj h).1

private theorem mem_antidiagonal_runtime {n : Nat} {ij : Nat × Nat} :
    ij ∈ List.Nat.antidiagonal n ↔ ij.1 + ij.2 = n := by
  rcases ij with ⟨i, j⟩
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨k, hk, hpair⟩
    have hklt : k < n + 1 := List.mem_range.mp hk
    have hi : k = i := congrArg Prod.fst hpair
    have hj : n - k = j := congrArg Prod.snd hpair
    omega
  · intro hsum
    apply List.mem_map.mpr
    refine ⟨i, List.mem_range.mpr (by omega), ?_⟩
    apply Prod.ext
    · rfl
    · omega

private theorem list_sum_eq_single_of_eq_zero_except
    (l : List (Nat × Nat)) (f : Nat × Nat → Rat) (a : Nat × Nat)
    (ha : a ∈ l) (hnodup : l.Nodup)
    (hzero : ∀ x ∈ l, x ≠ a → f x = 0) :
    (l.map f).sum = f a := by
  induction l with
  | nil =>
      exact False.elim (List.not_mem_nil ha)
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons]
      have hnodup' := List.nodup_cons.mp hnodup
      cases decEq x a with
      | isTrue hxa =>
        subst x
        have htail : (xs.map f).sum = 0 := by
          apply List.sum_eq_zero
          intro z hz
          rcases List.mem_map.mp hz with ⟨y, hy, rfl⟩
          apply hzero y (List.mem_cons_of_mem a hy)
          intro hya
          subst y
          exact hnodup'.1 hy
        rw [htail]
        exact cleanCommRingRat.add_zero _
      | isFalse hxa =>
        have haTail : a ∈ xs :=
          (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
        have hxzero : f x = 0 :=
          hzero x List.mem_cons_self hxa
        rw [hxzero, cleanCommRingRat.zero_add]
        apply ih haTail hnodup'.2
        intro y hy hya
        exact hzero y (List.mem_cons_of_mem x hy) hya

private theorem list_sum_append_runtime (xs ys : List Rat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil =>
      exact (cleanCommRingRat.zero_add ys.sum).symm
  | cons x xs ih =>
      change x + (xs ++ ys).sum = (x + xs.sum) + ys.sum
      rw [ih]
      exact (cleanCommRingRat.add_assoc x xs.sum ys.sum).symm

private theorem list_sum_flatten_runtime :
    ∀ xss : List (List Rat),
      xss.flatten.sum = (xss.map List.sum).sum
  | [] => rfl
  | xs :: xss => by
      change (xs ++ xss.flatten).sum =
        xs.sum + (xss.map List.sum).sum
      rw [list_sum_append_runtime, list_sum_flatten_runtime xss]

private def mulCoeff (p q : RuntimePolynomial) (n : Nat) : Rat :=
  ((List.Nat.antidiagonal n).map fun ij =>
    rawCoeff p ij.1 * rawCoeff q ij.2).sum

private theorem mulCoeff_eq_zero_of_natDegree_add_lt
    (p q : RuntimePolynomial) {n : Nat}
    (hdeg : natDegree p + natDegree q < n) :
    mulCoeff p q n = 0 := by
  unfold mulCoeff
  apply List.sum_eq_zero
  intro x hx
  rcases List.mem_map.mp hx with ⟨ij, hij, rfl⟩
  have hsum : ij.1 + ij.2 = n :=
    mem_antidiagonal_runtime.mp hij
  by_cases hp : natDegree p < ij.1
  · rw [rawCoeff_eq_zero_of_natDegree_lt p hp,
      cleanCommRingRat.zero_mul]
  · have hq : natDegree q < ij.2 := by omega
    rw [rawCoeff_eq_zero_of_natDegree_lt q hq,
      cleanCommRingRat.mul_zero]

public def mul (p q : RuntimePolynomial) : RuntimePolynomial :=
  ofCoeffs (natRange (natDegree p + natDegree q + 1)) (mulCoeff p q) (by
    intro n hn
    apply mem_natRange.mpr
    apply Nat.lt_of_not_ge
    intro hbound
    apply hn
    exact mulCoeff_eq_zero_of_natDegree_add_lt p q (by omega))

@[simp] private theorem rawCoeff_mul (p q : RuntimePolynomial) (n : Nat) :
    rawCoeff (mul p q) n = mulCoeff p q n :=
  rfl

private theorem rawCoeff_mul_monomial
    (p : RuntimePolynomial) (a : Rat) (d n : Nat) :
    rawCoeff (mul p (monomial a d)) n =
      if d ≤ n then rawCoeff p (n - d) * a else 0 := by
  rw [rawCoeff_mul]
  unfold mulCoeff
  by_cases hd : d ≤ n
  · rw [if_pos hd]
    rw [list_sum_eq_single_of_eq_zero_except
      (List.Nat.antidiagonal n)
      (fun ij => rawCoeff p ij.1 * rawCoeff (monomial a d) ij.2)
      (n - d, d)]
    · rw [rawCoeff_monomial, if_pos rfl]
    · apply mem_antidiagonal_runtime.mpr
      exact Nat.sub_add_cancel hd
    · exact nodup_antidiagonal_runtime n
    · intro ij hij hne
      have hsum : ij.1 + ij.2 = n :=
        mem_antidiagonal_runtime.mp hij
      by_cases hj : ij.2 = d
      · have hi : ij.1 = n - d := by omega
        exact False.elim (hne (Prod.ext hi hj))
      · rw [rawCoeff_monomial, if_neg hj,
          cleanCommRingRat.mul_zero]
  · rw [if_neg hd]
    apply List.sum_eq_zero
    intro x hx
    rcases List.mem_map.mp hx with ⟨ij, hij, rfl⟩
    have hsum : ij.1 + ij.2 = n :=
      mem_antidiagonal_runtime.mp hij
    have hj : ij.2 ≠ d := by
      intro h
      rw [h] at hsum
      exact hd (Nat.le_of_add_left_le hsum.le)
    rw [rawCoeff_monomial, if_neg hj,
      cleanCommRingRat.mul_zero]

private theorem mul_C_runtime (p : RuntimePolynomial) (a : Rat) :
    mul p (C a) = scale p a := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff]
  change
    rawCoeff (mul p (monomial a 0)) n =
      rawCoeff (scale p a) n
  rw [rawCoeff_mul_monomial, rawCoeff_scale]
  simp

@[simp] private theorem rawCoeff_add (p q : RuntimePolynomial) (n : Nat) :
    rawCoeff (add p q) n = rawCoeff p n + rawCoeff q n :=
  rfl

private theorem add_zero_runtime (p : RuntimePolynomial) :
    add p zero = p := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_add]
  change rawCoeff p n + 0 = rawCoeff p n
  exact add_zero _

private theorem zero_add_runtime (p : RuntimePolynomial) :
    add zero p = p := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_add]
  change 0 + rawCoeff p n = rawCoeff p n
  exact zero_add _

private theorem mul_zero_runtime (p : RuntimePolynomial) :
    mul p zero = zero := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_mul,
    rawCoeff_zero]
  unfold mulCoeff
  apply List.sum_eq_zero
  intro x hx
  rcases List.mem_map.mp hx with ⟨ij, _, rfl⟩
  change rawCoeff p ij.1 * 0 = 0
  exact cleanCommRingRat.mul_zero _

private theorem zero_mul_runtime (p : RuntimePolynomial) :
    mul zero p = zero := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_mul,
    rawCoeff_zero]
  unfold mulCoeff
  apply List.sum_eq_zero
  intro x hx
  rcases List.mem_map.mp hx with ⟨ij, _, rfl⟩
  change 0 * rawCoeff p ij.2 = 0
  exact cleanCommRingRat.zero_mul _

public def sub (p q : RuntimePolynomial) : RuntimePolynomial :=
  add p (neg q)

@[simp] private theorem rawCoeff_neg (p : RuntimePolynomial) (n : Nat) :
    rawCoeff (neg p) n = -rawCoeff p n :=
  rfl

private theorem neg_add_cancel_runtime (p : RuntimePolynomial) :
    add (neg p) p = zero := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_add,
    rawCoeff_neg, rawCoeff_zero]
  exact neg_add_cancel _

@[simp] private theorem rawCoeff_sub (p q : RuntimePolynomial) (n : Nat) :
    rawCoeff (sub p q) n = rawCoeff p n - rawCoeff q n := by
  rw [sub, rawCoeff_add, rawCoeff_neg, sub_eq_add_neg]

private theorem rawCoeff_mul_natDegree_add
    (p q : RuntimePolynomial) :
    rawCoeff (mul p q) (natDegree p + natDegree q) =
      leadingCoeff p * leadingCoeff q := by
  rw [rawCoeff_mul]
  unfold mulCoeff
  rw [list_sum_eq_single_of_eq_zero_except
    (List.Nat.antidiagonal (natDegree p + natDegree q))
    (fun ij => rawCoeff p ij.1 * rawCoeff q ij.2)
    (natDegree p, natDegree q)]
  · rfl
  · exact mem_antidiagonal_runtime.mpr rfl
  · exact nodup_antidiagonal_runtime _
  · intro ij hij hne
    have hsum :
        ij.1 + ij.2 = natDegree p + natDegree q :=
      mem_antidiagonal_runtime.mp hij
    by_cases hi : ij.1 ≤ natDegree p
    · by_cases hj : ij.2 ≤ natDegree q
      · have hei : ij.1 = natDegree p := by omega
        have hej : ij.2 = natDegree q := by omega
        exact False.elim (hne (Prod.ext hei hej))
      · rw [rawCoeff_eq_zero_of_natDegree_lt q
            (Nat.lt_of_not_ge hj),
          cleanCommRingRat.mul_zero]
    · rw [rawCoeff_eq_zero_of_natDegree_lt p
          (Nat.lt_of_not_ge hi),
        cleanCommRingRat.zero_mul]

private theorem rawSupport_mul_le (p q : RuntimePolynomial) {n : Nat}
    (hn : n ∈ rawSupport (mul p q)) :
    n ≤ natDegree p + natDegree q := by
  apply Nat.le_of_not_gt
  intro hgt
  have hcoeff : rawCoeff (mul p q) n ≠ 0 :=
    Finsupp.mem_support_iff.mp hn
  apply hcoeff
  rw [rawCoeff_mul]
  exact mulCoeff_eq_zero_of_natDegree_add_lt p q hgt

private theorem natDegree_mul_runtime
    {p q : RuntimePolynomial} (hp : p ≠ zero) (hq : q ≠ zero) :
    natDegree (mul p q) = natDegree p + natDegree q := by
  have hupper :
      natDegree (mul p q) ≤ natDegree p + natDegree q := by
    unfold natDegree
    apply supportMax_le.mpr
    intro n hn
    exact rawSupport_mul_le p q hn
  have hcoeff :
      rawCoeff (mul p q) (natDegree p + natDegree q) ≠ 0 := by
    rw [rawCoeff_mul_natDegree_add]
    exact rat_mul_ne_zero_runtime
      (leadingCoeff_ne_zero_runtime hp)
      (leadingCoeff_ne_zero_runtime hq)
  have hmem :
      natDegree p + natDegree q ∈ rawSupport (mul p q) :=
    Finsupp.mem_support_iff.mpr hcoeff
  have hlower :
      natDegree p + natDegree q ≤ natDegree (mul p q) := by
    unfold natDegree
    exact supportMax_le.mp (Nat.le_refl _) _ hmem
  exact Nat.le_antisymm hupper hlower

private theorem mul_ne_zero_runtime
    {p q : RuntimePolynomial} (hp : p ≠ zero) (hq : q ≠ zero) :
    mul p q ≠ zero := by
  intro hzero
  have hcoeff :
      rawCoeff (mul p q) (natDegree p + natDegree q) ≠ 0 := by
    rw [rawCoeff_mul_natDegree_add]
    exact rat_mul_ne_zero_runtime
      (leadingCoeff_ne_zero_runtime hp)
      (leadingCoeff_ne_zero_runtime hq)
  apply hcoeff
  rw [hzero, rawCoeff_zero]

private theorem leadingCoeff_mul_runtime
    {p q : RuntimePolynomial} (hp : p ≠ zero) (hq : q ≠ zero) :
    leadingCoeff (mul p q) = leadingCoeff p * leadingCoeff q := by
  unfold leadingCoeff
  rw [natDegree_mul_runtime hp hq, rawCoeff_mul_natDegree_add]
  rfl

private theorem natDegree_lt_of_coeff_zero_ge
    {p : RuntimePolynomial} {d : Nat} (hp : p ≠ zero)
    (hzero : ∀ n, d ≤ n → rawCoeff p n = 0) :
    natDegree p < d := by
  apply Nat.lt_of_not_ge
  intro h
  exact leadingCoeff_ne_zero_runtime hp (hzero (natDegree p) h)

private def IsMonicRuntime (p : RuntimePolynomial) : Prop :=
  leadingCoeff p = 1

private theorem leadingCoeff_zero : leadingCoeff zero = 0 :=
  rfl

private theorem IsMonicRuntime.ne_zero {p : RuntimePolynomial}
    (hp : IsMonicRuntime p) : p ≠ zero := by
  intro h
  subst p
  exact zero_ne_one (leadingCoeff_zero.trans hp)

public def pow : Nat → RuntimePolynomial → RuntimePolynomial
  | 0, _ => one
  | n + 1, p => mul (pow n p) p

def nsmul : Nat → RuntimePolynomial → RuntimePolynomial
  | 0, _ => zero
  | n + 1, p => add (nsmul n p) p

def zsmul : Int → RuntimePolynomial → RuntimePolynomial
  | .ofNat n, p => nsmul n p
  | .negSucc n, p => neg (nsmul (n + 1) p)

def natCast (n : Nat) : RuntimePolynomial :=
  C n

def intCast (z : Int) : RuntimePolynomial :=
  C z

theorem zero_eq : zero = (0 : RuntimePolynomial) := by
  apply Polynomial.coeff_injective
  funext n
  rfl

theorem one_eq : one = (1 : RuntimePolynomial) := by
  apply Polynomial.coeff_injective
  funext n
  simp [one, ofCoeffs, finsuppOfCandidates, Polynomial.coeff_one]

theorem C_eq (a : Rat) : C a = Polynomial.C a := by
  apply Polynomial.coeff_injective
  funext n
  simp [C, ofCoeffs, finsuppOfCandidates, Polynomial.coeff_C]

theorem X_eq : X = (Polynomial.X : RuntimePolynomial) := by
  apply Polynomial.coeff_injective
  funext n
  simp [X, ofCoeffs, finsuppOfCandidates, Polynomial.coeff_X, eq_comm]

theorem add_eq (p q : RuntimePolynomial) : add p q = p + q := by
  apply Polynomial.coeff_injective
  funext n
  simp [add, ofCoeffs, finsuppOfCandidates,
    Polynomial.coeff_add]

theorem neg_eq (p : RuntimePolynomial) : neg p = -p := by
  apply Polynomial.coeff_injective
  funext n
  simp [neg, ofCoeffs, finsuppOfCandidates,
    Polynomial.coeff_neg]

theorem mul_eq (p q : RuntimePolynomial) : mul p q = p * q := by
  apply Polynomial.coeff_injective
  funext n
  rw [Polynomial.coeff_mul]
  simp only [mul, ofCoeffs, finsuppOfCandidates, Polynomial.coeff_ofFinsupp,
    Finsupp.coe_mk, mulCoeff, rawCoeff_eq_coeff]
  rfl

theorem sub_eq (p q : RuntimePolynomial) : sub p q = p - q := by
  rw [sub, add_eq, neg_eq, sub_eq_add_neg]

theorem pow_eq (n : Nat) (p : RuntimePolynomial) : pow n p = p ^ n := by
  induction n with
  | zero =>
      exact one_eq
  | succ n ih =>
      rw [pow, mul_eq, ih, pow_succ]

theorem nsmul_eq (n : Nat) (p : RuntimePolynomial) : nsmul n p = n • p := by
  induction n with
  | zero =>
      rw [nsmul, zero_nsmul]
      exact zero_eq
  | succ n ih =>
      rw [nsmul, add_eq, ih, succ_nsmul]

theorem zsmul_eq (z : Int) (p : RuntimePolynomial) : zsmul z p = z • p := by
  cases z with
  | ofNat n =>
      change nsmul n p = (n : Int) • p
      rw [natCast_zsmul]
      exact nsmul_eq n p
  | negSucc n =>
      rw [zsmul, neg_eq, nsmul_eq]
      rw [negSucc_zsmul]

theorem natCast_eq (n : Nat) : natCast n = (n : RuntimePolynomial) := by
  rw [natCast, C_eq, Polynomial.C_eq_natCast]

theorem intCast_eq (z : Int) : intCast z = (z : RuntimePolynomial) := by
  rw [intCast, C_eq, Polynomial.C_eq_intCast]

@[implicit_reducible] private def nonUnitalCommRing :
    NonUnitalCommRing (RuntimePolynomial) where
  add := add
  add_assoc := by
    intro a b c
    change add (add a b) c = add a (add b c)
    simp only [add_eq]
    exact add_assoc a b c
  zero := zero
  zero_add := zero_add_runtime
  add_zero := add_zero_runtime
  nsmul := nsmul
  nsmul_zero := by
    intro a
    change nsmul 0 a = zero
    rfl
  nsmul_succ := by
    intro n a
    change nsmul (n + 1) a = add (nsmul n a) a
    rfl
  neg := neg
  sub := sub
  sub_eq_add_neg := by
    intro a b
    rfl
  zsmul := zsmul
  zsmul_zero' := by
    intro a
    change zsmul 0 a = zero
    rfl
  zsmul_succ' := by
    intro n a
    change zsmul (Int.ofNat n.succ) a = add (zsmul (Int.ofNat n) a) a
    rfl
  zsmul_neg' := by
    intro n a
    change zsmul (Int.negSucc n) a = neg (zsmul (Int.ofNat n.succ) a)
    rfl
  neg_add_cancel := neg_add_cancel_runtime
  add_comm := by
    intro a b
    change add a b = add b a
    simp only [add_eq]
    exact add_comm a b
  mul := mul
  left_distrib := by
    intro a b c
    change mul a (add b c) = add (mul a b) (mul a c)
    simp only [mul_eq, add_eq]
    exact left_distrib a b c
  right_distrib := by
    intro a b c
    change mul (add a b) c = add (mul a c) (mul b c)
    simp only [mul_eq, add_eq]
    exact right_distrib a b c
  zero_mul := zero_mul_runtime
  mul_zero := mul_zero_runtime
  mul_assoc := by
    intro a b c
    change mul (mul a b) c = mul a (mul b c)
    simp only [mul_eq]
    exact mul_assoc a b c
  mul_comm := by
    intro a b
    change mul a b = mul b a
    simp only [mul_eq]
    exact mul_comm a b

private theorem add_assoc_runtime (a b c : RuntimePolynomial) :
    add (add a b) c = add a (add b c) := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_add,
    rawCoeff_add, rawCoeff_add, rawCoeff_add]
  exact cleanCommRingRat.add_assoc _ _ _

private theorem add_comm_runtime (a b : RuntimePolynomial) :
    add a b = add b a := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_add, rawCoeff_add]
  exact cleanCommRingRat.add_comm _ _

private theorem left_distrib_runtime (a b c : RuntimePolynomial) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_mul, rawCoeff_add,
    rawCoeff_mul, rawCoeff_mul]
  unfold mulCoeff
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ij _
  rw [rawCoeff_add]
  exact cleanCommRingRat.left_distrib _ _ _

private theorem right_distrib_runtime (a b c : RuntimePolynomial) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_mul, rawCoeff_add,
    rawCoeff_mul, rawCoeff_mul]
  unfold mulCoeff
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ij _
  rw [rawCoeff_add]
  exact cleanCommRingRat.right_distrib _ _ _

private theorem sub_add_cancel_runtime (a b : RuntimePolynomial) :
    add (sub a b) b = a := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_add, rawCoeff_sub]
  exact sub_add_cancel _ _

private def measure (p : RuntimePolynomial) : Nat :=
  if isZeroB p = true then 0 else natDegree p + 1

private def divisionTerm (p q : RuntimePolynomial) : RuntimePolynomial :=
  monomial (leadingCoeff p) (natDegree p - natDegree q)

private def divisionStep (p q : RuntimePolynomial) : RuntimePolynomial :=
  sub p (mul q (divisionTerm p q))

private theorem divisionStep_coeff_zero_ge
    {p q : RuntimePolynomial} (hq : IsMonicRuntime q)
    (hdeg : natDegree q ≤ natDegree p) :
    ∀ n, natDegree p ≤ n → rawCoeff (divisionStep p q) n = 0 := by
  intro n hn
  rw [divisionStep, rawCoeff_sub, divisionTerm, rawCoeff_mul_monomial]
  by_cases hnp : n = natDegree p
  · subst n
    rw [if_pos (Nat.sub_le _ _), Nat.sub_sub_self hdeg]
    change leadingCoeff p - leadingCoeff q * leadingCoeff p = 0
    rw [hq, one_mul, sub_self]
  · have hpLt : natDegree p < n := by omega
    rw [rawCoeff_eq_zero_of_natDegree_lt p hpLt]
    by_cases hd : natDegree p - natDegree q ≤ n
    · rw [if_pos hd]
      have hqLt :
          natDegree q < n - (natDegree p - natDegree q) := by
        omega
      rw [rawCoeff_eq_zero_of_natDegree_lt q hqLt, zero_mul, sub_zero]
    · rw [if_neg hd, sub_zero]

private theorem divisionStep_measure_lt
    {p q : RuntimePolynomial} (hp : p ≠ zero) (hq : IsMonicRuntime q)
    (hdeg : natDegree q ≤ natDegree p) :
    measure (divisionStep p q) < measure p := by
  have hpBool : isZeroB p ≠ true :=
    fun h => hp ((isZeroB_eq_true_iff p).mp h)
  unfold measure
  rw [if_neg hpBool]
  by_cases hs : isZeroB (divisionStep p q) = true
  · rw [if_pos hs]
    exact Nat.zero_lt_succ _
  · rw [if_neg hs]
    apply Nat.add_lt_add_right
    apply natDegree_lt_of_coeff_zero_ge
    · exact fun h => hs ((isZeroB_eq_true_iff _).mpr h)
    · exact divisionStep_coeff_zero_ge hq hdeg

private structure DivModMonicResult
    (p q : RuntimePolynomial) where
  quot : RuntimePolynomial
  rem : RuntimePolynomial
  equation : add rem (mul q quot) = p
  rem_measure : measure rem < measure q

private def divModMonicResult :
    ∀ (p : RuntimePolynomial) {q : RuntimePolynomial},
      IsMonicRuntime q → DivModMonicResult p q
  | p, q, hq =>
      if hp : isZeroB p = true then
        { quot := zero
          rem := p
          equation := by rw [mul_zero_runtime, add_zero_runtime]
          rem_measure := by
            have hqBool : isZeroB q ≠ true :=
              fun h => hq.ne_zero ((isZeroB_eq_true_iff q).mp h)
            unfold measure
            rw [if_pos hp, if_neg hqBool]
            exact Nat.zero_lt_succ _ }
      else if hdeg : natDegree p < natDegree q then
        { quot := zero
          rem := p
          equation := by rw [mul_zero_runtime, add_zero_runtime]
          rem_measure := by
            have hqBool : isZeroB q ≠ true :=
              fun h => hq.ne_zero ((isZeroB_eq_true_iff q).mp h)
            unfold measure
            rw [if_neg hp, if_neg hqBool]
            exact Nat.add_lt_add_right hdeg 1 }
      else
        let z := divisionTerm p q
        have hp0 : p ≠ zero :=
          fun h => hp ((isZeroB_eq_true_iff p).mpr h)
        have hdeg' : natDegree q ≤ natDegree p :=
          Nat.le_of_not_gt hdeg
        let dm := divModMonicResult (divisionStep p q) hq
        { quot := add z dm.quot
          rem := dm.rem
          equation := by
            calc
              add dm.rem (mul q (add z dm.quot)) =
                  add dm.rem (add (mul q z) (mul q dm.quot)) := by
                    rw [left_distrib_runtime]
              _ = add (add dm.rem (mul q dm.quot)) (mul q z) := by
                calc
                  add dm.rem (add (mul q z) (mul q dm.quot)) =
                      add (add dm.rem (mul q z)) (mul q dm.quot) :=
                    (add_assoc_runtime _ _ _).symm
                  _ = add (mul q dm.quot) (add dm.rem (mul q z)) :=
                    add_comm_runtime _ _
                  _ = add (add (mul q dm.quot) dm.rem) (mul q z) :=
                    (add_assoc_runtime _ _ _).symm
                  _ = add (add dm.rem (mul q dm.quot)) (mul q z) := by
                    rw [add_comm_runtime (mul q dm.quot) dm.rem]
              _ = add (divisionStep p q) (mul q z) := by
                rw [dm.equation]
              _ = add (sub p (mul q z)) (mul q z) := rfl
              _ = p := sub_add_cancel_runtime p (mul q z)
          rem_measure := dm.rem_measure }
termination_by p => measure p
decreasing_by
  exact divisionStep_measure_lt hp0 hq hdeg'

def divModMonicAux (p : RuntimePolynomial) {q : RuntimePolynomial}
    (hq : IsMonicRuntime q) : RuntimePolynomial × RuntimePolynomial :=
  let dm := divModMonicResult p hq
  (dm.quot, dm.rem)

private theorem divModMonicAux_equation
    (p : RuntimePolynomial) {q : RuntimePolynomial} (hq : IsMonicRuntime q) :
    add (divModMonicAux p hq).2
        (mul q (divModMonicAux p hq).1) = p := by
  exact (divModMonicResult p hq).equation

private theorem divModMonicAux_rem_eq_self_of_measure_lt
    (p : RuntimePolynomial) {q : RuntimePolynomial} (hq : IsMonicRuntime q)
    (hmeasure : measure p < measure q) :
    (divModMonicAux p hq).2 = p := by
  unfold divModMonicAux
  rw [divModMonicResult]
  split
  · rfl
  · rename_i hp
    have hqBool : isZeroB q ≠ true :=
      fun h => hq.ne_zero ((isZeroB_eq_true_iff q).mp h)
    have hdeg : natDegree p < natDegree q := by
      unfold measure at hmeasure
      rw [if_neg hp, if_neg hqBool] at hmeasure
      omega
    simp only [hdeg, ↓reduceDIte]

private theorem IsMonicRuntime.toMonic {p : RuntimePolynomial}
    (hp : IsMonicRuntime p) : p.Monic := by
  rw [Polynomial.Monic, ← leadingCoeff_eq]
  exact hp

private theorem degree_lt_of_measure_lt
    {p q : RuntimePolynomial} (hqRuntime : q ≠ zero)
    (hmeasure : measure p < measure q) :
    p.degree < q.degree := by
  have hqStandard : q ≠ 0 :=
    fun h => hqRuntime (h.trans zero_eq.symm)
  by_cases hp : p = zero
  · have hpStandard : p = 0 := hp.trans zero_eq
    rw [hpStandard, Polynomial.degree_zero, bot_lt_iff_ne_bot]
    exact Polynomial.degree_ne_bot.mpr hqStandard
  · have hpStandard : p ≠ 0 :=
      fun h => hp (h.trans zero_eq.symm)
    have hpBool : isZeroB p ≠ true :=
      fun h => hp ((isZeroB_eq_true_iff p).mp h)
    have hqBool : isZeroB q ≠ true :=
      fun h => hqRuntime ((isZeroB_eq_true_iff q).mp h)
    have hnat : natDegree p < natDegree q := by
      unfold measure at hmeasure
      rw [if_neg hpBool, if_neg hqBool] at hmeasure
      omega
    rw [Polynomial.degree_eq_natDegree hpStandard,
      Polynomial.degree_eq_natDegree hqStandard]
    rw [← natDegree_eq, ← natDegree_eq]
    exact_mod_cast hnat

theorem divModMonicAux_eq_standard
    (p : RuntimePolynomial) {q : RuntimePolynomial} (hq : IsMonicRuntime q) :
    divModMonicAux p hq =
      (Polynomial.divByMonic p q, Polynomial.modByMonic p q) := by
  let dm := divModMonicResult p hq
  have hqStandard := hq.toMonic
  have heq : dm.rem + q * dm.quot = p := by
    simpa only [add_eq, mul_eq] using dm.equation
  have hu := Polynomial.div_modByMonic_unique
    dm.quot dm.rem hqStandard
      ⟨heq, degree_lt_of_measure_lt hq.ne_zero dm.rem_measure⟩
  apply Prod.ext
  · exact hu.1.symm
  · exact hu.2.symm

private def monicDivisor (q : RuntimePolynomial) : RuntimePolynomial :=
  scale q (leadingCoeff q)⁻¹

private theorem monicDivisor_eq (q : RuntimePolynomial) :
    monicDivisor q =
      q * Polynomial.C q.leadingCoeff⁻¹ := by
  apply Polynomial.coeff_injective
  funext n
  rw [Polynomial.coeff_mul_C, ← rawCoeff_eq_coeff,
    ← rawCoeff_eq_coeff, monicDivisor, rawCoeff_scale, leadingCoeff_eq]

private theorem monicDivisor_monic {q : RuntimePolynomial} (hq : q ≠ zero) :
    IsMonicRuntime (monicDivisor q) := by
  have hlc : leadingCoeff q ≠ 0 :=
    leadingCoeff_ne_zero_runtime hq
  rw [IsMonicRuntime, monicDivisor,
    leadingCoeff_scale (inv_ne_zero hlc), mul_inv_cancel₀ hlc]

private theorem monicDivisor_natDegree {q : RuntimePolynomial} (hq : q ≠ zero) :
    natDegree (monicDivisor q) = natDegree q := by
  rw [monicDivisor, natDegree_scale]
  exact inv_ne_zero (leadingCoeff_ne_zero_runtime hq)

private theorem monicDivisor_measure {q : RuntimePolynomial} (hq : q ≠ zero) :
    measure (monicDivisor q) = measure q := by
  have hmonic := monicDivisor_monic hq
  have hqBool : isZeroB q ≠ true :=
    fun h => hq ((isZeroB_eq_true_iff q).mp h)
  have hmBool : isZeroB (monicDivisor q) ≠ true :=
    fun h => hmonic.ne_zero ((isZeroB_eq_true_iff _).mp h)
  unfold measure
  rw [if_neg hmBool, if_neg hqBool, monicDivisor_natDegree hq]

public def divMod (p q : RuntimePolynomial) :
    RuntimePolynomial × RuntimePolynomial :=
  if hq : isZeroB q = true then
    (zero, p)
  else
    have hq0 : q ≠ zero :=
      fun h => hq ((isZeroB_eq_true_iff q).mpr h)
    let dm := divModMonicAux p (monicDivisor_monic hq0)
    (mul (C (leadingCoeff q)⁻¹) dm.1, dm.2)

private theorem divMod_rem_measure_lt
    (p : RuntimePolynomial) {q : RuntimePolynomial} (hq : q ≠ zero) :
    measure (divMod p q).2 < measure q := by
  unfold divMod
  split
  case isTrue hqB =>
    exact False.elim <| hq ((isZeroB_eq_true_iff q).mp hqB)
  case isFalse =>
    let hmonic := monicDivisor_monic hq
    let dm := divModMonicResult p hmonic
    change measure dm.rem < measure q
    exact dm.rem_measure.trans_eq (monicDivisor_measure hq)

private theorem divMod_rem_eq_self_of_measure_lt
    (p : RuntimePolynomial) {q : RuntimePolynomial} (hq : q ≠ zero)
    (hmeasure : measure p < measure q) :
    (divMod p q).2 = p := by
  unfold divMod
  split
  case isTrue hqB =>
    exact False.elim <| hq ((isZeroB_eq_true_iff q).mp hqB)
  case isFalse =>
    apply divModMonicAux_rem_eq_self_of_measure_lt
    rw [monicDivisor_measure hq]
    exact hmeasure

theorem divMod_eq_standard (p q : RuntimePolynomial) :
    divMod p q = (p / q, p % q) := by
  unfold divMod
  split
  case isTrue hq =>
    have hq0 : q = zero := (isZeroB_eq_true_iff q).mp hq
    subst q
    rw [zero_eq]
    simp
  case isFalse hq =>
    have hq0 : q ≠ zero :=
      fun h => hq ((isZeroB_eq_true_iff q).mpr h)
    simp only
    rw [divModMonicAux_eq_standard]
    apply Prod.ext
    · simp only [mul_eq, C_eq, leadingCoeff_eq, monicDivisor_eq]
      exact Polynomial.div_def.symm
    · simp only [monicDivisor_eq]
      exact Polynomial.mod_def.symm

public def normalize (p : RuntimePolynomial) : RuntimePolynomial :=
  if isZeroB p = true then zero
  else mul p (C (leadingCoeff p)⁻¹)

def normUnit (p : RuntimePolynomial) : RuntimePolynomial :=
  if isZeroB p = true then one
  else C (leadingCoeff p)⁻¹

def normUnitUnit (p : RuntimePolynomial) : (RuntimePolynomial)ˣ :=
  if hp : isZeroB p = true then
    { val := one
      inv := one
      val_inv := by rw [one_eq, mul_one]
      inv_val := by rw [one_eq, mul_one] }
  else
    have hlc : leadingCoeff p ≠ 0 := by
      rw [leadingCoeff_eq, Polynomial.leadingCoeff_ne_zero]
      intro h
      exact hp ((isZeroB_eq_true_iff p).2 h)
    { val := C (leadingCoeff p)⁻¹
      inv := C (leadingCoeff p)
      val_inv := by
        rw [C_eq, C_eq, ← Polynomial.C_mul,
          inv_mul_cancel₀ hlc, Polynomial.C_1]
      inv_val := by
        rw [C_eq, C_eq, ← Polynomial.C_mul,
          mul_inv_cancel₀ hlc, Polynomial.C_1] }

theorem normalize_eq_standard (p : RuntimePolynomial) :
    normalize p = _root_.normalize p := by
  unfold normalize
  split
  case isTrue hp =>
    have hp0 : p = 0 := (isZeroB_eq_true_iff p).1 hp
    subst p
    rw [zero_eq, _root_.normalize_zero]
  case isFalse hp =>
    have hp0 : p ≠ 0 := by
      intro h
      exact hp ((isZeroB_eq_true_iff p).2 h)
    rw [mul_eq, C_eq, leadingCoeff_eq, _root_.normalize_apply,
      Polynomial.coe_normUnit_of_ne_zero hp0]

theorem normUnit_eq_standard (p : RuntimePolynomial) :
    normUnit p = (↑(NormalizationMonoid.normUnit p) : RuntimePolynomial) := by
  unfold normUnit
  split
  case isTrue hp =>
    have hp0 : p = 0 := (isZeroB_eq_true_iff p).1 hp
    subst p
    rw [one_eq, normUnit_zero, Units.val_one]
  case isFalse hp =>
    have hp0 : p ≠ 0 := by
      intro h
      exact hp ((isZeroB_eq_true_iff p).2 h)
    rw [C_eq, leadingCoeff_eq, Polynomial.coe_normUnit_of_ne_zero hp0]

theorem normUnitUnit_eq_standard (p : RuntimePolynomial) :
    normUnitUnit p = NormalizationMonoid.normUnit p := by
  apply Units.ext
  unfold normUnitUnit
  split
  case isTrue hp =>
    have hp0 : p = 0 := (isZeroB_eq_true_iff p).1 hp
    change one = (↑(NormalizationMonoid.normUnit p) : RuntimePolynomial)
    rw [one_eq, hp0, normUnit_zero, Units.val_one]
  case isFalse hp =>
    have hp0 : p ≠ 0 := by
      intro h
      exact hp ((isZeroB_eq_true_iff p).2 h)
    change C (leadingCoeff p)⁻¹ =
      (↑(NormalizationMonoid.normUnit p) : RuntimePolynomial)
    rw [C_eq, leadingCoeff_eq, Polynomial.coe_normUnit_of_ne_zero hp0]

@[implicit_reducible] private def normalizationMonoidStandard :
    NormalizationMonoid (RuntimePolynomial) where
  normUnit := normUnitUnit
  normUnit_zero := by
    rw [normUnitUnit_eq_standard]
    exact normUnit_zero
  normUnit_one := by
    rw [normUnitUnit_eq_standard]
    exact normUnit_one
  normUnit_mul_units := by
    intro p u hp
    simp only [normUnitUnit_eq_standard]
    exact normUnit_mul_units u hp

private abbrev CoeffTriple := Nat × (Nat × Nat)

private def leftTriples (n : Nat) : List CoeffTriple :=
  (List.Nat.antidiagonal n).flatMap fun kc =>
    (List.Nat.antidiagonal kc.1).map fun ab =>
      (ab.1, (ab.2, kc.2))

private def rightTriples (n : Nat) : List CoeffTriple :=
  (List.Nat.antidiagonal n).flatMap fun ak =>
    (List.Nat.antidiagonal ak.2).map fun bc =>
      (ak.1, (bc.1, bc.2))

private theorem mem_leftTriples {n : Nat} {t : CoeffTriple} :
    t ∈ leftTriples n ↔ t.1 + t.2.1 + t.2.2 = n := by
  rcases t with ⟨a, ⟨b, c⟩⟩
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨kc, hkc, ht⟩
    rcases List.mem_map.mp ht with ⟨ab, hab, heq⟩
    have houter : kc.1 + kc.2 = n :=
      mem_antidiagonal_runtime.mp hkc
    have hinner : ab.1 + ab.2 = kc.1 :=
      mem_antidiagonal_runtime.mp hab
    have ha : ab.1 = a := congrArg (fun x => x.1) heq
    have hb : ab.2 = b := congrArg (fun x => x.2.1) heq
    have hc : kc.2 = c := congrArg (fun x => x.2.2) heq
    change a + b + c = n
    omega
  · intro hsum
    change a + b + c = n at hsum
    apply List.mem_flatMap.mpr
    refine ⟨(a + b, c), mem_antidiagonal_runtime.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨(a, b), mem_antidiagonal_runtime.mpr rfl, rfl⟩

private theorem mem_rightTriples {n : Nat} {t : CoeffTriple} :
    t ∈ rightTriples n ↔ t.1 + t.2.1 + t.2.2 = n := by
  rcases t with ⟨a, ⟨b, c⟩⟩
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨ak, hak, ht⟩
    rcases List.mem_map.mp ht with ⟨bc, hbc, heq⟩
    have houter : ak.1 + ak.2 = n :=
      mem_antidiagonal_runtime.mp hak
    have hinner : bc.1 + bc.2 = ak.2 :=
      mem_antidiagonal_runtime.mp hbc
    have ha : ak.1 = a := congrArg (fun x => x.1) heq
    have hb : bc.1 = b := congrArg (fun x => x.2.1) heq
    have hc : bc.2 = c := congrArg (fun x => x.2.2) heq
    change a + b + c = n
    omega
  · intro hsum
    change a + b + c = n at hsum
    apply List.mem_flatMap.mpr
    refine ⟨(a, b + c), mem_antidiagonal_runtime.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨(b, c), mem_antidiagonal_runtime.mpr rfl, rfl⟩

private theorem nodup_leftTriples (n : Nat) :
    (leftTriples n).Nodup := by
  unfold leftTriples
  rw [List.nodup_flatMap]
  constructor
  · intro kc _
    exact (nodup_antidiagonal_runtime kc.1).map fun x y h => by
      apply Prod.ext
      · exact congrArg (fun t => t.1) h
      · exact congrArg (fun t => t.2.1) h
  · apply
      (List.nodup_iff_pairwise_ne.mp
        (nodup_antidiagonal_runtime n)).imp_of_mem
    intro kc₁ kc₂ hkc₁ hkc₂ hne
    unfold Function.onFun
    rw [List.disjoint_left]
    intro t ht₁ ht₂
    rcases List.mem_map.mp ht₁ with ⟨ab₁, _, heq₁⟩
    rcases List.mem_map.mp ht₂ with ⟨ab₂, _, heq₂⟩
    have hc : kc₁.2 = kc₂.2 := by
      calc
        kc₁.2 = ((ab₁.1, (ab₁.2, kc₁.2)) : CoeffTriple).2.2 := rfl
        _ = t.2.2 := congrArg (fun x => x.2.2) heq₁
        _ = ((ab₂.1, (ab₂.2, kc₂.2)) : CoeffTriple).2.2 :=
          (congrArg (fun x => x.2.2) heq₂).symm
        _ = kc₂.2 := rfl
    have hsum₁ : kc₁.1 + kc₁.2 = n :=
      mem_antidiagonal_runtime.mp hkc₁
    have hsum₂ : kc₂.1 + kc₂.2 = n :=
      mem_antidiagonal_runtime.mp hkc₂
    exact hne (Prod.ext (by omega) hc)

private theorem nodup_rightTriples (n : Nat) :
    (rightTriples n).Nodup := by
  unfold rightTriples
  rw [List.nodup_flatMap]
  constructor
  · intro ak _
    exact (nodup_antidiagonal_runtime ak.2).map fun x y h => by
      apply Prod.ext
      · exact congrArg (fun t => t.2.1) h
      · exact congrArg (fun t => t.2.2) h
  · apply
      (List.nodup_iff_pairwise_ne.mp
        (nodup_antidiagonal_runtime n)).imp_of_mem
    intro ak₁ ak₂ hak₁ hak₂ hne
    unfold Function.onFun
    rw [List.disjoint_left]
    intro t ht₁ ht₂
    rcases List.mem_map.mp ht₁ with ⟨bc₁, _, heq₁⟩
    rcases List.mem_map.mp ht₂ with ⟨bc₂, _, heq₂⟩
    have ha : ak₁.1 = ak₂.1 := by
      calc
        ak₁.1 = ((ak₁.1, (bc₁.1, bc₁.2)) : CoeffTriple).1 := rfl
        _ = t.1 := congrArg (fun x => x.1) heq₁
        _ = ((ak₂.1, (bc₂.1, bc₂.2)) : CoeffTriple).1 :=
          (congrArg (fun x => x.1) heq₂).symm
        _ = ak₂.1 := rfl
    have hsum₁ : ak₁.1 + ak₁.2 = n :=
      mem_antidiagonal_runtime.mp hak₁
    have hsum₂ : ak₂.1 + ak₂.2 = n :=
      mem_antidiagonal_runtime.mp hak₂
    exact hne (Prod.ext ha (by omega))

private theorem triples_perm (n : Nat) :
    (leftTriples n).Perm (rightTriples n) := by
  apply
    (List.perm_ext_iff_of_nodup
      (nodup_leftTriples n) (nodup_rightTriples n)).mpr
  intro t
  exact mem_leftTriples.trans mem_rightTriples.symm

private theorem mulCoeff_assoc_left
    (p q r : RuntimePolynomial) (n : Nat) :
    mulCoeff (mul p q) r n =
      ((leftTriples n).map fun t =>
        (rawCoeff p t.1 * rawCoeff q t.2.1) *
          rawCoeff r t.2.2).sum := by
  unfold mulCoeff leftTriples
  simp only [rawCoeff_mul, mulCoeff, List.map_map,
    List.flatMap_def, List.map_flatten]
  rw [list_sum_flatten_runtime]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro kc _
  unfold Function.comp
  rw [List.map_map]
  exact (List.sum_map_mul_right
    (List.Nat.antidiagonal kc.1)
    (fun ab => rawCoeff p ab.1 * rawCoeff q ab.2)
    (rawCoeff r kc.2)).symm

private theorem mulCoeff_assoc_right
    (p q r : RuntimePolynomial) (n : Nat) :
    mulCoeff p (mul q r) n =
      ((rightTriples n).map fun t =>
        rawCoeff p t.1 *
          (rawCoeff q t.2.1 * rawCoeff r t.2.2)).sum := by
  unfold mulCoeff rightTriples
  simp only [rawCoeff_mul, mulCoeff, List.map_map,
    List.flatMap_def, List.map_flatten]
  rw [list_sum_flatten_runtime]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ak _
  unfold Function.comp
  rw [List.map_map]
  exact (List.sum_map_mul_left
    (List.Nat.antidiagonal ak.2)
    (fun bc => rawCoeff q bc.1 * rawCoeff r bc.2)
    (rawCoeff p ak.1)).symm

private theorem mulCoeff_assoc
    (p q r : RuntimePolynomial) (n : Nat) :
    mulCoeff (mul p q) r n = mulCoeff p (mul q r) n := by
  rw [mulCoeff_assoc_left, mulCoeff_assoc_right]
  calc
    ((leftTriples n).map fun t =>
        (rawCoeff p t.1 * rawCoeff q t.2.1) *
          rawCoeff r t.2.2).sum =
        ((leftTriples n).map fun t =>
          rawCoeff p t.1 *
            (rawCoeff q t.2.1 * rawCoeff r t.2.2)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro t _
          exact cleanCommRingRat.mul_assoc _ _ _
    _ = ((rightTriples n).map fun t =>
          rawCoeff p t.1 *
            (rawCoeff q t.2.1 * rawCoeff r t.2.2)).sum :=
      ((triples_perm n).map fun t =>
        rawCoeff p t.1 *
          (rawCoeff q t.2.1 * rawCoeff r t.2.2)).sum_eq

private theorem mul_assoc_runtime' (p q r : RuntimePolynomial) :
    mul (mul p q) r = mul p (mul q r) := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_mul, rawCoeff_mul]
  exact mulCoeff_assoc p q r n

private theorem mul_comm_runtime' (p q : RuntimePolynomial) :
    mul p q = mul q p := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_mul, rawCoeff_mul]
  unfold mulCoeff
  calc
    ((List.Nat.antidiagonal n).map fun ij =>
        rawCoeff p ij.1 * rawCoeff q ij.2).sum =
        ((List.Nat.antidiagonal n).map fun ij =>
          rawCoeff q ij.2 * rawCoeff p ij.1).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro ij _
            exact cleanCommRingRat.mul_comm _ _
    _ = (((List.Nat.antidiagonal n).map Prod.swap).map fun ij =>
          rawCoeff q ij.1 * rawCoeff p ij.2).sum := by
            rw [List.map_map]
            apply congrArg List.sum
            apply List.map_congr_left
            intro ij _
            rfl
    _ = ((List.Nat.antidiagonal n).reverse.map fun ij =>
          rawCoeff q ij.1 * rawCoeff p ij.2).sum := by
            rw [List.Nat.map_swap_antidiagonal]
    _ = (((List.Nat.antidiagonal n).map fun ij =>
          rawCoeff q ij.1 * rawCoeff p ij.2).reverse).sum := by
            rw [List.map_reverse]
    _ = ((List.Nat.antidiagonal n).map fun ij =>
          rawCoeff q ij.1 * rawCoeff p ij.2).sum :=
      (List.reverse_perm _).sum_eq

private theorem mul_one_runtime' (p : RuntimePolynomial) :
    mul p one = p := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff]
  change rawCoeff (mul p (monomial 1 0)) n = rawCoeff p n
  rw [rawCoeff_mul_monomial]
  simp

private theorem one_mul_runtime' (p : RuntimePolynomial) :
    mul one p = p := by
  rw [mul_comm_runtime']
  exact mul_one_runtime' p

@[implicit_reducible] private def commRing : CommRing (RuntimePolynomial) where
  add := add
  add_assoc := add_assoc_runtime
  zero := zero
  zero_add := zero_add_runtime
  add_zero := add_zero_runtime
  nsmul := nsmul
  nsmul_zero := by
    intro _
    rfl
  nsmul_succ := by
    intro _ _
    rfl
  add_comm := add_comm_runtime
  mul := mul
  mul_assoc := mul_assoc_runtime'
  one := one
  one_mul := one_mul_runtime'
  mul_one := mul_one_runtime'
  npow := fun n a => pow n a
  npow_zero := by
    intro a
    change pow 0 a = one
    rfl
  npow_succ := by
    intro _ _
    rfl
  zero_mul := zero_mul_runtime
  mul_zero := mul_zero_runtime
  left_distrib := left_distrib_runtime
  right_distrib := right_distrib_runtime
  natCast := natCast
  natCast_zero := by
    change natCast 0 = zero
    apply Polynomial.coeff_injective
    funext n
    rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff]
    rw [natCast, rawCoeff_C, rawCoeff_zero]
    split
    · exact cleanSemiringRat.natCast_zero
    · rfl
  natCast_succ := by
    intro n
    change natCast (n + 1) = add (natCast n) one
    apply Polynomial.coeff_injective
    funext k
    rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_add]
    change
      (if k = 0 then ((n + 1 : Nat) : Rat) else 0) =
        (if k = 0 then (n : Rat) else 0) +
          (if k = 0 then 1 else 0)
    by_cases h : k = 0
    · simp only [h, ↓reduceIte]
      exact cleanSemiringRat.natCast_succ n
    · simp [h]
  neg := neg
  sub := sub
  sub_eq_add_neg := by
    intro _ _
    rfl
  zsmul := zsmul
  zsmul_zero' := by
    intro _
    rfl
  zsmul_succ' := by
    intro _ _
    rfl
  zsmul_neg' := by
    intro _ _
    rfl
  neg_add_cancel := neg_add_cancel_runtime
  intCast := intCast
  intCast_ofNat := by
    intro n
    change intCast (Int.ofNat n) = natCast n
    apply Polynomial.coeff_injective
    funext k
    rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff]
    change
      (if k = 0 then ((Int.ofNat n : Int) : Rat) else 0) =
        (if k = 0 then (n : Rat) else 0)
    by_cases h : k = 0 <;> simp [h]
  intCast_negSucc := by
    intro n
    change intCast (Int.negSucc n) = neg (natCast (n + 1))
    apply Polynomial.coeff_injective
    funext k
    rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, intCast, natCast,
      rawCoeff_C, rawCoeff_neg, rawCoeff_C]
    by_cases h : k = 0
    · simp only [h, ↓reduceIte]
      exact cleanRingRat.intCast_negSucc n
    · simp [h]
  mul_comm := mul_comm_runtime'

private theorem divMod_equation (p q : RuntimePolynomial) :
    add (mul q (divMod p q).1) (divMod p q).2 = p := by
  unfold divMod
  split
  case isTrue =>
    rw [mul_zero_runtime, zero_add_runtime]
  case isFalse hqB =>
    have hq : q ≠ zero :=
      fun h => hqB ((isZeroB_eq_true_iff q).mpr h)
    let hmonic := monicDivisor_monic hq
    let dm := divModMonicAux p hmonic
    have heq := divModMonicAux_equation p hmonic
    change
      add (mul q (mul (C (leadingCoeff q)⁻¹) dm.1))
        dm.2 = p
    calc
      add (mul q (mul (C (leadingCoeff q)⁻¹) dm.1)) dm.2 =
          add dm.2 (mul (monicDivisor q) dm.1) := by
            rw [← mul_assoc_runtime', mul_C_runtime, monicDivisor]
            exact add_comm_runtime _ _
      _ = p := heq

private theorem measure_mul_not_lt_left
    (p q : RuntimePolynomial) (hq : q ≠ zero) :
    ¬measure (mul p q) < measure p := by
  by_cases hpBool : isZeroB p = true
  · have hp : p = zero := (isZeroB_eq_true_iff p).1 hpBool
    subst p
    have hz : isZeroB zero = true :=
      (isZeroB_eq_true_iff zero).mpr rfl
    unfold measure
    rw [if_pos hz]
    exact Nat.not_lt_zero _
  · have hp : p ≠ zero :=
      fun h => hpBool ((isZeroB_eq_true_iff p).2 h)
    have hmulRuntime : mul p q ≠ zero :=
      mul_ne_zero_runtime hp hq
    have hmulBool : isZeroB (mul p q) ≠ true :=
      fun h => hmulRuntime ((isZeroB_eq_true_iff _).mp h)
    unfold measure
    rw [if_neg hmulBool, if_neg hpBool]
    rw [natDegree_mul_runtime hp hq]
    omega

private theorem nontrivialRuntimePolynomial :
    Nontrivial RuntimePolynomial :=
  { exists_pair_ne := ⟨zero, one, by
    intro h
    have hcoeff := congrArg (fun p => rawCoeff p 0) h
    change (0 : Rat) = 1 at hcoeff
    exact zero_ne_one hcoeff⟩ }

@[implicit_reducible] private def euclideanDomain :
    EuclideanDomain (RuntimePolynomial) :=
  { commRing, nontrivialRuntimePolynomial with
    quotient := fun p q => (divMod p q).1
    quotient_zero := by
      intro p
      change (divMod p zero).1 = zero
      have hzero : isZeroB zero = true :=
        (isZeroB_eq_true_iff zero).2 rfl
      simp only [divMod, hzero, ↓reduceDIte]
    remainder := fun p q => (divMod p q).2
    quotient_mul_add_remainder_eq := by
      intro p q
      change add (mul q (divMod p q).1) (divMod p q).2 = p
      exact divMod_equation p q
    r := fun p q => measure p < measure q
    r_wellFounded :=
      WellFounded.onFun Nat.lt_wfRel.wf (f := measure)
    remainder_lt := by
      intro p q hq
      exact divMod_rem_measure_lt p hq
    mul_left_not_lt := by
      intro p q hq
      exact measure_mul_not_lt_left p q hq }

private theorem commRing_eq_standard :
    commRing = Polynomial.commRing := by
  apply CommRing.ext
  · funext p q
    exact add_eq p q
  · funext p q
    exact mul_eq p q

@[reducible] private def monoidWithZeroOfCommRing
    {α : Type _} (c : CommRing α) : MonoidWithZero α :=
  @Semiring.toMonoidWithZero α c.toCommSemiring.toSemiring

@[reducible] private def monoidOfCommRing
    {α : Type _} (c : CommRing α) : Monoid α :=
  @Semiring.toMonoid α c.toCommSemiring.toSemiring

@[reducible] private def dvdOfCommRing
    {α : Type _} (c : CommRing α) : Dvd α :=
  @semigroupDvd α
    (@SemigroupWithZero.toSemigroup α
      (@NonUnitalSemiring.toSemigroupWithZero α
        (@NonUnitalCommSemiring.toNonUnitalSemiring α
          (@NonUnitalCommRing.toNonUnitalCommSemiring α
            c.toNonUnitalCommRing))))

private theorem mul_C_C_runtime (a b : Rat) :
    mul (C a) (C b) = C (a * b) := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff]
  change
    rawCoeff (mul (C a) (monomial b 0)) n =
      rawCoeff (C (a * b)) n
  rw [rawCoeff_mul_monomial]
  simp only [rawCoeff_C]
  simp

private theorem C_one_runtime : C 1 = one := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff, rawCoeff_C, rawCoeff_one]

private theorem C_eq_monomial_runtime (a : Rat) :
    C a = monomial a 0 := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff,
    rawCoeff_C, rawCoeff_monomial]

private theorem C_ne_zero_runtime {a : Rat} (ha : a ≠ 0) :
    C a ≠ zero := by
  intro h
  have hcoeff := congrArg (fun p => rawCoeff p 0) h
  change a = 0 at hcoeff
  exact ha hcoeff

private theorem natDegree_C_runtime {a : Rat} (ha : a ≠ 0) :
    natDegree (C a) = 0 := by
  rw [C_eq_monomial_runtime, natDegree_monomial ha]

private theorem leadingCoeff_C_runtime {a : Rat} (ha : a ≠ 0) :
    leadingCoeff (C a) = a := by
  rw [C_eq_monomial_runtime, leadingCoeff_monomial ha]

private theorem rawSupport_one_runtime : rawSupport one = {0} := by
  apply Finset.ext
  intro n
  change
    n ∈ one.toFinsupp.coeff.support ↔
      n ∈ ({0} : Finset Nat)
  rw [Finsupp.mem_support_iff]
  change (if n = 0 then 1 else 0) ≠ 0 ↔ n ∈ ({0} : Finset Nat)
  by_cases h : n = 0 <;> simp [h]

private theorem natDegree_one_runtime : natDegree one = 0 := by
  unfold natDegree
  rw [rawSupport_one_runtime]
  simp [supportMax]

private theorem leadingCoeff_one_runtime : leadingCoeff one = 1 := by
  unfold leadingCoeff natDegree
  rw [rawSupport_one_runtime]
  simp only [supportMax, Finset.fold_singleton, id_eq]
  change rawCoeff one 0 = 1
  rw [rawCoeff_one]
  rfl

private theorem one_ne_zero_runtime : one ≠ zero := by
  intro h
  have hcoeff := congrArg (fun p => rawCoeff p 0) h
  change (1 : Rat) = 0 at hcoeff
  exact one_ne_zero hcoeff

private theorem eq_C_leadingCoeff_of_natDegree_eq_zero
    {p : RuntimePolynomial} (hdegree : natDegree p = 0) :
    p = C (leadingCoeff p) := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff]
  by_cases hn : n = 0
  · subst n
    rw [rawCoeff_C, if_pos rfl]
    unfold leadingCoeff
    rw [hdegree]
  · have hdeg : natDegree p < n := by omega
    rw [rawCoeff_eq_zero_of_natDegree_lt p hdeg,
      rawCoeff_C, if_neg hn]

private def runtimeUnit (p : RuntimePolynomial) :
    @Units (RuntimePolynomial) (monoidOfCommRing commRing) :=
  if hp : isZeroB p = true then
    @Units.mk (RuntimePolynomial) (monoidOfCommRing commRing)
      one one
      (by
        change mul one one = one
        exact one_mul_runtime' one)
      (by
        change mul one one = one
        exact one_mul_runtime' one)
  else
    have hp0 : p ≠ zero :=
      fun h => hp ((isZeroB_eq_true_iff p).2 h)
    have hlc : leadingCoeff p ≠ 0 :=
      leadingCoeff_ne_zero_runtime hp0
    @Units.mk (RuntimePolynomial) (monoidOfCommRing commRing)
      (C (leadingCoeff p)⁻¹) (C (leadingCoeff p))
      (by
        change mul (C (leadingCoeff p)⁻¹) (C (leadingCoeff p)) = one
        rw [mul_C_C_runtime,
          @inv_mul_cancel₀ Rat
            cleanCommGroupWithZeroRat.toGroupWithZero _ hlc,
          C_one_runtime])
      (by
        change mul (C (leadingCoeff p)) (C (leadingCoeff p)⁻¹) = one
        rw [mul_C_C_runtime,
          @mul_inv_cancel₀ Rat
            cleanCommGroupWithZeroRat.toGroupWithZero _ hlc,
          C_one_runtime])

private theorem runtimeUnit_val (p : RuntimePolynomial) :
    @Units.val (RuntimePolynomial) (monoidOfCommRing commRing)
      (runtimeUnit p) = normUnit p := by
  unfold runtimeUnit normUnit
  split <;> rfl

private noncomputable def unitToStandard
    (u : @Units (RuntimePolynomial) (monoidOfCommRing commRing)) :
    @Units (RuntimePolynomial) (monoidOfCommRing Polynomial.commRing) :=
  @Units.mk (RuntimePolynomial) (monoidOfCommRing Polynomial.commRing)
    (@Units.val (RuntimePolynomial) (monoidOfCommRing commRing) u)
    (@Units.inv (RuntimePolynomial) (monoidOfCommRing commRing) u)
    (by
      have h :=
        @Units.val_inv (RuntimePolynomial) (monoidOfCommRing commRing) u
      change mul
        (@Units.val (RuntimePolynomial) (monoidOfCommRing commRing) u)
        (@Units.inv (RuntimePolynomial) (monoidOfCommRing commRing) u) = one at h
      simpa only [mul_eq, one_eq] using h)
    (by
      have h :=
        @Units.inv_val (RuntimePolynomial) (monoidOfCommRing commRing) u
      change mul
        (@Units.inv (RuntimePolynomial) (monoidOfCommRing commRing) u)
        (@Units.val (RuntimePolynomial) (monoidOfCommRing commRing) u) = one at h
      simpa only [mul_eq, one_eq] using h)

@[implicit_reducible] private def normalizationMonoid :
    @NormalizationMonoid (RuntimePolynomial)
      (monoidWithZeroOfCommRing commRing) :=
  @NormalizationMonoid.mk (RuntimePolynomial)
    (monoidWithZeroOfCommRing commRing)
    runtimeUnit
    (by
      apply @Units.ext (RuntimePolynomial) (monoidOfCommRing commRing)
      rfl)
    (by
      apply @Units.ext (RuntimePolynomial) (monoidOfCommRing commRing)
      change
        @Units.val (RuntimePolynomial) (monoidOfCommRing commRing)
          (runtimeUnit one) = one
      rw [runtimeUnit_val]
      unfold normUnit
      have hone : isZeroB one ≠ true :=
        fun h => one_ne_zero_runtime ((isZeroB_eq_true_iff one).1 h)
      rw [if_neg hone, leadingCoeff_one_runtime,
        rat_inv_one_runtime, C_one_runtime])
    (by
      intro p u hp
      change p ≠ zero at hp
      apply @Units.ext (RuntimePolynomial) (monoidOfCommRing commRing)
      let uv :=
        @Units.val (RuntimePolynomial) (monoidOfCommRing commRing) u
      let ui :=
        @Units.inv (RuntimePolynomial) (monoidOfCommRing commRing) u
      simp only [Units.val_mul]
      change
        @Units.val (RuntimePolynomial) (monoidOfCommRing commRing)
            (runtimeUnit (mul p uv)) =
          mul ui
            (@Units.val (RuntimePolynomial) (monoidOfCommRing commRing)
              (runtimeUnit p))
      rw [runtimeUnit_val, runtimeUnit_val]
      have huvEq :=
        @Units.val_inv (RuntimePolynomial) (monoidOfCommRing commRing) u
      change mul uv ui = one at huvEq
      have huv0 : uv ≠ zero := by
        intro hzero
        rw [hzero, zero_mul_runtime] at huvEq
        exact one_ne_zero_runtime huvEq.symm
      have hui0 : ui ≠ zero := by
        intro hzero
        rw [hzero, mul_zero_runtime] at huvEq
        exact one_ne_zero_runtime huvEq.symm
      have hproduct0 : mul p uv ≠ zero :=
        mul_ne_zero_runtime hp huv0
      have hpBool : isZeroB p ≠ true :=
        fun h => hp ((isZeroB_eq_true_iff p).1 h)
      have hproductBool : isZeroB (mul p uv) ≠ true :=
        fun h => hproduct0 ((isZeroB_eq_true_iff _).1 h)
      have hdegreeProduct :=
        congrArg natDegree huvEq
      rw [natDegree_mul_runtime huv0 hui0,
        natDegree_one_runtime] at hdegreeProduct
      have huiDegree : natDegree ui = 0 := by omega
      have huiC : ui = C (leadingCoeff ui) :=
        eq_C_leadingCoeff_of_natDegree_eq_zero huiDegree
      have hlcEq :=
        congrArg leadingCoeff huvEq
      rw [leadingCoeff_mul_runtime huv0 hui0,
        leadingCoeff_one_runtime] at hlcEq
      have hlu0 : leadingCoeff uv ≠ 0 :=
        leadingCoeff_ne_zero_runtime huv0
      have hli : leadingCoeff ui = (leadingCoeff uv)⁻¹ := by
        calc
          leadingCoeff ui =
              1 * leadingCoeff ui :=
            (cleanCommGroupWithZeroRat.one_mul _).symm
          _ = ((leadingCoeff uv)⁻¹ * leadingCoeff uv) *
                leadingCoeff ui := by
              rw [@inv_mul_cancel₀ Rat
                cleanCommGroupWithZeroRat.toGroupWithZero _ hlu0]
          _ = (leadingCoeff uv)⁻¹ *
                (leadingCoeff uv * leadingCoeff ui) :=
            cleanCommGroupWithZeroRat.mul_assoc _ _ _
          _ = (leadingCoeff uv)⁻¹ := by
            rw [hlcEq]
            exact cleanCommGroupWithZeroRat.mul_one _
      unfold normUnit
      rw [if_neg hproductBool, if_neg hpBool,
        leadingCoeff_mul_runtime hp huv0, huiC, mul_C_C_runtime]
      apply congrArg C
      rw [rat_inv_mul_runtime, ← hli])

private def decEq (p q : RuntimePolynomial) : Decidable (p = q) :=
  if h : isZeroB (sub p q) = true then
    .isTrue <|
      (@sub_eq_zero RuntimePolynomial commRing.toAddGroup p q).mp <|
        (isZeroB_eq_true_iff (sub p q)).1 h
  else
    .isFalse fun hpq =>
      h <| (isZeroB_eq_true_iff (sub p q)).2 <| by
        rw [hpq]
        exact @sub_self RuntimePolynomial commRing.toAddGroup q

local instance runtimeEuclideanDomain :
    EuclideanDomain (RuntimePolynomial) :=
  euclideanDomain

local instance runtimeDecidableEq :
    DecidableEq (RuntimePolynomial) :=
  decEq

local instance runtimeNormalizationMonoid :
    @NormalizationMonoid (RuntimePolynomial)
      (monoidWithZeroOfCommRing commRing) :=
  normalizationMonoid

private theorem runtimeNormUnit_coe (p : RuntimePolynomial) :
    (↑(@NormalizationMonoid.normUnit (RuntimePolynomial)
        (monoidWithZeroOfCommRing commRing) normalizationMonoid p) :
      RuntimePolynomial) =
      normUnit p := by
  exact runtimeUnit_val p

private theorem dvd_iff_standard (p q : RuntimePolynomial) :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) p q ↔
      @Dvd.dvd (RuntimePolynomial)
        (dvdOfCommRing Polynomial.commRing) p q := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.trans (mul_eq p c)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.trans (mul_eq p c).symm⟩

private theorem divMod_measure_lt (p : RuntimePolynomial) {q : RuntimePolynomial}
    (hq : q ≠ zero) :
    measure (divMod p q).2 < measure q :=
  divMod_rem_measure_lt p hq

private structure RawXGCDResult
    (a b : RuntimePolynomial) where
  gcd : RuntimePolynomial
  leftCoeff : RuntimePolynomial
  rightCoeff : RuntimePolynomial
  bezout : add (mul a leftCoeff) (mul b rightCoeff) = gcd
  gcd_dvd_left :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) gcd a
  gcd_dvd_right :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) gcd b
  dvd_gcd :
    ∀ {d : RuntimePolynomial},
      @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d a →
      @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d b →
      @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d gcd

private theorem dvd_refl_runtime (a : RuntimePolynomial) :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) a a :=
  ⟨one, (mul_one_runtime' a).symm⟩

private theorem dvd_zero_runtime (a : RuntimePolynomial) :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) a zero :=
  ⟨zero, (mul_zero_runtime a).symm⟩

private theorem dvd_mul_right_runtime
    {d a : RuntimePolynomial}
    (hdiv : @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d a)
    (q : RuntimePolynomial) :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d (mul a q) := by
  rcases hdiv with ⟨c, hac⟩
  change a = mul d c at hac
  refine ⟨mul c q, ?_⟩
  change mul a q = mul d (mul c q)
  rw [hac]
  exact mul_assoc_runtime' d c q

private theorem dvd_add_runtime
    {d a b : RuntimePolynomial}
    (ha : @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d a)
    (hb : @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d b) :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d (add a b) := by
  rcases ha with ⟨c, hac⟩
  rcases hb with ⟨e, hbe⟩
  change a = mul d c at hac
  change b = mul d e at hbe
  refine ⟨add c e, ?_⟩
  change add a b = mul d (add c e)
  rw [hac, hbe]
  exact (left_distrib_runtime d c e).symm

private theorem mul_sub_runtime'
    (a b c : RuntimePolynomial) :
    mul a (sub b c) = sub (mul a b) (mul a c) :=
  @mul_sub RuntimePolynomial
    commRing.toRing.toNonUnitalRing.toNonUnitalNonAssocRing a b c

private theorem add_add_sub_cancel_runtime'
    (a b c : RuntimePolynomial) :
    add (add a b) (sub c a) = add c b := by
  apply Polynomial.coeff_injective
  funext n
  rw [← rawCoeff_eq_coeff, ← rawCoeff_eq_coeff,
    rawCoeff_add, rawCoeff_add, rawCoeff_sub, rawCoeff_add]
  letI : CommRing Rat := cleanCommRingRat
  ring

private theorem dvd_sub_runtime
    {d a b : RuntimePolynomial}
    (ha : @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d a)
    (hb : @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d b) :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d (sub a b) := by
  rcases ha with ⟨c, hac⟩
  rcases hb with ⟨e, hbe⟩
  change a = mul d c at hac
  change b = mul d e at hbe
  refine ⟨sub c e, ?_⟩
  change sub a b = mul d (sub c e)
  rw [hac, hbe]
  exact
    (@mul_sub RuntimePolynomial
      commRing.toRing.toNonUnitalRing.toNonUnitalNonAssocRing d c e).symm

/--
Direct extended Euclidean recursion over the runtime `divMod`.  Unlike
mathlib's generic `gcd`/`gcdA`/`gcdB`, this data path mentions only the
constructive polynomial operations defined in this module.
-/
private def rawXgcd (a b : RuntimePolynomial) : RawXGCDResult a b :=
  if hb : isZeroB b = true then
    have hb0 : b = zero := (isZeroB_eq_true_iff b).1 hb
    { gcd := a
      leftCoeff := one
      rightCoeff := zero
      bezout := by
        rw [hb0, mul_one_runtime', zero_mul_runtime, add_zero_runtime]
      gcd_dvd_left := dvd_refl_runtime a
      gcd_dvd_right := by
        subst b
        exact dvd_zero_runtime a
      dvd_gcd := by
        intro d hda _
        exact hda }
  else
    have hb0 : b ≠ zero := by
      intro h
      exact hb ((isZeroB_eq_true_iff b).2 h)
    let dm := divMod a b
    let next := rawXgcd b dm.2
    have hdiv : add (mul b dm.1) dm.2 = a := by
      simpa only [dm] using divMod_equation a b
    { gcd := next.gcd
      leftCoeff := next.rightCoeff
      rightCoeff := sub next.leftCoeff (mul dm.1 next.rightCoeff)
      bezout := by
        have hnext := next.bezout
        calc
          add (mul a next.rightCoeff)
              (mul b (sub next.leftCoeff
                (mul dm.1 next.rightCoeff))) =
              add
                (mul (add (mul b dm.1) dm.2) next.rightCoeff)
                (mul b (sub next.leftCoeff
                  (mul dm.1 next.rightCoeff))) := by
                    rw [hdiv]
          _ = add (mul b next.leftCoeff)
                (mul dm.2 next.rightCoeff) := by
            rw [right_distrib_runtime, mul_sub_runtime',
              ← mul_assoc_runtime' b dm.1 next.rightCoeff]
            exact add_add_sub_cancel_runtime' _ _ _
          _ = next.gcd := hnext
      gcd_dvd_left := by
        rw [← hdiv]
        exact dvd_add_runtime
          (dvd_mul_right_runtime next.gcd_dvd_left dm.1)
          next.gcd_dvd_right
      gcd_dvd_right := next.gcd_dvd_left
      dvd_gcd := by
        intro d hda hdb
        apply next.dvd_gcd hdb
        have hrem : dm.2 = sub a (mul b dm.1) := by
          exact
            @eq_sub_of_add_eq' RuntimePolynomial
              commRing.toAddCommGroup dm.2 a (mul b dm.1) hdiv
        rw [hrem]
        exact dvd_sub_runtime hda
          (dvd_mul_right_runtime hdb dm.1) }
termination_by measure b
decreasing_by
  exact divMod_measure_lt a hb0

private def xgcd (a b : RuntimePolynomial) :
    XGCDResult (RuntimePolynomial) :=
  let raw := rawXgcd a b
  let u := normUnit raw.gcd
  { gcd := mul raw.gcd u
    leftCoeff := mul raw.leftCoeff u
    rightCoeff := mul raw.rightCoeff u }

private theorem mul_normUnit_eq_normalize (p : RuntimePolynomial) :
    mul p (normUnit p) = normalize p := by
  unfold normUnit normalize
  split
  case isTrue hp =>
    have hp0 : p = zero := (isZeroB_eq_true_iff p).1 hp
    subst p
    rw [zero_mul_runtime]
  case isFalse =>
    rfl

private theorem runtimeNormalize_eq (p : RuntimePolynomial) :
    @_root_.normalize (RuntimePolynomial)
      (monoidWithZeroOfCommRing commRing) normalizationMonoid p =
        normalize p := by
  change mul p
      (↑(@NormalizationMonoid.normUnit (RuntimePolynomial)
        (monoidWithZeroOfCommRing commRing) normalizationMonoid p) :
        RuntimePolynomial) =
    normalize p
  rw [runtimeNormUnit_coe, mul_normUnit_eq_normalize]

private theorem normalize_ne_zero
    {p : RuntimePolynomial} (hp : p ≠ zero) :
    normalize p ≠ zero := by
  have hpBool : isZeroB p ≠ true :=
    fun h => hp ((isZeroB_eq_true_iff p).1 h)
  have hlc : leadingCoeff p ≠ 0 :=
    leadingCoeff_ne_zero_runtime hp
  have hinv : (leadingCoeff p)⁻¹ ≠ 0 :=
    inv_ne_zero hlc
  rw [normalize, if_neg hpBool]
  exact mul_ne_zero_runtime hp (C_ne_zero_runtime hinv)

private theorem leadingCoeff_normalize_runtime
    {p : RuntimePolynomial} (hp : p ≠ zero) :
    leadingCoeff (normalize p) = 1 := by
  have hpBool : isZeroB p ≠ true :=
    fun h => hp ((isZeroB_eq_true_iff p).1 h)
  have hlc : leadingCoeff p ≠ 0 :=
    leadingCoeff_ne_zero_runtime hp
  have hinv : (leadingCoeff p)⁻¹ ≠ 0 :=
    inv_ne_zero hlc
  rw [normalize, if_neg hpBool,
    leadingCoeff_mul_runtime hp (C_ne_zero_runtime hinv),
    leadingCoeff_C_runtime hinv, mul_inv_cancel₀ hlc]

private theorem normalize_idem_runtime (p : RuntimePolynomial) :
    normalize (normalize p) = normalize p := by
  by_cases hp : p = zero
  · subst p
    have hzero : isZeroB zero = true :=
      (isZeroB_eq_true_iff zero).2 rfl
    simp only [normalize, hzero, ↓reduceIte]
  · have hnorm : normalize p ≠ zero :=
      normalize_ne_zero hp
    have hnormBool : isZeroB (normalize p) ≠ true :=
      fun h => hnorm ((isZeroB_eq_true_iff _).1 h)
    calc
      normalize (normalize p) =
          mul (normalize p) (C (leadingCoeff (normalize p))⁻¹) := by
            rw [normalize, if_neg hnormBool]
      _ = mul (normalize p) (C (1 : Rat)⁻¹) := by
        rw [leadingCoeff_normalize_runtime hp]
      _ = normalize p := by
        rw [rat_inv_one_runtime, C_one_runtime, mul_one_runtime']

private theorem normalize_natDegree (p : RuntimePolynomial) :
    natDegree (normalize p) = natDegree p := by
  by_cases hp : p = zero
  · subst p
    have hzero : isZeroB zero = true :=
      (isZeroB_eq_true_iff zero).2 rfl
    simp only [normalize, hzero, ↓reduceIte]
  · have hpBool : isZeroB p ≠ true :=
      fun h => hp ((isZeroB_eq_true_iff p).1 h)
    have hlc : leadingCoeff p ≠ 0 :=
      leadingCoeff_ne_zero_runtime hp
    have hinv : (leadingCoeff p)⁻¹ ≠ 0 :=
      inv_ne_zero hlc
    rw [normalize, if_neg hpBool,
      natDegree_mul_runtime hp (C_ne_zero_runtime hinv),
      natDegree_C_runtime hinv, Nat.add_zero]

private theorem commonDivisor_natDegree_lt_left
    {a b g : RuntimePolynomial}
    (ha : a ≠ zero)
    (hnot : ¬@Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) a b)
    (hdivARuntime :
      @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) g a)
    (hdivBRuntime :
      @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) g b) :
    natDegree g < natDegree a := by
  rcases hdivARuntime with ⟨c, hac⟩
  rcases hdivBRuntime with ⟨d, hbd⟩
  change a = mul g c at hac
  change b = mul g d at hbd
  have hg0 : g ≠ zero := by
    intro hzero
    rw [hzero, zero_mul_runtime] at hac
    exact ha hac
  have hc0 : c ≠ zero := by
    intro hzero
    rw [hzero, mul_zero_runtime] at hac
    exact ha hac
  have hcDegree : natDegree c ≠ 0 := by
    intro hdegree
    apply hnot
    have hcC : c = C (leadingCoeff c) :=
      eq_C_leadingCoeff_of_natDegree_eq_zero hdegree
    have hlc : leadingCoeff c ≠ 0 :=
      leadingCoeff_ne_zero_runtime hc0
    let ci := C (leadingCoeff c)⁻¹
    have hci : mul c ci = one := by
      rw [hcC]
      unfold ci
      rw [mul_C_C_runtime, mul_inv_cancel₀ hlc, C_one_runtime]
    refine ⟨mul ci d, ?_⟩
    change b = mul a (mul ci d)
    calc
      b = mul g d := hbd
      _ = mul g (mul one d) := by
        rw [one_mul_runtime']
      _ = mul g (mul (mul c ci) d) := by
        rw [hci]
      _ = mul g (mul c (mul ci d)) := by
        rw [mul_assoc_runtime']
      _ = mul (mul g c) (mul ci d) :=
        (mul_assoc_runtime' g c (mul ci d)).symm
      _ = mul a (mul ci d) := by rw [← hac]
  rw [hac, natDegree_mul_runtime hg0 hc0]
  omega

private theorem mul_normUnit_dvd_of_dvd
    {g a : RuntimePolynomial}
    (hdiv :
      @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) g a) :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing)
      (mul g (normUnit g)) a := by
  rcases hdiv with ⟨c, hac⟩
  change a = mul g c at hac
  let u := runtimeUnit g
  let uv :=
    @Units.val (RuntimePolynomial) (monoidOfCommRing commRing) u
  let ui :=
    @Units.inv (RuntimePolynomial) (monoidOfCommRing commRing) u
  have huval : uv = normUnit g := by
    exact runtimeUnit_val g
  have huvEq :=
    @Units.val_inv (RuntimePolynomial) (monoidOfCommRing commRing) u
  change mul uv ui = one at huvEq
  refine ⟨mul ui c, ?_⟩
  change a = mul (mul g (normUnit g)) (mul ui c)
  calc
    a = mul g c := hac
    _ = mul g (mul one c) := by rw [one_mul_runtime']
    _ = mul g (mul (mul uv ui) c) := by rw [huvEq]
    _ = mul g (mul uv (mul ui c)) := by
      rw [mul_assoc_runtime']
    _ = mul (mul g uv) (mul ui c) :=
      (mul_assoc_runtime' g uv (mul ui c)).symm
    _ = mul (mul g (normUnit g)) (mul ui c) := by
      rw [huval]

private theorem dvd_mul_normUnit_of_dvd
    {d g : RuntimePolynomial}
    (hdiv :
      @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d g) :
    @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing)
      d (mul g (normUnit g)) := by
  rcases hdiv with ⟨c, hgc⟩
  change g = mul d c at hgc
  refine ⟨mul c (normUnit g), ?_⟩
  change mul g (normUnit g) = mul d (mul c (normUnit g))
  calc
    mul g (normUnit g) =
        mul (mul d c) (normUnit g) := by rw [← hgc]
    _ = mul d (mul c (normUnit g)) :=
      mul_assoc_runtime' d c (normUnit g)

@[implicit_reducible] private def ops :
    @ComputableEuclideanOps (RuntimePolynomial)
      runtimeEuclideanDomain normalizationMonoid where
  eqb p q := isZeroB (sub p q)
  divMod := divMod
  normalize := normalize
  normUnit := normUnit
  xgcd := xgcd
  measure := measure
  normUnitUnit := runtimeUnit

  eqb_spec := by
    intro p q
    rw [isZeroB_eq_true_iff]
    exact @sub_eq_zero RuntimePolynomial commRing.toAddGroup p q
  divMod_spec := by
    intro p q
    rfl
  remainder_measure_lt := by
    intro p q hq
    exact divMod_measure_lt p hq
  normalize_spec := by
    intro p
    exact (runtimeNormalize_eq p).symm
  normalize_idem_spec := normalize_idem_runtime
  normUnit_spec := by
    intro p
    exact (runtimeNormUnit_coe p).symm
  normUnitUnit_coe := by
    intro p
    exact runtimeUnit_val p
  xgcd_normalized := by
    intro a b
    let raw := rawXgcd a b
    change mul raw.gcd (normUnit raw.gcd) =
      @_root_.normalize (RuntimePolynomial)
        (monoidWithZeroOfCommRing commRing) normalizationMonoid
        (mul raw.gcd (normUnit raw.gcd))
    rw [mul_normUnit_eq_normalize, runtimeNormalize_eq,
      normalize_idem_runtime]
  xgcd_bezout_spec := by
    intro a b
    let raw := rawXgcd a b
    let u := normUnit raw.gcd
    change add (mul a (mul raw.leftCoeff u))
      (mul b (mul raw.rightCoeff u)) = mul raw.gcd u
    have hraw := raw.bezout
    calc
      add (mul a (mul raw.leftCoeff u))
          (mul b (mul raw.rightCoeff u)) =
          add (mul (mul a raw.leftCoeff) u)
            (mul (mul b raw.rightCoeff) u) := by
              rw [mul_assoc_runtime', mul_assoc_runtime']
      _ = mul
          (add (mul a raw.leftCoeff) (mul b raw.rightCoeff)) u :=
        (right_distrib_runtime
          (mul a raw.leftCoeff) (mul b raw.rightCoeff) u).symm
      _ = mul raw.gcd u := by rw [hraw]
  xgcd_dvd_left := by
    intro a b
    let raw := rawXgcd a b
    change @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing)
      (mul raw.gcd (normUnit raw.gcd)) a
    exact mul_normUnit_dvd_of_dvd raw.gcd_dvd_left
  xgcd_dvd_right := by
    intro a b
    let raw := rawXgcd a b
    change @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing)
      (mul raw.gcd (normUnit raw.gcd)) b
    exact mul_normUnit_dvd_of_dvd raw.gcd_dvd_right
  dvd_xgcd := by
    intro a b d ha hb
    let raw := rawXgcd a b
    change @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing) d
      (mul raw.gcd (normUnit raw.gcd))
    exact dvd_mul_normUnit_of_dvd (raw.dvd_gcd ha hb)
  xgcd_measure_lt := by
    intro a b ha hnot
    change a ≠ zero at ha
    let raw := rawXgcd a b
    have hg0 : raw.gcd ≠ zero := by
      intro hg
      rcases raw.gcd_dvd_left with ⟨c, hac⟩
      change a = mul raw.gcd c at hac
      rw [hg, zero_mul_runtime] at hac
      exact ha hac
    have hnormG0 : normalize raw.gcd ≠ zero := normalize_ne_zero hg0
    have hnormA0 : normalize a ≠ zero := normalize_ne_zero ha
    change measure (mul raw.gcd (normUnit raw.gcd)) <
      measure (normalize a)
    rw [mul_normUnit_eq_normalize]
    unfold measure
    rw [if_neg (fun h => hnormG0 ((isZeroB_eq_true_iff _).1 h)),
      if_neg (fun h => hnormA0 ((isZeroB_eq_true_iff _).1 h))]
    apply Nat.add_lt_add_right
    rw [normalize_natDegree, normalize_natDegree]
    exact commonDivisor_natDegree_lt_left ha hnot
      raw.gcd_dvd_left raw.gcd_dvd_right

private theorem rawCoeff_eq_zero_of_measure_lt
    {p m : RuntimePolynomial} (hm : m ≠ zero)
    (hpm : measure p < measure m) {n : Nat}
    (hn : natDegree m ≤ n) :
    rawCoeff p n = 0 := by
  by_cases hp : p = zero
  · subst p
    exact rawCoeff_zero n
  · have hpBool : isZeroB p ≠ true :=
      fun h => hp ((isZeroB_eq_true_iff p).1 h)
    have hmBool : isZeroB m ≠ true :=
      fun h => hm ((isZeroB_eq_true_iff m).1 h)
    unfold measure at hpm
    rw [if_neg hpBool, if_neg hmBool] at hpm
    apply rawCoeff_eq_zero_of_natDegree_lt p
    omega

private theorem sub_measure_lt
    {a b m : RuntimePolynomial} (hm : m ≠ zero)
    (ha : measure a < measure m)
    (hb : measure b < measure m) :
    measure (sub b a) < measure m := by
  have hmBool : isZeroB m ≠ true :=
    fun h => hm ((isZeroB_eq_true_iff m).1 h)
  by_cases hsub : sub b a = zero
  · have hsubBool : isZeroB (sub b a) = true :=
      (isZeroB_eq_true_iff _).2 hsub
    unfold measure
    rw [if_pos hsubBool, if_neg hmBool]
    omega
  · have hcoeff :
        ∀ n, natDegree m ≤ n → rawCoeff (sub b a) n = 0 := by
      intro n hn
      rw [rawCoeff_sub,
        rawCoeff_eq_zero_of_measure_lt hm hb hn,
        rawCoeff_eq_zero_of_measure_lt hm ha hn]
      exact @sub_self Rat cleanRingRat.toAddGroup 0
    have hdeg :
        natDegree (sub b a) < natDegree m :=
      natDegree_lt_of_coeff_zero_ge hsub hcoeff
    have hsubBool : isZeroB (sub b a) ≠ true :=
      fun h => hsub ((isZeroB_eq_true_iff _).1 h)
    unfold measure
    rw [if_neg hsubBool, if_neg hmBool]
    omega

public structure CanonicalModLaws
    (euclidean : EuclideanDomain (RuntimePolynomial)) : Prop where
  mod_mod : ∀ a b : RuntimePolynomial,
    euclidean.remainder (euclidean.remainder a b) b =
      euclidean.remainder a b
  reduced_eq_of_dvd_sub :
    ∀ {a b m : RuntimePolynomial},
      a = euclidean.remainder a m →
      b = euclidean.remainder b m →
      @Dvd.dvd (RuntimePolynomial)
        (@semigroupDvd (RuntimePolynomial)
          (@SemigroupWithZero.toSemigroup (RuntimePolynomial)
            (@NonUnitalSemiring.toSemigroupWithZero (RuntimePolynomial)
              (@NonUnitalCommSemiring.toNonUnitalSemiring (RuntimePolynomial)
                (@NonUnitalCommRing.toNonUnitalCommSemiring (RuntimePolynomial)
                  euclidean.toCommRing.toNonUnitalCommRing)))))
        m (euclidean.toCommRing.sub b a) →
      a = b

private theorem canonicalMod :
  CanonicalModLaws runtimeEuclideanDomain := by
  constructor
  · intro a b
    change (divMod (divMod a b).2 b).2 = (divMod a b).2
    by_cases hb : b = zero
    · subst b
      have hzero : isZeroB zero = true :=
        (isZeroB_eq_true_iff zero).mpr rfl
      simp only [divMod, hzero, ↓reduceDIte]
    · exact divMod_rem_eq_self_of_measure_lt
        (divMod a b).2 hb (divMod_rem_measure_lt a hb)
  · intro a b m ha hb hdiv
    change a = (divMod a m).2 at ha
    change b = (divMod b m).2 at hb
    have hdivRuntime :
        @Dvd.dvd (RuntimePolynomial) (dvdOfCommRing commRing)
          m (sub b a) := hdiv
    rcases hdivRuntime with ⟨c, hsub⟩
    change sub b a = mul m c at hsub
    by_cases hm : m = zero
    · subst m
      rw [zero_mul_runtime] at hsub
      exact
        (@sub_eq_zero RuntimePolynomial commRing.toAddGroup b a).mp hsub |>.symm
    · have hma : measure a < measure m := by
        rw [ha]
        exact divMod_rem_measure_lt a hm
      have hmb : measure b < measure m := by
        rw [hb]
        exact divMod_rem_measure_lt b hm
      have hsubMeasure : measure (sub b a) < measure m :=
        sub_measure_lt hm hma hmb
      by_cases hc : c = zero
      · subst c
        rw [mul_zero_runtime] at hsub
        exact
          (@sub_eq_zero RuntimePolynomial commRing.toAddGroup b a).mp hsub |>.symm
      · have hproduct : measure (mul m c) < measure m := by
          rw [← hsub]
          exact hsubMeasure
        exact False.elim (measure_mul_not_lt_left m c hc hproduct)

/--
The coherent runtime dictionaries used to execute rational-polynomial normal
forms.  The representation and proof bridges remain internal; clients consume
the bundle as one value so algebraic instances cannot be mixed accidentally.
-/
public structure RuntimeAlgebra where
  euclidean : EuclideanDomain (RuntimePolynomial)
  normalization :
    @NormalizationMonoid (RuntimePolynomial)
      (@Semiring.toMonoidWithZero (RuntimePolynomial)
        euclidean.toCommRing.toCommSemiring.toSemiring)
  decidableEq : DecidableEq (RuntimePolynomial)
  operations :
    @ComputableEuclideanOps (RuntimePolynomial) euclidean normalization
  canonicalMod : CanonicalModLaws euclidean

/-- Coherent, executable rational-polynomial Euclidean dictionaries. -/
public def runtimeAlgebra : RuntimeAlgebra where
  euclidean := euclideanDomain
  normalization := normalizationMonoid
  decidableEq := decEq
  operations := ops
  canonicalMod := canonicalMod

/-
Implementation modules imported with `import all` use these equalities to move
runtime certificates into standard polynomial algebra without exposing the
private runtime ring dictionary through the stable core facade.
-/
theorem runtimeAlgebra_zero_eq :
    @Zero.zero RuntimePolynomial
        runtimeAlgebra.euclidean.toCommRing.toZero =
      zero :=
  rfl

theorem runtimeAlgebra_one_eq :
    @One.one RuntimePolynomial
        runtimeAlgebra.euclidean.toCommRing.toOne =
      one :=
  rfl

theorem runtimeAlgebra_add_eq (p q : RuntimePolynomial) :
    @Add.add RuntimePolynomial
        runtimeAlgebra.euclidean.toCommRing.toAdd p q =
      add p q :=
  rfl

theorem runtimeAlgebra_mul_eq (p q : RuntimePolynomial) :
    @Mul.mul RuntimePolynomial
        runtimeAlgebra.euclidean.toCommRing.toMul p q =
      mul p q :=
  rfl

/-
`MatrixInverseCertificate` obtains matrix addition and multiplication through
the `CommSemiring` projection of its `CommRing` argument.  Keep these two
coherence lemmas beside the runtime dictionary so application-only transport
code can map such certificates without rebuilding polynomial arithmetic.
-/
theorem runtimeAlgebra_commSemiring_add_eq (p q : RuntimePolynomial) :
    @Add.add RuntimePolynomial
        (@Semiring.toAddCommMonoid RuntimePolynomial
          runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toAdd p q =
      add p q :=
  rfl

theorem runtimeAlgebra_commSemiring_zero_eq :
    @Zero.zero RuntimePolynomial
        (@Semiring.toAddCommMonoid RuntimePolynomial
          runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toZero =
      zero :=
  rfl

theorem runtimeAlgebra_certificate_zero_eq :
    @Zero.zero RuntimePolynomial
        (@MulZeroClass.toZero RuntimePolynomial
          (@instMulZeroClassOfSemiring RuntimePolynomial
            runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring)) =
      zero :=
  rfl

theorem runtimeAlgebra_certificate_one_eq :
    @One.one RuntimePolynomial
        (@AddMonoidWithOne.toOne RuntimePolynomial
          (@AddGroupWithOne.toAddMonoidWithOne RuntimePolynomial
            (@Ring.toAddGroupWithOne RuntimePolynomial
              runtimeAlgebra.euclidean.toCommRing.toRing))) =
      one :=
  rfl

theorem runtimeAlgebra_commSemiring_mul_eq (p q : RuntimePolynomial) :
    @Mul.mul RuntimePolynomial
        (@instDistribOfSemiring RuntimePolynomial
          runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul p q =
      mul p q :=
  rfl

theorem runtimeAlgebra_divisibility_mul_eq (p q : RuntimePolynomial) :
    @Mul.mul RuntimePolynomial
        (let sourceRing :=
          runtimeAlgebra.euclidean.toCommRing.toNonUnitalCommRing
        let source := sourceRing.toNonUnitalCommSemiring
        source.toSemigroupWithZero.toMul)
        p q =
      mul p q :=
  rfl

end PolynomialRatRuntime

end NormalForms
