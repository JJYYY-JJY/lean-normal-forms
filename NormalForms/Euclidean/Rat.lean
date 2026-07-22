/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Tactic.Ring.RingNF

/-!
# Constructive rational algebra

Lean's rational representation is constructive, but the bundled mathlib ring
proofs currently pass through a choice-bearing integer division lemma.  This
module builds the same rational operations through a quotient of integer
fractions and transports them to `Rat`.  The quotient does not normalize
fractions; normalization is needed only for the equivalence back to `Rat`.
-/

namespace NormalForms

namespace ConstructiveRat

private structure Raw where
  num : Int
  den : Int
  den_ne_zero : den ≠ 0

private def Raw.Rel (a b : Raw) : Prop :=
  a.num * b.den = b.num * a.den

private theorem Raw.Rel.refl (a : Raw) : a.Rel a :=
  rfl

private theorem Raw.Rel.symm' {a b : Raw} (h : a.Rel b) : b.Rel a :=
  Eq.symm h

private theorem Raw.Rel.trans {a b c : Raw}
    (hab : a.Rel b) (hbc : b.Rel c) : a.Rel c := by
  unfold Raw.Rel at hab hbc ⊢
  apply Int.eq_of_mul_eq_mul_right b.den_ne_zero
  calc
    (a.num * c.den) * b.den =
        (a.num * b.den) * c.den := by ring
    _ = (b.num * a.den) * c.den := by rw [hab]
    _ = (b.num * c.den) * a.den := by ring
    _ = (c.num * b.den) * a.den := by rw [hbc]
    _ = (c.num * a.den) * b.den := by ring

private def rawSetoid : Setoid Raw where
  r := Raw.Rel
  iseqv := ⟨Raw.Rel.refl, Raw.Rel.symm', Raw.Rel.trans⟩

private abbrev Fraction := Quotient rawSetoid

private def Raw.zero : Raw :=
  ⟨0, 1, Int.one_ne_zero⟩

private def Raw.one : Raw :=
  ⟨1, 1, Int.one_ne_zero⟩

private def Raw.add (a b : Raw) : Raw :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den,
    Int.mul_ne_zero a.den_ne_zero b.den_ne_zero⟩

private def Raw.neg (a : Raw) : Raw :=
  ⟨-a.num, a.den, a.den_ne_zero⟩

private def Raw.mul (a b : Raw) : Raw :=
  ⟨a.num * b.num, a.den * b.den,
    Int.mul_ne_zero a.den_ne_zero b.den_ne_zero⟩

private def Raw.inv (a : Raw) : Raw :=
  if h : a.num = 0 then Raw.zero else ⟨a.den, a.num, h⟩

private theorem Raw.add_rel {a a' b b' : Raw}
    (ha : a.Rel a') (hb : b.Rel b') :
    (a.add b).Rel (a'.add b') := by
  unfold Raw.Rel at ha hb ⊢
  dsimp only [Raw.add]
  calc
    (a.num * b.den + b.num * a.den) * (a'.den * b'.den) =
        (a.num * a'.den) * (b.den * b'.den) +
          (b.num * b'.den) * (a.den * a'.den) := by ring
    _ = (a'.num * a.den) * (b.den * b'.den) +
          (b'.num * b.den) * (a.den * a'.den) := by rw [ha, hb]
    _ = (a'.num * b'.den + b'.num * a'.den) *
          (a.den * b.den) := by ring

private theorem Raw.neg_rel {a b : Raw} (h : a.Rel b) :
    a.neg.Rel b.neg := by
  unfold Raw.Rel at h ⊢
  dsimp only [Raw.neg]
  calc
    -a.num * b.den = -(a.num * b.den) := by ring
    _ = -(b.num * a.den) := congrArg Neg.neg h
    _ = -b.num * a.den := by ring

private theorem Raw.mul_rel {a a' b b' : Raw}
    (ha : a.Rel a') (hb : b.Rel b') :
    (a.mul b).Rel (a'.mul b') := by
  unfold Raw.Rel at ha hb ⊢
  dsimp only [Raw.mul]
  calc
    a.num * b.num * (a'.den * b'.den) =
        (a.num * a'.den) * (b.num * b'.den) := by ring
    _ = (a'.num * a.den) * (b'.num * b.den) := by rw [ha, hb]
    _ = a'.num * b'.num * (a.den * b.den) := by ring

private theorem Raw.num_eq_zero_iff {a b : Raw} (h : a.Rel b) :
    a.num = 0 ↔ b.num = 0 := by
  unfold Raw.Rel at h
  constructor
  · intro ha
    rw [ha, Int.zero_mul] at h
    exact (Int.mul_eq_zero.mp h.symm).resolve_right a.den_ne_zero
  · intro hb
    rw [hb, Int.zero_mul] at h
    exact (Int.mul_eq_zero.mp h).resolve_right b.den_ne_zero

private theorem Raw.inv_rel {a b : Raw} (h : a.Rel b) :
    a.inv.Rel b.inv := by
  unfold Raw.inv
  split <;> rename_i ha
  · have hb : b.num = 0 := (Raw.num_eq_zero_iff h).1 ha
    simp only [hb, ↓reduceDIte]
    exact Raw.Rel.refl Raw.zero
  · have hb : b.num ≠ 0 := fun hb =>
      ha ((Raw.num_eq_zero_iff h).2 hb)
    simp only [hb, ↓reduceDIte]
    unfold Raw.Rel at h ⊢
    dsimp only
    calc
      a.den * b.num = b.num * a.den := by ring
      _ = a.num * b.den := h.symm
      _ = b.den * a.num := by ring

private def zero : Fraction :=
  Quotient.mk rawSetoid Raw.zero

private def one : Fraction :=
  Quotient.mk rawSetoid Raw.one

private def add : Fraction → Fraction → Fraction :=
  fun a b => Quotient.liftOn₂ a b
    (fun x y => Quotient.mk rawSetoid (x.add y))
    (fun _ _ _ _ hx hy => Quotient.sound (Raw.add_rel hx hy))

private def neg : Fraction → Fraction :=
  Quotient.map Raw.neg (fun _ _ => Raw.neg_rel)

private def mul : Fraction → Fraction → Fraction :=
  fun a b => Quotient.liftOn₂ a b
    (fun x y => Quotient.mk rawSetoid (x.mul y))
    (fun _ _ _ _ hx hy => Quotient.sound (Raw.mul_rel hx hy))

private def inv : Fraction → Fraction :=
  Quotient.map Raw.inv (fun _ _ => Raw.inv_rel)

private def sub (a b : Fraction) : Fraction :=
  add a (neg b)

private def div (a b : Fraction) : Fraction :=
  mul a (inv b)

private def nsmul : Nat → Fraction → Fraction
  | 0, _ => zero
  | n + 1, a => add (nsmul n a) a

private def zsmul : Int → Fraction → Fraction
  | .ofNat n, a => nsmul n a
  | .negSucc n, a => neg (nsmul (n + 1) a)

private def npow : Nat → Fraction → Fraction
  | 0, _ => one
  | n + 1, a => mul (npow n a) a

private def zpow : Int → Fraction → Fraction
  | .ofNat n, a => npow n a
  | .negSucc n, a => inv (npow (n + 1) a)

private def ofInt (z : Int) : Fraction :=
  Quotient.mk rawSetoid ⟨z, 1, Int.one_ne_zero⟩

private theorem sound_raw (a b : Raw) (h : a.Rel b) :
    Quotient.mk rawSetoid a = Quotient.mk rawSetoid b :=
  Quotient.sound h

private theorem add_assoc_fraction (a b c : Fraction) :
    add (add a b) c = add a (add b c) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.add
  dsimp only
  ring

private theorem zero_add_fraction (a : Fraction) : add zero a = a := by
  induction a using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.add Raw.zero
  dsimp only
  ring

private theorem add_zero_fraction (a : Fraction) : add a zero = a := by
  induction a using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.add Raw.zero
  dsimp only
  ring

private theorem add_comm_fraction (a b : Fraction) : add a b = add b a := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.add
  dsimp only
  ring

private theorem neg_add_cancel_fraction (a : Fraction) :
    add (neg a) a = zero := by
  induction a using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.add Raw.neg Raw.zero
  dsimp only
  ring

private theorem mul_assoc_fraction (a b c : Fraction) :
    mul (mul a b) c = mul a (mul b c) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.mul
  dsimp only
  ring

private theorem one_mul_fraction (a : Fraction) : mul one a = a := by
  induction a using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.mul Raw.one
  dsimp only
  ring

private theorem mul_one_fraction (a : Fraction) : mul a one = a := by
  induction a using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.mul Raw.one
  dsimp only
  ring

private theorem zero_mul_fraction (a : Fraction) : mul zero a = zero := by
  induction a using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.mul Raw.zero
  dsimp only
  ring

private theorem mul_zero_fraction (a : Fraction) : mul a zero = zero := by
  induction a using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.mul Raw.zero
  dsimp only
  ring

private theorem left_distrib_fraction (a b c : Fraction) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.mul Raw.add
  dsimp only
  ring

private theorem right_distrib_fraction (a b c : Fraction) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  induction c using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.mul Raw.add
  dsimp only
  ring

private theorem mul_comm_fraction (a b : Fraction) : mul a b = mul b a := by
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  apply sound_raw
  unfold Raw.Rel Raw.mul
  dsimp only
  ring

@[implicit_reducible] private def commRingFraction : CommRing Fraction where
  add := add
  add_assoc := add_assoc_fraction
  zero := zero
  zero_add := zero_add_fraction
  add_zero := add_zero_fraction
  nsmul := nsmul
  nsmul_zero := by intros; rfl
  nsmul_succ := by intros; rfl
  add_comm := add_comm_fraction
  mul := mul
  mul_assoc := mul_assoc_fraction
  one := one
  one_mul := one_mul_fraction
  mul_one := mul_one_fraction
  npow := fun n a => npow n a
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl
  zero_mul := zero_mul_fraction
  mul_zero := mul_zero_fraction
  left_distrib := left_distrib_fraction
  right_distrib := right_distrib_fraction
  natCast := fun n => ofInt n
  natCast_zero := by
    apply sound_raw
    exact Raw.Rel.refl Raw.zero
  natCast_succ := by
    intro n
    change ofInt (Int.ofNat (n + 1)) = add (ofInt (Int.ofNat n)) one
    apply sound_raw
    unfold Raw.Rel Raw.add Raw.one
    dsimp only [ofInt]
    norm_num
  neg := neg
  sub := sub
  sub_eq_add_neg := by intros; rfl
  zsmul := zsmul
  zsmul_zero' := by intros; rfl
  zsmul_succ' := by intros; rfl
  zsmul_neg' := by intros; rfl
  neg_add_cancel := neg_add_cancel_fraction
  intCast := ofInt
  intCast_ofNat := by intro; rfl
  intCast_negSucc := by
    intro n
    change ofInt (Int.negSucc n) = neg (ofInt (Int.ofNat (n + 1)))
    apply sound_raw
    unfold Raw.Rel Raw.neg
    dsimp only [ofInt]
    simp [Int.negSucc_eq]
  mul_comm := mul_comm_fraction

private theorem inv_zero_fraction : inv zero = zero := by
  apply sound_raw
  unfold Raw.inv Raw.zero
  simp only [↓reduceDIte]
  exact Raw.Rel.refl Raw.zero

private theorem mul_inv_cancel_fraction (a : Fraction) (ha : a ≠ zero) :
    mul a (inv a) = one := by
  induction a using Quotient.inductionOn with
  | _ a =>
      have hnum : a.num ≠ 0 := by
        intro h
        apply ha
        apply sound_raw
        unfold Raw.Rel Raw.zero
        dsimp only
        simp [h]
      apply sound_raw
      unfold Raw.inv
      simp only [hnum, ↓reduceDIte]
      unfold Raw.Rel Raw.mul Raw.one
      dsimp only
      ring

private theorem fraction_nontrivial : zero ≠ one := by
  intro h
  have hrel : Raw.zero.Rel Raw.one :=
    Quotient.exact h
  unfold Raw.Rel Raw.zero Raw.one at hrel
  exact Int.zero_ne_one (by
    simpa only [Int.zero_mul, Int.one_mul] using hrel)

private def exactQuot (num : Int) (den : Nat) : Int :=
  match num with
  | .ofNat n => Int.ofNat (show Nat from n / den)
  | .negSucc n => -Int.ofNat (show Nat from (n + 1) / den)

@[simp] private theorem exactQuot_one (num : Int) :
    exactQuot num 1 = num := by
  cases num with
  | ofNat n =>
      change Int.ofNat (n / 1) = Int.ofNat n
      rw [Nat.div_one]
  | negSucc n =>
      change -Int.ofNat ((n + 1) / 1) = Int.negSucc n
      rw [Nat.div_one]
      simpa [Nat.succ_eq_add_one] using Int.neg_ofNat_succ n

private theorem exactQuot_natAbs (num : Int) (den : Nat) :
    (exactQuot num den).natAbs = num.natAbs / den := by
  cases num with
  | ofNat n => rfl
  | negSucc n =>
      change
        (-Int.ofNat ((n + 1) / den)).natAbs =
          (n + 1) / den
      rw [Int.natAbs_neg, Int.natAbs_ofNat']

private theorem exactQuot_mul {num : Int} {den : Nat}
    (hden : den ∣ num.natAbs) :
    exactQuot num den * (den : Int) = num := by
  cases num with
  | ofNat n =>
      have hden' : den ∣ n := by
        simpa only [Int.natAbs_ofNat'] using hden
      change
        Int.ofNat (n / den) * Int.ofNat den = Int.ofNat n
      calc
        Int.ofNat (n / den) * Int.ofNat den =
            Int.ofNat (n / den * den) := rfl
        _ = Int.ofNat n :=
          congrArg Int.ofNat (Nat.div_mul_cancel hden')
  | negSucc n =>
      have hden' : den ∣ n + 1 := by
        simpa only [Int.natAbs_negSucc] using hden
      change
        -Int.ofNat ((n + 1) / den) * Int.ofNat den =
          Int.negSucc n
      have hcast :
          Int.ofNat ((n + 1) / den) * Int.ofNat den =
            Int.ofNat (n + 1) := by
        calc
          Int.ofNat ((n + 1) / den) * Int.ofNat den =
              Int.ofNat ((n + 1) / den * den) := rfl
          _ = Int.ofNat (n + 1) :=
            congrArg Int.ofNat (Nat.div_mul_cancel hden')
      rw [Int.neg_mul, hcast]
      simpa [Nat.succ_eq_add_one] using Int.neg_ofNat_succ n

private def normalize (num : Int) (den : Nat) (den_ne_zero : den ≠ 0) :
    Rat :=
  let g := num.natAbs.gcd den
  { num := exactQuot num g
    den := den / g
    den_nz := Rat.normalize.den_nz den_ne_zero rfl
    reduced := by
      rw [exactQuot_natAbs]
      exact Nat.coprime_div_gcd_div_gcd
        (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero den_ne_zero)) }

private theorem normalize_cross (num : Int) (den : Nat)
    (den_ne_zero : den ≠ 0) :
    (normalize num den den_ne_zero).num * (den : Int) =
      num * (normalize num den den_ne_zero).den := by
  let g := num.natAbs.gcd den
  have hg_den : g ∣ den :=
    Rat.normalize.dvd_den (num := num) (den := den) (g := g) rfl
  have hnum : exactQuot num g * (g : Int) = num :=
    exactQuot_mul (Nat.gcd_dvd_left num.natAbs den)
  have hden : (den : Int) = (den / g : Nat) * (g : Nat) := by
    exact congrArg Int.ofNat (Nat.div_mul_cancel hg_den).symm
  change exactQuot num g * (den : Int) =
    num * (den / g : Nat)
  rw [hden]
  calc
    exactQuot num g * ((den / g : Nat) * (g : Nat)) =
        (exactQuot num g * (g : Int)) * (den / g : Nat) := by
      ring
    _ = num * (den / g : Nat) := by rw [hnum]

private theorem normalize_reduced (r : Rat) :
    normalize r.num r.den r.den_ne_zero = r := by
  have hgcd : r.num.natAbs.gcd r.den = 1 :=
    r.reduced
  apply Rat.ext
  · simp [normalize, hgcd]
  · simp [normalize, hgcd]

private def divInt (num den : Int) : Rat :=
  match den with
  | .ofNat 0 => 0
  | .ofNat (n + 1) => normalize num (n + 1) (Nat.succ_ne_zero n)
  | .negSucc n => normalize (-num) (n + 1) (Nat.succ_ne_zero n)

private theorem divInt_cross {num den : Int} (den_ne_zero : den ≠ 0) :
    (divInt num den).num * den = num * (divInt num den).den := by
  cases den with
  | ofNat n =>
      cases n with
      | zero => exact False.elim (den_ne_zero rfl)
      | succ n =>
          simpa [divInt] using
            normalize_cross num (n + 1) (Nat.succ_ne_zero n)
  | negSucc n =>
      have h :=
        normalize_cross (-num) (n + 1) (Nat.succ_ne_zero n)
      change
        (normalize (-num) (n + 1) (Nat.succ_ne_zero n)).num *
            Int.negSucc n =
          num *
            (normalize (-num) (n + 1) (Nat.succ_ne_zero n)).den
      rw [Int.negSucc_eq]
      calc
        (normalize (-num) (n + 1) (Nat.succ_ne_zero n)).num *
              -((n : Int) + 1) =
            -((normalize (-num) (n + 1) (Nat.succ_ne_zero n)).num *
              ((n + 1 : Nat) : Int)) := by
                push_cast
                ring
        _ = -((-num) *
              (normalize (-num) (n + 1) (Nat.succ_ne_zero n)).den) :=
            congrArg Neg.neg h
        _ = num *
              (normalize (-num) (n + 1) (Nat.succ_ne_zero n)).den := by
            ring

private def Raw.ofRat (r : Rat) : Raw :=
  ⟨r.num, r.den, by
    exact Int.ofNat_ne_zero.mpr r.den_ne_zero⟩

private theorem divInt_rel (a : Raw) :
    (Raw.ofRat (divInt a.num a.den)).Rel a := by
  exact divInt_cross a.den_ne_zero

private theorem rat_eq_of_cross {a b : Rat}
    (h : a.num * (b.den : Int) = b.num * (a.den : Int)) :
    a = b := by
  have habs := congrArg Int.natAbs h
  have hnat :
      a.num.natAbs * b.den = b.num.natAbs * a.den := by
    simpa [Int.natAbs_mul] using habs
  have had_dvd_bd : a.den ∣ b.den := by
    apply a.reduced.symm.dvd_of_dvd_mul_left
    refine ⟨b.num.natAbs, ?_⟩
    simpa [Nat.mul_comm] using hnat
  have hbd_dvd_ad : b.den ∣ a.den := by
    apply b.reduced.symm.dvd_of_dvd_mul_left
    refine ⟨a.num.natAbs, ?_⟩
    simpa [Nat.mul_comm] using hnat.symm
  have hden : a.den = b.den :=
    Nat.dvd_antisymm had_dvd_bd hbd_dvd_ad
  have hnum : a.num = b.num := by
    apply Int.eq_of_mul_eq_mul_right
      (Int.ofNat_ne_zero.mpr a.den_ne_zero)
    calc
      a.num * (a.den : Int) =
          a.num * (b.den : Int) :=
        congrArg (fun d : Nat => a.num * (d : Int)) hden
      _ = b.num * (a.den : Int) := h
  exact Rat.ext hnum hden

private def toFraction (r : Rat) : Fraction :=
  Quotient.mk rawSetoid (Raw.ofRat r)

private def fromFraction : Fraction → Rat :=
  Quotient.lift (fun a => divInt a.num a.den) (by
    intro a b h
    apply rat_eq_of_cross
    have ha := divInt_rel a
    have hb := divInt_rel b
    exact Raw.Rel.trans (Raw.Rel.trans ha h) (Raw.Rel.symm' hb))

private theorem from_to_fraction (r : Rat) :
    fromFraction (toFraction r) = r := by
  rcases r with ⟨num, den, den_ne_zero, reduced⟩
  change divInt num (den : Int) =
    ⟨num, den, den_ne_zero, reduced⟩
  cases den with
  | zero => exact False.elim (den_ne_zero rfl)
  | succ n =>
      change normalize num (n + 1) (Nat.succ_ne_zero n) =
        ⟨num, n + 1, den_ne_zero, reduced⟩
      exact normalize_reduced
        ⟨num, n + 1, den_ne_zero, reduced⟩

private theorem to_from_fraction (q : Fraction) :
    toFraction (fromFraction q) = q := by
  induction q using Quotient.inductionOn with
  | _ a =>
      apply Quotient.sound
      exact divInt_rel a

private def fractionEquivRat : Fraction ≃ Rat where
  toFun := fromFraction
  invFun := toFraction
  left_inv := to_from_fraction
  right_inv := from_to_fraction

@[implicit_reducible] private def fieldFraction : Field Fraction where
  __ := commRingFraction
  inv := inv
  div := div
  div_eq_mul_inv := by intros; rfl
  zpow := fun n a => zpow n a
  zpow_zero' := by intro; rfl
  zpow_succ' := by
    intro n a
    cases n <;> rfl
  zpow_neg' := by
    intro n a
    cases n <;> rfl
  exists_pair_ne := ⟨zero, one, fraction_nontrivial⟩
  mul_inv_cancel := mul_inv_cancel_fraction
  inv_zero := inv_zero_fraction
  nnratCast := fun q =>
    div (ofInt q.num) (ofInt q.den)
  nnratCast_def := by
    intro q
    rfl
  nnqsmul := fun q a =>
    mul (div (ofInt q.num) (ofInt q.den)) a
  nnqsmul_def := by
    intros
    rfl
  ratCast := fun q =>
    div (ofInt q.num) (ofInt q.den)
  ratCast_def := by
    intro q
    rfl
  qsmul := fun q a =>
    mul (div (ofInt q.num) (ofInt q.den)) a
  qsmul_def := by
    intros
    rfl

local instance : Field Fraction :=
  fieldFraction

@[implicit_reducible] private def commRingRat : CommRing Rat :=
  Equiv.commRing fractionEquivRat.symm

private theorem toFraction_eq_div (q : Rat) :
    toFraction q = div (ofInt q.num) (ofInt q.den) := by
  apply Quotient.sound
  unfold Raw.inv
  simp only [Int.ofNat_ne_zero.mpr q.den_ne_zero, ↓reduceDIte]
  change
    q.num * (1 * (q.den : Int)) =
      (q.num * 1) * (q.den : Int)
  ring

private theorem toFraction_nnrat_eq_div (q : NNRat) :
    toFraction q =
      div (ofInt q.num) (ofInt q.den) := by
  have hnum_nonneg : 0 ≤ (q : Rat).num :=
    Rat.num_nonneg.mpr q.property
  have hnum : ((q.num : Nat) : Int) = (q : Rat).num := by
    change Int.ofNat (q : Rat).num.natAbs = (q : Rat).num
    exact Int.ofNat_natAbs_of_nonneg hnum_nonneg
  simpa only [NNRat.den, hnum] using
    toFraction_eq_div (q : Rat)

private theorem toFraction_natCast (n : Nat) :
    toFraction (n : Rat) = ofInt n := by
  apply Quotient.sound
  change (n : Int) * 1 = (n : Int) * 1
  rfl

private theorem toFraction_intCast (z : Int) :
    toFraction (z : Rat) = ofInt z := by
  apply Quotient.sound
  change z * 1 = z * 1
  rfl

/--
A choice-free field dictionary on Lean's canonical `Rat` representation.
Its operations are transported from the integer-fraction quotient and are
extensionally the usual rational operations.
-/
@[implicit_reducible] public def field : Field Rat := by
  let e := fractionEquivRat.symm
  let cr := commRingRat
  let invR : Inv Rat :=
    @Equiv.Inv Rat Fraction e fieldFraction.toInv
  let divR := e.div
  let zpowR : ZPow Rat :=
    @ZPow.ofPow Rat (e.pow Int)
  let nnratCastR : NNRatCast Rat := ⟨fun q => q⟩
  let ratCastR : RatCast Rat := ⟨fun q => q⟩
  letI : Zero Rat := cr.toZero
  letI : One Rat := cr.toOne
  letI : Add Rat := cr.toAdd
  letI : Mul Rat := cr.toMul
  letI : Neg Rat := cr.toNeg
  letI : Sub Rat := cr.toSub
  letI : NSMul Rat := cr.toNSMul
  letI : ZSMul Rat := cr.toZSMul
  letI : NPow Rat := cr.toNPow
  letI : NatCast Rat := cr.toNatCast
  letI : IntCast Rat := cr.toIntCast
  letI : CommRing Rat := cr
  letI : Inv Rat := invR
  letI : Div Rat := divR
  letI : ZPow Rat := zpowR
  letI : Pow Rat Nat := @NPow.toPow Rat cr.toNPow
  letI : Pow Rat Int := @ZPow.toPow Rat zpowR
  letI : NNRatCast Rat := nnratCastR
  letI : RatCast Rat := ratCastR
  letI : Nontrivial Rat := Rat.nontrivial
  have map_zero :
      e (@Zero.zero Rat cr.toZero) =
        @Zero.zero Fraction fieldFraction.toZero :=
    by
      change
        e (e.symm (@Zero.zero Fraction fieldFraction.toZero)) =
          @Zero.zero Fraction fieldFraction.toZero
      exact e.apply_symm_apply _
  have map_one :
      e (@One.one Rat cr.toOne) =
        @One.one Fraction fieldFraction.toOne :=
    by
      change
        e (e.symm (@One.one Fraction fieldFraction.toOne)) =
          @One.one Fraction fieldFraction.toOne
      exact e.apply_symm_apply _
  have map_mul (a b : Rat) :
      e (@Mul.mul Rat cr.toMul a b) =
        @Mul.mul Fraction fieldFraction.toMul (e a) (e b) :=
    by
      have hmul :
          @Mul.mul Rat cr.toMul a b =
            e.symm
              (@Mul.mul Fraction fieldFraction.toMul
                (e a) (e b)) := by
        rfl
      rw [hmul]
      exact e.apply_symm_apply _
  have map_inv (a : Rat) :
      e (@Inv.inv Rat invR a) =
        @Inv.inv Fraction fieldFraction.toInv (e a) :=
    by
      change
        e (e.symm
          (@Inv.inv Fraction fieldFraction.toInv (e a))) =
            @Inv.inv Fraction fieldFraction.toInv (e a)
      exact e.apply_symm_apply _
  have map_div (a b : Rat) :
      e (@Div.div Rat divR a b) =
        @Div.div Fraction fieldFraction.toDiv (e a) (e b) :=
    by
      change
        e (e.symm
          (@Div.div Fraction fieldFraction.toDiv (e a) (e b))) =
            @Div.div Fraction fieldFraction.toDiv (e a) (e b)
      exact e.apply_symm_apply _
  have map_zpow (a : Rat) (z : Int) :
      e (@ZPow.zpow Rat zpowR z a) =
        @ZPow.zpow Fraction fieldFraction.toZPow z (e a) :=
    by
      have hpow :
          @ZPow.zpow Rat zpowR z a =
            e.symm
              (@ZPow.zpow Fraction fieldFraction.toZPow
                z (e a)) := by
        rfl
      rw [hpow]
      exact e.apply_symm_apply _
  exact @Field.mk Rat cr invR divR zpowR
    (div_eq_mul_inv := by
        intro a b
        change
          @Div.div Rat divR a b =
            @Mul.mul Rat cr.toMul a (@Inv.inv Rat invR b)
        apply e.injective
        rw [map_div, map_mul, map_inv]
        exact fieldFraction.div_eq_mul_inv (e a) (e b))
    (zpow_zero' := by
        intro a
        change
          @ZPow.zpow Rat zpowR 0 a =
            @One.one Rat cr.toOne
        apply e.injective
        rw [map_zpow, map_one]
        exact fieldFraction.zpow_zero' (e a))
    (zpow_succ' := by
        intro n a
        change
          @ZPow.zpow Rat zpowR (n.succ : Int) a =
            @Mul.mul Rat cr.toMul
              (@ZPow.zpow Rat zpowR (n : Int) a) a
        apply e.injective
        rw [map_zpow, map_mul, map_zpow]
        exact fieldFraction.zpow_succ' n (e a))
    (zpow_neg' := by
        intro n a
        change
          @ZPow.zpow Rat zpowR (Int.negSucc n) a =
            @Inv.inv Rat invR
              (@ZPow.zpow Rat zpowR (n.succ : Int) a)
        apply e.injective
        rw [map_zpow, map_inv, map_zpow]
        exact fieldFraction.zpow_neg' n (e a))
    (toNontrivial := Rat.nontrivial)
    (toNNRatCast := nnratCastR)
    (toRatCast := ratCastR)
    (mul_inv_cancel := by
        intro a ha
        change
          @Mul.mul Rat cr.toMul a (@Inv.inv Rat invR a) =
            @One.one Rat cr.toOne
        apply e.injective
        rw [map_mul, map_inv, map_one]
        apply fieldFraction.mul_inv_cancel
        intro hea
        apply ha
        apply e.injective
        exact hea.trans map_zero.symm)
    (inv_zero := by
        change
          @Inv.inv Rat invR (@Zero.zero Rat cr.toZero) =
            @Zero.zero Rat cr.toZero
        apply e.injective
        rw [map_inv, map_zero]
        exact fieldFraction.inv_zero)
    (nnratCast_def := by
        intro q
        refine e.injective ?_
        calc
          e (q : Rat) = toFraction q := rfl
          _ = div (ofInt q.num) (ofInt q.den) :=
            toFraction_nnrat_eq_div q
          _ = e (@Div.div Rat divR
              (@Nat.cast Rat cr.toNatCast q.num)
              (@Nat.cast Rat cr.toNatCast q.den)) := by
            have hnum :
                e (@Nat.cast Rat cr.toNatCast q.num) =
                  (q.num : Fraction) :=
              by
                change e (e.symm (q.num : Fraction)) =
                  (q.num : Fraction)
                exact e.apply_symm_apply _
            have hden :
                e (@Nat.cast Rat cr.toNatCast q.den) =
                  (q.den : Fraction) :=
              by
                change e (e.symm (q.den : Fraction)) =
                  (q.den : Fraction)
                exact e.apply_symm_apply _
            have hnum' :
                ofInt (q.num : Int) =
                  e (@Nat.cast Rat cr.toNatCast q.num) :=
              hnum.symm
            have hden' :
                ofInt (q.den : Int) =
                  e (@Nat.cast Rat cr.toNatCast q.den) :=
              hden.symm
            rw [hnum', hden']
            exact
              (map_div
                (@Nat.cast Rat cr.toNatCast q.num)
                (@Nat.cast Rat cr.toNatCast q.den)).symm)
    (nnqsmul := fun q a =>
      @Mul.mul Rat cr.toMul (q : Rat) a)
    (nnqsmul_def := by
        intros
        rfl)
    (ratCast_def := by
        intro q
        refine e.injective ?_
        calc
          e q = toFraction q := rfl
          _ = div (ofInt q.num) (ofInt q.den) :=
            toFraction_eq_div q
          _ = e (@Div.div Rat divR
              (@Int.cast Rat cr.toIntCast q.num)
              (@Nat.cast Rat cr.toNatCast q.den)) := by
            have hnum :
                e (@Int.cast Rat cr.toIntCast q.num) =
                  (q.num : Fraction) :=
              by
                change e (e.symm (q.num : Fraction)) =
                  (q.num : Fraction)
                exact e.apply_symm_apply _
            have hden :
                e (@Nat.cast Rat cr.toNatCast q.den) =
                  (q.den : Fraction) :=
              by
                change e (e.symm (q.den : Fraction)) =
                  (q.den : Fraction)
                exact e.apply_symm_apply _
            have hnum' :
                ofInt q.num =
                  e (@Int.cast Rat cr.toIntCast q.num) :=
              hnum.symm
            have hden' :
                ofInt (q.den : Int) =
                  e (@Nat.cast Rat cr.toNatCast q.den) :=
              hden.symm
            rw [hnum', hden']
            exact
              (map_div
                (@Int.cast Rat cr.toIntCast q.num)
                (@Nat.cast Rat cr.toNatCast q.den)).symm)
    (qsmul := fun q a =>
      @Mul.mul Rat cr.toMul q a)
    (qsmul_def := by
        intros
        rfl)

private theorem toFraction_zero_standard :
    toFraction (0 : Rat) = @Zero.zero Fraction fieldFraction.toZero := by
  apply Quotient.sound
  rfl

private theorem toFraction_one_standard :
    toFraction (1 : Rat) = @One.one Fraction fieldFraction.toOne := by
  apply Quotient.sound
  rfl

private theorem toFraction_add_standard (a b : Rat) :
    toFraction (a + b) =
      @Add.add Fraction fieldFraction.toAdd
        (toFraction a) (toFraction b) := by
  apply Quotient.sound
  change
    (a + b).num * ((a.den * b.den : Nat) : Int) =
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
        ((a + b).den : Int)
  simpa only [Int.natCast_mul, Int.mul_assoc] using
    Rat.add_num_den' a b

private theorem toFraction_neg_standard (a : Rat) :
    toFraction (-a) =
      @Neg.neg Fraction fieldFraction.toNeg (toFraction a) := by
  apply Quotient.sound
  change
    (-a).num * (a.den : Int) =
      -a.num * ((-a).den : Int)
  rw [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den]

private theorem toFraction_mul_standard (a b : Rat) :
    toFraction (a * b) =
      @Mul.mul Fraction fieldFraction.toMul
        (toFraction a) (toFraction b) := by
  apply Quotient.sound
  change
    (a * b).num * ((a.den * b.den : Nat) : Int) =
      (a.num * b.num) * ((a * b).den : Int)
  simpa only [Int.natCast_mul, Int.mul_assoc] using
    Rat.mul_num_den' a b

/-
These non-public bridge lemmas are available to implementation modules through
`import all`.  They keep the choice-free runtime dictionary proof-equal to the
canonical `Rat` operations without expanding the stable core facade.
-/
theorem field_zero_eq_standard :
    @Zero.zero Rat field.toZero = (0 : Rat) := by
  change
    fractionEquivRat (@Zero.zero Fraction fieldFraction.toZero) =
      (0 : Rat)
  rw [← toFraction_zero_standard]
  exact fractionEquivRat.apply_symm_apply (0 : Rat)

theorem field_one_eq_standard :
    @One.one Rat field.toOne = (1 : Rat) := by
  change
    fractionEquivRat (@One.one Fraction fieldFraction.toOne) =
      (1 : Rat)
  rw [← toFraction_one_standard]
  exact fractionEquivRat.apply_symm_apply (1 : Rat)

theorem field_add_eq_standard (a b : Rat) :
    @Add.add Rat field.toAdd a b = a + b := by
  change
    fractionEquivRat
        (@Add.add Fraction fieldFraction.toAdd
          (toFraction a) (toFraction b)) =
      a + b
  rw [← toFraction_add_standard]
  exact fractionEquivRat.apply_symm_apply (a + b)

theorem field_neg_eq_standard (a : Rat) :
    @Neg.neg Rat field.toNeg a = -a := by
  change
    fractionEquivRat
        (@Neg.neg Fraction fieldFraction.toNeg (toFraction a)) =
      -a
  rw [← toFraction_neg_standard]
  exact fractionEquivRat.apply_symm_apply (-a)

theorem field_mul_eq_standard (a b : Rat) :
    @Mul.mul Rat field.toMul a b = a * b := by
  change
    fractionEquivRat
        (@Mul.mul Fraction fieldFraction.toMul
          (toFraction a) (toFraction b)) =
      a * b
  rw [← toFraction_mul_standard]
  exact fractionEquivRat.apply_symm_apply (a * b)

theorem field_inv_eq_standard (a : Rat) :
    @Inv.inv Rat field.toInv a = a⁻¹ := by
  by_cases ha : a = 0
  · subst a
    calc
      @Inv.inv Rat field.toInv (0 : Rat) =
          @Zero.zero Rat field.toZero :=
        field.inv_zero
      _ = (0 : Rat) :=
        field_zero_eq_standard
      _ = (0 : Rat)⁻¹ :=
        inv_zero.symm
  · have haRuntime :
        a ≠ @Zero.zero Rat field.toZero := by
      rw [field_zero_eq_standard]
      exact ha
    have hRuntime :
        a * @Inv.inv Rat field.toInv a = 1 := by
      rw [← field_mul_eq_standard, ← field_one_eq_standard]
      exact field.mul_inv_cancel a haRuntime
    calc
      @Inv.inv Rat field.toInv a =
          1 * @Inv.inv Rat field.toInv a := by
            rw [one_mul]
      _ = (a⁻¹ * a) * @Inv.inv Rat field.toInv a := by
            rw [inv_mul_cancel₀ ha]
      _ = a⁻¹ * (a * @Inv.inv Rat field.toInv a) := by
            rw [mul_assoc]
      _ = a⁻¹ * 1 := by rw [hRuntime]
      _ = a⁻¹ := mul_one _

end ConstructiveRat

end NormalForms
