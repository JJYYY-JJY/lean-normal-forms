/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Tactic

/-! # Fixed Monomial Envelopes -/

public section

namespace NormalForms.Research.KannanBachem

/-- A common base, at least two, for bivariate fixed-polynomial bounds. -/
@[expose] public def polyBase (dimension inputBits : Nat) : Nat :=
  dimension + inputBits + 2

public theorem polyBase_two_le (dimension inputBits : Nat) :
    2 ≤ polyBase dimension inputBits := by
  unfold polyBase
  omega

/--
`f` has a fixed monomial envelope.  The exponent is independent of both
arguments; coefficient one is enough because `polyBase` is at least two.
-/
public structure PolyEnvelope
    (f : Nat → Nat → Nat) where
  degree : Nat
  bound : ∀ dimension inputBits,
    f dimension inputBits ≤ polyBase dimension inputBits ^ degree

namespace PolyEnvelope

@[expose] public def of_le {f g : Nat → Nat → Nat}
    (hg : PolyEnvelope g)
    (hle : ∀ dimension inputBits,
      f dimension inputBits ≤ g dimension inputBits) :
    PolyEnvelope f :=
  ⟨hg.degree, fun dimension inputBits ↦
    (hle dimension inputBits).trans (hg.bound dimension inputBits)⟩

@[expose] public def of_eq {f g : Nat → Nat → Nat}
    (hg : PolyEnvelope g)
    (heq : ∀ dimension inputBits,
      f dimension inputBits = g dimension inputBits) :
    PolyEnvelope f :=
  of_le hg fun dimension inputBits ↦ (heq dimension inputBits).le

public theorem pow_mono_degree (dimension inputBits : Nat)
    {smaller larger : Nat} (hle : smaller ≤ larger) :
    polyBase dimension inputBits ^ smaller ≤
      polyBase dimension inputBits ^ larger :=
  Nat.pow_le_pow_right (by
    exact (polyBase_two_le dimension inputBits).trans' (by omega)) hle

@[expose] public def constant (value : Nat) :
    PolyEnvelope (fun _ _ ↦ value) := by
  refine ⟨value, ?_⟩
  intro dimension inputBits
  let base := polyBase dimension inputBits
  have baseOne : 1 ≤ base := (polyBase_two_le _ _).trans' (by omega)
  calc
    value ≤ base * value := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right value baseOne
    _ ≤ base ^ value := by
      exact Nat.mul_le_pow (by
        have : 2 ≤ base := polyBase_two_le _ _
        omega) value

@[expose] public def dimension :
    PolyEnvelope (fun dimension _ ↦ dimension) :=
  ⟨1, by
    intro dimension inputBits
    simp only [pow_one, polyBase]
    omega⟩

@[expose] public def inputBits :
    PolyEnvelope (fun _ inputBits ↦ inputBits) :=
  ⟨1, by
    intro dimension inputBits
    simp only [pow_one, polyBase]
    omega⟩

@[expose] public def add {f g : Nat → Nat → Nat}
    (hf : PolyEnvelope f) (hg : PolyEnvelope g) :
    PolyEnvelope (fun dimension inputBits ↦
      f dimension inputBits + g dimension inputBits) := by
  refine ⟨Nat.max hf.degree hg.degree + 1, ?_⟩
  intro dimension inputBits
  let base := polyBase dimension inputBits
  have fBound : f dimension inputBits ≤
      base ^ Nat.max hf.degree hg.degree :=
    (hf.bound _ _).trans <|
      pow_mono_degree dimension inputBits (le_max_left _ _)
  have gBound : g dimension inputBits ≤
      base ^ Nat.max hf.degree hg.degree :=
    (hg.bound _ _).trans <|
      pow_mono_degree dimension inputBits (le_max_right _ _)
  have baseTwo : 2 ≤ base := polyBase_two_le _ _
  calc
    f dimension inputBits + g dimension inputBits ≤
        2 * base ^ Nat.max hf.degree hg.degree := by omega
    _ ≤ base * base ^ Nat.max hf.degree hg.degree := by gcongr
    _ = base ^ (Nat.max hf.degree hg.degree + 1) := by
      rw [pow_succ, Nat.mul_comm]

@[expose] public def mul {f g : Nat → Nat → Nat}
    (hf : PolyEnvelope f) (hg : PolyEnvelope g) :
    PolyEnvelope (fun dimension inputBits ↦
      f dimension inputBits * g dimension inputBits) := by
  refine ⟨hf.degree + hg.degree, ?_⟩
  intro dimension inputBits
  calc
    f dimension inputBits * g dimension inputBits ≤
        polyBase dimension inputBits ^ hf.degree *
          polyBase dimension inputBits ^ hg.degree :=
      Nat.mul_le_mul (hf.bound _ _) (hg.bound _ _)
    _ = polyBase dimension inputBits ^ (hf.degree + hg.degree) := by
      rw [pow_add]

@[expose] public def max {f g : Nat → Nat → Nat}
    (hf : PolyEnvelope f) (hg : PolyEnvelope g) :
    PolyEnvelope (fun dimension inputBits ↦
      Nat.max (f dimension inputBits) (g dimension inputBits)) := by
  refine ⟨Nat.max hf.degree hg.degree, ?_⟩
  intro dimension inputBits
  exact max_le
    ((hf.bound _ _).trans <|
      pow_mono_degree dimension inputBits (le_max_left _ _))
    ((hg.bound _ _).trans <|
      pow_mono_degree dimension inputBits (le_max_right _ _))

@[expose] public def pow {f : Nat → Nat → Nat}
    (hf : PolyEnvelope f) (exponent : Nat) :
    PolyEnvelope (fun dimension inputBits ↦
      f dimension inputBits ^ exponent) := by
  refine ⟨hf.degree * exponent, ?_⟩
  intro dimension inputBits
  calc
    f dimension inputBits ^ exponent ≤
        (polyBase dimension inputBits ^ hf.degree) ^ exponent :=
      Nat.pow_le_pow_left (hf.bound _ _) exponent
    _ = polyBase dimension inputBits ^ (hf.degree * exponent) := by
      rw [pow_mul]

@[expose] public def sub {f g : Nat → Nat → Nat}
    (hf : PolyEnvelope f) :
    PolyEnvelope (fun dimension inputBits ↦
      f dimension inputBits - g dimension inputBits) :=
  of_le hf fun _dimension _inputBits ↦ Nat.sub_le _ _

public theorem natSize_le_succ (value : Nat) :
    value.size ≤ value + 1 := by
  rw [Nat.size_le]
  exact lt_of_lt_of_le (by omega)
    (Nat.mul_le_pow (by decide : (2 : Nat) ≠ 1) (value + 1))

@[expose] public def natSize {f : Nat → Nat → Nat}
    (hf : PolyEnvelope f) :
    PolyEnvelope (fun dimension inputBits ↦
      Nat.size (f dimension inputBits)) := by
  let successor :=
    add hf (constant 1)
  refine ⟨successor.degree, ?_⟩
  intro dimension inputBits
  exact (natSize_le_succ _).trans (successor.bound _ _)

/-- Fixed-polynomial substitution into both arguments of an envelope. -/
@[expose] public def monotoneSubstitution
    {outer left right : Nat → Nat → Nat}
    (houter : PolyEnvelope outer)
    (hleft : PolyEnvelope left)
    (hright : PolyEnvelope right) :
    PolyEnvelope (fun dimension inputBits ↦
      outer (left dimension inputBits) (right dimension inputBits)) := by
  let innerDegree := Nat.max hleft.degree hright.degree
  refine ⟨(innerDegree + 2) * houter.degree, ?_⟩
  intro dimension inputBits
  let base := polyBase dimension inputBits
  have leftBound :
      left dimension inputBits ≤ base ^ innerDegree :=
    (hleft.bound _ _).trans <|
      pow_mono_degree dimension inputBits (le_max_left _ _)
  have rightBound :
      right dimension inputBits ≤ base ^ innerDegree :=
    (hright.bound _ _).trans <|
      pow_mono_degree dimension inputBits (le_max_right _ _)
  have baseTwo : 2 ≤ base := polyBase_two_le _ _
  have powerOne : 1 ≤ base ^ innerDegree := by
    exact Nat.one_le_pow _ _ (by omega)
  have innerBase :
      polyBase (left dimension inputBits) (right dimension inputBits) ≤
        base ^ (innerDegree + 2) := by
    unfold polyBase
    calc
      left dimension inputBits + right dimension inputBits + 2 ≤
          4 * base ^ innerDegree := by omega
      _ ≤ base ^ 2 * base ^ innerDegree := by
        gcongr
        simpa [pow_two] using Nat.mul_le_mul baseTwo baseTwo
      _ = base ^ (innerDegree + 2) := by
        rw [pow_add]
        exact Nat.mul_comm _ _
  calc
    outer (left dimension inputBits) (right dimension inputBits) ≤
        polyBase (left dimension inputBits) (right dimension inputBits) ^
          houter.degree :=
      houter.bound _ _
    _ ≤ (base ^ (innerDegree + 2)) ^ houter.degree :=
      Nat.pow_le_pow_left innerBase houter.degree
    _ = base ^ ((innerDegree + 2) * houter.degree) := by
      rw [pow_mul]

/--
An additive dimension recursion remains fixed-polynomial when its base and
per-level increment do.
-/
@[expose] public def dimensionRecursion
    {f step : Nat → Nat → Nat}
    (hbase : PolyEnvelope (fun _ inputBits ↦ f 0 inputBits))
    (hstep : PolyEnvelope step)
    (recurrence : ∀ dimension inputBits,
      f (dimension + 1) inputBits ≤
        f dimension inputBits + step (dimension + 1) inputBits) :
    PolyEnvelope f := by
  let degree := Nat.max hbase.degree hstep.degree
  refine ⟨degree + 2, ?_⟩
  intro dimension inputBits
  have accumulated :
      f dimension inputBits ≤
        f 0 inputBits +
          dimension *
            polyBase dimension inputBits ^ hstep.degree := by
    induction dimension with
    | zero => simp
    | succ dimension ih =>
        have stepBound := hstep.bound (dimension + 1) inputBits
        have baseMono :
            polyBase dimension inputBits ≤
              polyBase (dimension + 1) inputBits := by
          unfold polyBase
          omega
        have powerMono :
            polyBase dimension inputBits ^ hstep.degree ≤
              polyBase (dimension + 1) inputBits ^ hstep.degree :=
          Nat.pow_le_pow_left baseMono hstep.degree
        have ihMono :
            f dimension inputBits ≤
              f 0 inputBits +
                dimension *
                  polyBase (dimension + 1) inputBits ^ hstep.degree :=
          ih.trans <|
            Nat.add_le_add_left
              (Nat.mul_le_mul_left dimension powerMono) _
        calc
          f (dimension + 1) inputBits ≤
              f dimension inputBits +
                step (dimension + 1) inputBits :=
            recurrence dimension inputBits
          _ ≤ (f 0 inputBits +
                  dimension *
                    polyBase (dimension + 1) inputBits ^ hstep.degree) +
                polyBase (dimension + 1) inputBits ^ hstep.degree :=
            Nat.add_le_add ihMono stepBound
          _ = f 0 inputBits +
              (dimension + 1) *
                polyBase (dimension + 1) inputBits ^ hstep.degree := by
            ring
  let base := polyBase dimension inputBits
  have baseBound :
      f 0 inputBits ≤ base ^ degree :=
    (hbase.bound dimension inputBits).trans <|
      pow_mono_degree dimension inputBits (le_max_left _ _)
  have stepPower :
      base ^ hstep.degree ≤ base ^ degree :=
    pow_mono_degree dimension inputBits (le_max_right _ _)
  have dimensionBound : dimension ≤ base := by
    unfold base polyBase
    omega
  have baseTwo : 2 ≤ base := polyBase_two_le _ _
  have oneAddBase : 1 + base ≤ base * base := by
    calc
      1 + base ≤ base + base := by omega
      _ ≤ base * base := by
        simpa [two_mul] using Nat.mul_le_mul_right base baseTwo
  calc
    f dimension inputBits ≤
        f 0 inputBits + dimension * base ^ hstep.degree :=
      accumulated
    _ ≤ base ^ degree + base * base ^ degree := by
      exact Nat.add_le_add baseBound
        (Nat.mul_le_mul dimensionBound stepPower)
    _ ≤ base ^ 2 * base ^ degree := by
      rw [show base ^ degree + base * base ^ degree =
          (1 + base) * base ^ degree by ring]
      simpa [pow_two] using
        Nat.mul_le_mul_right (base ^ degree) oneAddBase
    _ = base ^ (degree + 2) := by
      rw [pow_add]
      exact Nat.mul_comm _ _

/-- A bounded prefix sum is the canonical additive dimension recursion. -/
@[expose] public def boundedSum {f : Nat → Nat → Nat}
    (hf : PolyEnvelope f) :
    PolyEnvelope (fun dimension inputBits ↦
      ∑ index ∈ Finset.range dimension, f (index + 1) inputBits) := by
  apply dimensionRecursion (constant 0) hf
  intro dimension inputBits
  rw [Finset.sum_range_succ]

end PolyEnvelope

end NormalForms.Research.KannanBachem
