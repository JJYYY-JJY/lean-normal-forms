/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.Data.Num.ZNum

/-!
# Binary Sign-Magnitude Integers and Cost Results

This research line uses mathlib's explicit binary `ZNum` representation:

* `ZNum.zero` represents zero;
* `ZNum.pos p` represents the positive `PosNum` magnitude `p`;
* `ZNum.neg p` represents the negative `PosNum` magnitude `p`.

`PosNum` is an inductive binary word, not a native `Int`. Consequently its
addition, multiplication, and division definitions are recursive bit
algorithms. Later modules attach an explicit bit-operation count to those
reference computations and prove agreement with standard `Int` operations.

The four acceptance tiers below prevent a ring-operation count or native wall
time from being reported as a bit-complexity theorem.
-/

public section

namespace NormalForms.Research.BitCost

/--
The four distinct levels of an algorithmic complexity claim.

The constructors are ordered by logical strength only as a project
vocabulary; no implication between adjacent tiers is automatic.
-/
public inductive AcceptanceTier where
  /-- The returned mathematical value satisfies its specification. -/
  | semanticCorrectness
  /-- The number of abstract ring operations is bounded. -/
  | ringOperationCount
  /-- Every intermediate coefficient has a proved bit-length bound. -/
  | coefficientBitLength
  /-- Primitive binary operations have explicit bit-operation bounds. -/
  | bitComplexity
  deriving DecidableEq, Repr

/--
Canonical explicit binary sign-magnitude integers.

This abbreviation deliberately exposes `ZNum` rather than wrapping it in a
second representation. `ZNum` already has exactly one zero constructor and
positive/negative constructors carrying canonical positive binary words.
-/
public abbrev SignMagnitude := ZNum

namespace SignMagnitude

/-- Interpret an explicit sign-magnitude word as the standard Lean integer. -/
@[expose] public def value (a : SignMagnitude) : Int :=
  (a : Int)

/-- Encode a standard integer as a canonical binary sign-magnitude word. -/
@[expose] public def ofInt (a : Int) : SignMagnitude :=
  (a : ZNum)

/-- The number of magnitude bits; zero has bit length zero. -/
@[expose] public def bitLength : SignMagnitude → Nat
  | .zero => 0
  | .pos magnitude => magnitude.natSize
  | .neg magnitude => magnitude.natSize

/-- The unsigned binary magnitude. -/
@[expose] public def magnitude : SignMagnitude → Num
  | .zero => 0
  | .pos magnitude => .pos magnitude
  | .neg magnitude => .pos magnitude

@[simp] public theorem value_ofInt (a : Int) :
    (ofInt a).value = a :=
  ZNum.to_of_int a

@[simp] public theorem ofInt_value (a : SignMagnitude) :
    ofInt a.value = a :=
  ZNum.of_to_int a

@[simp] public theorem value_zero :
    value 0 = 0 :=
  rfl

@[simp] public theorem value_neg (a : SignMagnitude) :
    value (-a) = -value a :=
  ZNum.cast_zneg a

@[simp] public theorem bitLength_neg (a : SignMagnitude) :
    (-a).bitLength = a.bitLength := by
  cases a <;> rfl

@[simp] public theorem magnitude_value (a : SignMagnitude) :
    (a.magnitude : Nat) = Int.natAbs a.value := by
  exact ZNum.abs_to_nat a

@[simp] public theorem bitLength_zero :
    bitLength 0 = 0 :=
  rfl

public theorem bitLength_eq_natSize_magnitude (a : SignMagnitude) :
    a.bitLength = a.magnitude.natSize := by
  cases a <;> rfl

public theorem bitLength_eq_natSize_natAbs (a : SignMagnitude) :
    a.bitLength = Nat.size (Int.natAbs a.value) := by
  rw [bitLength_eq_natSize_magnitude, Num.natSize_to_nat]
  congr 1
  exact magnitude_value a

end SignMagnitude

/-- A value paired with the exact cost assigned by the reference model. -/
public structure WithCost (α : Type*) where
  value : α
  cost : Nat
  deriving DecidableEq, Repr

namespace WithCost

/-- A cost-free result, useful for representation-only steps. -/
@[expose] public def pure (value : α) : WithCost α :=
  { value, cost := 0 }

/-- Apply a pure function without changing the accumulated cost. -/
@[expose] public def map (f : α → β) (result : WithCost α) : WithCost β :=
  { value := f result.value, cost := result.cost }

/-- Sequence two costed computations and add their costs. -/
@[expose] public def bind (result : WithCost α)
    (next : α → WithCost β) : WithCost β :=
  let following := next result.value
  { value := following.value
    cost := result.cost + following.cost }

@[simp] public theorem pure_value (value : α) :
    (pure value).value = value :=
  rfl

@[simp] public theorem pure_cost (value : α) :
    (pure value).cost = 0 :=
  rfl

@[simp] public theorem map_value (f : α → β) (result : WithCost α) :
    (result.map f).value = f result.value :=
  rfl

@[simp] public theorem map_cost (f : α → β) (result : WithCost α) :
    (result.map f).cost = result.cost :=
  rfl

end WithCost

/-- Quotient and remainder produced by one shared long-division pass. -/
public structure DivModResult where
  quotient : SignMagnitude
  remainder : SignMagnitude
  deriving DecidableEq, Repr

/-- Normalized gcd and Bézout coefficients from the costed Euclidean loop. -/
public structure XGCDResult where
  gcd : SignMagnitude
  leftCoeff : SignMagnitude
  rightCoeff : SignMagnitude
  deriving DecidableEq, Repr

end NormalForms.Research.BitCost
