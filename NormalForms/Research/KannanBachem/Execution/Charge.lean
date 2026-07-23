/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.BitCost.Primitives

/-!
# Leaf Arithmetic Charges

The flat execution trace contains only modeled scalar primitives.  Composite
algorithm steps contribute by concatenating their children's charge lists.
Each leaf stores the primitive run that supplied both its transition value and
its folded cost.
-/

public section

namespace NormalForms.Research.KannanBachem

open NormalForms.Research.BitCost

/-- The five closed roles of long division outside opaque bounded XGCD. -/
public inductive StandaloneDivModRole where
  | hnfReduceAbove
  | bezoutLeftExact
  | bezoutRightExact
  | smithSearch
  | smithClear
  deriving DecidableEq, Repr

/-- Static call-site class used to validate role ownership. -/
public inductive ArithmeticChargeSite where
  | scalar
  | hnfReduceAbove
  | bezoutBlock
  | smithSearch
  | smithClear
  deriving DecidableEq, Repr

/-- Runtime indices plus a proof that every recorded index fits its matrix. -/
public structure ArithmeticChargeLocation where
  site : ArithmeticChargeSite
  dimension : Nat
  indices : List Nat
  indices_valid : ∀ index ∈ indices, index < dimension

namespace ArithmeticChargeLocation

/-- A non-matrix scalar location carries no indices. -/
@[expose] public def scalar : ArithmeticChargeLocation :=
  { site := .scalar, dimension := 0, indices := []
    indices_valid := by simp }

/-- A checked matrix location. -/
@[expose] public def ofIndices
    (site : ArithmeticChargeSite) (dimension : Nat) (indices : List Nat)
    (valid : ∀ index ∈ indices, index < dimension) :
    ArithmeticChargeLocation :=
  { site, dimension, indices, indices_valid := valid }

end ArithmeticChargeLocation

namespace Internal

@[expose] public def roleMatchesSite :
    StandaloneDivModRole → ArithmeticChargeSite → Prop
  | .hnfReduceAbove, .hnfReduceAbove => True
  | .bezoutLeftExact, .bezoutBlock => True
  | .bezoutRightExact, .bezoutBlock => True
  | .smithSearch, .smithSearch => True
  | .smithClear, .smithClear => True
  | _, _ => False

public structure ZeroTestCharge where
  location : ArithmeticChargeLocation
  operand : SignMagnitude
  run : WithCost Bool
  run_eq : run = isZeroWithCost operand

public structure MagnitudeCompareCharge where
  location : ArithmeticChargeLocation
  left : SignMagnitude
  right : SignMagnitude
  run : WithCost Ordering
  run_eq : run = magnitudeCompareWithCost left right

public structure AdditionCharge where
  location : ArithmeticChargeLocation
  left : SignMagnitude
  right : SignMagnitude
  run : WithCost SignMagnitude
  run_eq : run = addWithCost left right

public structure MultiplicationCharge where
  location : ArithmeticChargeLocation
  left : SignMagnitude
  right : SignMagnitude
  run : WithCost SignMagnitude
  run_eq : run = mulWithCost left right

public structure DivModCharge where
  location : ArithmeticChargeLocation
  role : StandaloneDivModRole
  numerator : SignMagnitude
  divisor : SignMagnitude
  run : WithCost DivModResult
  run_eq : run = divModWithCost numerator divisor
  role_valid : roleMatchesSite role location.site

public structure BoundedBezoutBlockCharge where
  location : ArithmeticChargeLocation
  left : SignMagnitude
  right : SignMagnitude
  run : WithCost BoundedBezoutBlock
  run_eq : run = boundedBezoutBlockWithCost left right

public structure NormalizationCharge where
  location : ArithmeticChargeLocation
  operand : SignMagnitude
  run : WithCost Intˣ
  run_eq : run = normalizationUnitWithCost operand

public inductive ArithmeticChargeData where
  | zeroTest (charge : ZeroTestCharge)
  | magnitudeCompare (charge : MagnitudeCompareCharge)
  | addition (charge : AdditionCharge)
  | multiplication (charge : MultiplicationCharge)
  | divMod (charge : DivModCharge)
  | boundedBezoutBlock (charge : BoundedBezoutBlockCharge)
  | normalization (charge : NormalizationCharge)

end Internal

/--
An unforgeable arithmetic leaf.  Its constructor and representation are
private; public smart constructors require a named primitive run and its
definitional alignment proof.
-/
public structure KannanBachemArithmeticCharge where
  mk ::
  data : Internal.ArithmeticChargeData

namespace KannanBachemArithmeticCharge

/-- Record one zero-test run. -/
@[expose] public def zeroTestOfRun
    (location : ArithmeticChargeLocation) (operand : SignMagnitude)
    (run : WithCost Bool) (run_eq : run = isZeroWithCost operand) :
    KannanBachemArithmeticCharge :=
  ⟨.zeroTest ⟨location, operand, run, run_eq⟩⟩

/-- Record one structural magnitude comparison run. -/
@[expose] public def magnitudeCompareOfRun
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost Ordering)
    (run_eq : run = magnitudeCompareWithCost left right) :
    KannanBachemArithmeticCharge :=
  ⟨.magnitudeCompare ⟨location, left, right, run, run_eq⟩⟩

/-- Record one sign-magnitude addition run. -/
@[expose] public def additionOfRun
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost SignMagnitude) (run_eq : run = addWithCost left right) :
    KannanBachemArithmeticCharge :=
  ⟨.addition ⟨location, left, right, run, run_eq⟩⟩

/-- Record one sign-magnitude multiplication run. -/
@[expose] public def multiplicationOfRun
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost SignMagnitude) (run_eq : run = mulWithCost left right) :
    KannanBachemArithmeticCharge :=
  ⟨.multiplication ⟨location, left, right, run, run_eq⟩⟩

/-- Record one standalone shared quotient/remainder run. -/
@[expose] public def divModOfRun
    (location : ArithmeticChargeLocation) (role : StandaloneDivModRole)
    (numerator divisor : SignMagnitude) (run : WithCost DivModResult)
    (run_eq : run = divModWithCost numerator divisor)
    (role_valid : Internal.roleMatchesSite role location.site) :
    KannanBachemArithmeticCharge :=
  ⟨.divMod
    { location, role, numerator, divisor, run
      run_eq := by simpa using run_eq
      role_valid }⟩

/-- Record one opaque bounded-Bézout block run. -/
@[expose] public def boundedBezoutBlockOfRun
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost BoundedBezoutBlock)
    (run_eq : run = boundedBezoutBlockWithCost left right) :
    KannanBachemArithmeticCharge :=
  ⟨.boundedBezoutBlock ⟨location, left, right, run, run_eq⟩⟩

/-- Record one canonical sign-normalization run. -/
@[expose] public def normalizationOfRun
    (location : ArithmeticChargeLocation) (operand : SignMagnitude)
    (run : WithCost Intˣ)
    (run_eq : run = normalizationUnitWithCost operand) :
    KannanBachemArithmeticCharge :=
  ⟨.normalization ⟨location, operand, run, run_eq⟩⟩

/-- The exact cost stored by the named primitive run. -/
@[expose] public def bitCost : KannanBachemArithmeticCharge → Nat
  | ⟨.zeroTest charge⟩ => charge.run.cost
  | ⟨.magnitudeCompare charge⟩ => charge.run.cost
  | ⟨.addition charge⟩ => charge.run.cost
  | ⟨.multiplication charge⟩ => charge.run.cost
  | ⟨.divMod charge⟩ => charge.run.cost
  | ⟨.boundedBezoutBlock charge⟩ => charge.run.cost
  | ⟨.normalization charge⟩ => charge.run.cost

@[simp] public theorem bitCost_zeroTestOfRun
    (location : ArithmeticChargeLocation) (operand : SignMagnitude)
    (run : WithCost Bool) (run_eq : run = isZeroWithCost operand) :
    (zeroTestOfRun location operand run run_eq).bitCost = run.cost :=
  rfl

@[simp] public theorem bitCost_additionOfRun
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost SignMagnitude) (run_eq : run = addWithCost left right) :
    (additionOfRun location left right run run_eq).bitCost = run.cost :=
  rfl

@[simp] public theorem bitCost_multiplicationOfRun
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost SignMagnitude) (run_eq : run = mulWithCost left right) :
    (multiplicationOfRun location left right run run_eq).bitCost = run.cost :=
  rfl

@[simp] public theorem bitCost_divModOfRun
    (location : ArithmeticChargeLocation) (role : StandaloneDivModRole)
    (numerator divisor : SignMagnitude) (run : WithCost DivModResult)
    (run_eq : run = divModWithCost numerator divisor)
    (role_valid : Internal.roleMatchesSite role location.site) :
    (divModOfRun location role numerator divisor run run_eq role_valid).bitCost =
      run.cost :=
  rfl

@[simp] public theorem bitCost_boundedBezoutBlockOfRun
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost BoundedBezoutBlock)
    (run_eq : run = boundedBezoutBlockWithCost left right) :
    (boundedBezoutBlockOfRun location left right run run_eq).bitCost =
      run.cost :=
  rfl

/-- The matrix location stored by a leaf. -/
@[expose] public def location :
    KannanBachemArithmeticCharge → ArithmeticChargeLocation
  | ⟨.zeroTest charge⟩ => charge.location
  | ⟨.magnitudeCompare charge⟩ => charge.location
  | ⟨.addition charge⟩ => charge.location
  | ⟨.multiplication charge⟩ => charge.location
  | ⟨.divMod charge⟩ => charge.location
  | ⟨.boundedBezoutBlock charge⟩ => charge.location
  | ⟨.normalization charge⟩ => charge.location

/-- Standalone division roles owned by one leaf. -/
@[expose] public def standaloneDivModRoles :
    KannanBachemArithmeticCharge → List StandaloneDivModRole
  | ⟨.divMod charge⟩ => [charge.role]
  | ⟨.boundedBezoutBlock charge⟩ =>
      if charge.run.value.gcd = 0 then
        []
      else
        [.bezoutLeftExact, .bezoutRightExact]
  | _ => []

/--
Public integrity predicate.  It checks primitive identity, role ownership, and
the index bounds retained by the location.  The XGCD case is a single opaque
leaf and therefore has no arithmetic descendants.
-/
@[expose] public def WellFormed : KannanBachemArithmeticCharge → Prop
  | ⟨.zeroTest charge⟩ =>
      charge.run = isZeroWithCost charge.operand ∧
        ∀ index ∈ charge.location.indices,
          index < charge.location.dimension
  | ⟨.magnitudeCompare charge⟩ =>
      charge.run = magnitudeCompareWithCost charge.left charge.right ∧
        ∀ index ∈ charge.location.indices,
          index < charge.location.dimension
  | ⟨.addition charge⟩ =>
      charge.run = addWithCost charge.left charge.right ∧
        ∀ index ∈ charge.location.indices,
          index < charge.location.dimension
  | ⟨.multiplication charge⟩ =>
      charge.run = mulWithCost charge.left charge.right ∧
        ∀ index ∈ charge.location.indices,
          index < charge.location.dimension
  | ⟨.divMod charge⟩ =>
      charge.run = divModWithCost charge.numerator charge.divisor ∧
        Internal.roleMatchesSite charge.role charge.location.site ∧
        ∀ index ∈ charge.location.indices,
          index < charge.location.dimension
  | ⟨.boundedBezoutBlock charge⟩ =>
      charge.run = boundedBezoutBlockWithCost charge.left charge.right ∧
        ∀ index ∈ charge.location.indices,
          index < charge.location.dimension
  | ⟨.normalization charge⟩ =>
      charge.run = normalizationUnitWithCost charge.operand ∧
        ∀ index ∈ charge.location.indices,
          index < charge.location.dimension

public theorem zeroTestOfRun_wellFormed
    (location : ArithmeticChargeLocation) (operand : SignMagnitude)
    (run : WithCost Bool) (run_eq : run = isZeroWithCost operand) :
    (zeroTestOfRun location operand run run_eq).WellFormed :=
  ⟨run_eq, location.indices_valid⟩

public theorem magnitudeCompareOfRun_wellFormed
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost Ordering)
    (run_eq : run = magnitudeCompareWithCost left right) :
    (magnitudeCompareOfRun location left right run run_eq).WellFormed :=
  ⟨run_eq, location.indices_valid⟩

public theorem additionOfRun_wellFormed
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost SignMagnitude) (run_eq : run = addWithCost left right) :
    (additionOfRun location left right run run_eq).WellFormed :=
  ⟨run_eq, location.indices_valid⟩

public theorem multiplicationOfRun_wellFormed
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost SignMagnitude) (run_eq : run = mulWithCost left right) :
    (multiplicationOfRun location left right run run_eq).WellFormed :=
  ⟨run_eq, location.indices_valid⟩

public theorem divModOfRun_wellFormed
    (location : ArithmeticChargeLocation) (role : StandaloneDivModRole)
    (numerator divisor : SignMagnitude) (run : WithCost DivModResult)
    (run_eq : run = divModWithCost numerator divisor)
    (role_valid : Internal.roleMatchesSite role location.site) :
    (divModOfRun location role numerator divisor run run_eq role_valid).WellFormed :=
  ⟨run_eq, role_valid, location.indices_valid⟩

public theorem boundedBezoutBlockOfRun_wellFormed
    (location : ArithmeticChargeLocation) (left right : SignMagnitude)
    (run : WithCost BoundedBezoutBlock)
    (run_eq : run = boundedBezoutBlockWithCost left right) :
    (boundedBezoutBlockOfRun location left right run run_eq).WellFormed :=
  ⟨run_eq, location.indices_valid⟩

public theorem normalizationOfRun_wellFormed
    (location : ArithmeticChargeLocation) (operand : SignMagnitude)
    (run : WithCost Intˣ)
    (run_eq : run = normalizationUnitWithCost operand) :
    (normalizationOfRun location operand run run_eq).WellFormed :=
  ⟨run_eq, location.indices_valid⟩

end KannanBachemArithmeticCharge

/-- Unified macro-operation count derived from the same flat charge list. -/
@[ext] public structure ArithmeticOperationCount where
  additions : Nat
  multiplications : Nat
  xgcdCalls : Nat
  normalizations : Nat
  standaloneDivModCalls : Nat
  deriving DecidableEq, Repr

namespace ArithmeticOperationCount

@[expose] public def add
    (left right : ArithmeticOperationCount) : ArithmeticOperationCount :=
  { additions := left.additions + right.additions
    multiplications := left.multiplications + right.multiplications
    xgcdCalls := left.xgcdCalls + right.xgcdCalls
    normalizations := left.normalizations + right.normalizations
    standaloneDivModCalls :=
      left.standaloneDivModCalls + right.standaloneDivModCalls }

public instance : Add ArithmeticOperationCount :=
  ⟨ArithmeticOperationCount.add⟩

@[expose] public def zero : ArithmeticOperationCount :=
  { additions := 0
    multiplications := 0
    xgcdCalls := 0
    normalizations := 0
    standaloneDivModCalls := 0 }

public instance : OfNat ArithmeticOperationCount 0 where
  ofNat :=
    zero

@[simp] public theorem zero_additions :
    (0 : ArithmeticOperationCount).additions = 0 := by
  change zero.additions = 0
  rfl

@[simp] public theorem zero_multiplications :
    (0 : ArithmeticOperationCount).multiplications = 0 := by
  change zero.multiplications = 0
  rfl

@[simp] public theorem zero_xgcdCalls :
    (0 : ArithmeticOperationCount).xgcdCalls = 0 := by
  change zero.xgcdCalls = 0
  rfl

@[simp] public theorem zero_normalizations :
    (0 : ArithmeticOperationCount).normalizations = 0 := by
  change zero.normalizations = 0
  rfl

@[simp] public theorem zero_standaloneDivModCalls :
    (0 : ArithmeticOperationCount).standaloneDivModCalls = 0 := by
  change zero.standaloneDivModCalls = 0
  rfl

@[simp] public theorem add_additions
    (left right : ArithmeticOperationCount) :
    (left + right).additions = left.additions + right.additions :=
  rfl

@[simp] public theorem add_multiplications
    (left right : ArithmeticOperationCount) :
    (left + right).multiplications =
      left.multiplications + right.multiplications :=
  rfl

@[simp] public theorem add_xgcdCalls
    (left right : ArithmeticOperationCount) :
    (left + right).xgcdCalls = left.xgcdCalls + right.xgcdCalls :=
  rfl

@[simp] public theorem add_normalizations
    (left right : ArithmeticOperationCount) :
    (left + right).normalizations =
      left.normalizations + right.normalizations :=
  rfl

@[simp] public theorem add_standaloneDivModCalls
    (left right : ArithmeticOperationCount) :
    (left + right).standaloneDivModCalls =
      left.standaloneDivModCalls + right.standaloneDivModCalls :=
  rfl

@[simp] public theorem zero_add (count : ArithmeticOperationCount) :
    0 + count = count := by
  ext <;> simp

@[simp] public theorem add_zero (count : ArithmeticOperationCount) :
    count + 0 = count := by
  ext <;> simp

public theorem add_assoc
    (first second third : ArithmeticOperationCount) :
    first + second + third = first + (second + third) := by
  cases first
  cases second
  cases third
  ext <;> simp [Nat.add_assoc]

/-- Total counted macro operations. -/
@[expose] public def total (count : ArithmeticOperationCount) : Nat :=
  count.additions + count.multiplications + count.xgcdCalls +
    count.normalizations + count.standaloneDivModCalls

end ArithmeticOperationCount

namespace KannanBachemArithmeticCharge

/-- One leaf's contribution to the unified macro count. -/
@[expose] public def operationDelta :
    KannanBachemArithmeticCharge → ArithmeticOperationCount
  | ⟨.addition _⟩ =>
      { additions := 1, multiplications := 0, xgcdCalls := 0,
        normalizations := 0, standaloneDivModCalls := 0 }
  | ⟨.multiplication _⟩ =>
      { additions := 0, multiplications := 1, xgcdCalls := 0,
        normalizations := 0, standaloneDivModCalls := 0 }
  | ⟨.boundedBezoutBlock charge⟩ =>
      { additions := 0, multiplications := 0, xgcdCalls := 1,
        normalizations := 0
        standaloneDivModCalls :=
          if charge.run.value.gcd = 0 then 0 else 2 }
  | ⟨.normalization _⟩ =>
      { additions := 0, multiplications := 0, xgcdCalls := 0,
        normalizations := 1, standaloneDivModCalls := 0 }
  | ⟨.divMod _⟩ =>
      { additions := 0, multiplications := 0, xgcdCalls := 0,
        normalizations := 0, standaloneDivModCalls := 1 }
  | _ => 0

end KannanBachemArithmeticCharge

/-- Sum the exact primitive bit costs in a flat arithmetic trace. -/
@[expose] public def traceBitCost
    (charges : List KannanBachemArithmeticCharge) : Nat :=
  (charges.map KannanBachemArithmeticCharge.bitCost).sum

@[simp] public theorem traceBitCost_singleton_zeroTestOfRun
    (location : ArithmeticChargeLocation) (operand : SignMagnitude)
    (run : WithCost Bool) (run_eq : run = isZeroWithCost operand) :
    traceBitCost
        [KannanBachemArithmeticCharge.zeroTestOfRun
          location operand run run_eq] =
      run.cost := by
  simp [traceBitCost]

/-- Fold the unified macro count from the same flat arithmetic trace. -/
@[expose] public def traceOperationCount
    (charges : List KannanBachemArithmeticCharge) :
    ArithmeticOperationCount :=
  charges.foldl
    (fun count charge ↦ count + charge.operationDelta) 0

public theorem traceBitCost_append
    (first second : List KannanBachemArithmeticCharge) :
    traceBitCost (first ++ second) =
      traceBitCost first + traceBitCost second := by
  simp [traceBitCost]

private theorem traceOperationCount_accumulator
    (charges : List KannanBachemArithmeticCharge)
    (initial : ArithmeticOperationCount) :
    charges.foldl (fun count charge ↦ count + charge.operationDelta) initial =
      initial + traceOperationCount charges := by
  induction charges generalizing initial with
  | nil => simp [traceOperationCount]
  | cons charge tail ih =>
      rw [List.foldl_cons, ih]
      change initial + charge.operationDelta + traceOperationCount tail =
        initial +
          tail.foldl
            (fun count charge ↦ count + charge.operationDelta)
            (0 + charge.operationDelta)
      rw [ih]
      simp only [ArithmeticOperationCount.zero_add,
        ArithmeticOperationCount.add_assoc]

public theorem traceOperationCount_append
    (first second : List KannanBachemArithmeticCharge) :
    traceOperationCount (first ++ second) =
      traceOperationCount first + traceOperationCount second := by
  rw [traceOperationCount, List.foldl_append,
    traceOperationCount_accumulator]
  rfl

/-- Standalone division events, preserving their execution order and roles. -/
@[expose] public def traceStandaloneDivModEvents
    (charges : List KannanBachemArithmeticCharge) :
    List StandaloneDivModRole :=
  charges.flatMap KannanBachemArithmeticCharge.standaloneDivModRoles

public theorem trace_standaloneDivModCalls_eq_events
    (charges : List KannanBachemArithmeticCharge) :
    (traceOperationCount charges).standaloneDivModCalls =
      (traceStandaloneDivModEvents charges).length := by
  induction charges with
  | nil => rfl
  | cons charge tail ih =>
      rw [show charge :: tail = [charge] ++ tail by rfl,
        traceOperationCount_append]
      simp only [ArithmeticOperationCount.add_standaloneDivModCalls, ih]
      cases charge with
      | mk data =>
          cases data <;> simp [traceOperationCount,
            traceStandaloneDivModEvents,
            KannanBachemArithmeticCharge.operationDelta,
            KannanBachemArithmeticCharge.standaloneDivModRoles]
          all_goals try omega
          split <;> simp_all

/-- Number of standalone divisions carrying one designated closed role. -/
@[expose] public def traceRoleEventCount
    (role : StandaloneDivModRole)
    (charges : List KannanBachemArithmeticCharge) : Nat :=
  (traceStandaloneDivModEvents charges).count role

public theorem trace_hnfReduceAboveDivMods
    (charges : List KannanBachemArithmeticCharge) :
    traceRoleEventCount .hnfReduceAbove charges =
      (traceStandaloneDivModEvents charges).count .hnfReduceAbove :=
  rfl

public theorem trace_bezoutExactDivMods
    (charges : List KannanBachemArithmeticCharge) :
    traceRoleEventCount .bezoutLeftExact charges +
        traceRoleEventCount .bezoutRightExact charges =
      (traceStandaloneDivModEvents charges).count .bezoutLeftExact +
        (traceStandaloneDivModEvents charges).count .bezoutRightExact :=
  rfl

public theorem trace_smithSearchDivMods
    (charges : List KannanBachemArithmeticCharge) :
    traceRoleEventCount .smithSearch charges =
      (traceStandaloneDivModEvents charges).count .smithSearch :=
  rfl

public theorem trace_smithClearDivMods
    (charges : List KannanBachemArithmeticCharge) :
    traceRoleEventCount .smithClear charges =
      (traceStandaloneDivModEvents charges).count .smithClear :=
  rfl

/-- Public trace integrity is pointwise leaf integrity. -/
@[expose] public def ArithmeticChargeListWellFormed
    (charges : List KannanBachemArithmeticCharge) : Prop :=
  charges.Forall KannanBachemArithmeticCharge.WellFormed

public theorem ArithmeticChargeListWellFormed.append
    {first second : List KannanBachemArithmeticCharge}
    (firstWellFormed : ArithmeticChargeListWellFormed first)
    (secondWellFormed : ArithmeticChargeListWellFormed second) :
    ArithmeticChargeListWellFormed (first ++ second) := by
  exact List.forall_append.mpr ⟨firstWellFormed, secondWellFormed⟩

end NormalForms.Research.KannanBachem
