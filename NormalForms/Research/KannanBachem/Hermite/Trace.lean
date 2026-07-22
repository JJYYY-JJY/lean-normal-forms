/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Matrix.Hermite.Defs
public import NormalForms.Matrix.Elementary.Basic

/-!
# Reversible Row Traces for the Kannan--Bachem Research Line

This module separates two notions that must not be conflated in a complexity
proof:

* the semantic fact that a certified invertible row matrix transforms the
  input; and
* a decomposition of that matrix into row primitives whose work can be
  counted.

`certifiedBlock` is therefore an explicit trace class.  It is useful for
binding the frozen core HNF result to the research specification, but a trace
containing such a block is not a primitive trace and cannot discharge a
Kannan--Bachem operation-count theorem.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary

/-- The semantic class of one reversible row step. -/
public inductive RowOperationKind where
  | swap
  | add
  | unitScale
  | bezoutPair
  | certifiedBlock
  deriving DecidableEq, Repr

/-- Exact counts of the row-step classes represented by a trace. -/
public structure OperationCount where
  swaps : Nat := 0
  additions : Nat := 0
  unitScales : Nat := 0
  bezoutPairs : Nat := 0
  certifiedBlocks : Nat := 0
  deriving DecidableEq, Repr

namespace OperationCount

/-- Total number of represented row steps. -/
@[expose] public def total (count : OperationCount) : Nat :=
  count.swaps + count.additions + count.unitScales +
    count.bezoutPairs + count.certifiedBlocks

/-- Componentwise addition of trace counts. -/
@[expose] public def add (left right : OperationCount) : OperationCount :=
  { swaps := left.swaps + right.swaps
    additions := left.additions + right.additions
    unitScales := left.unitScales + right.unitScales
    bezoutPairs := left.bezoutPairs + right.bezoutPairs
    certifiedBlocks := left.certifiedBlocks + right.certifiedBlocks }

/-- The one-step count associated with an operation class. -/
@[expose] public def singleton : RowOperationKind → OperationCount
  | .swap => { swaps := 1 }
  | .add => { additions := 1 }
  | .unitScale => { unitScales := 1 }
  | .bezoutPair => { bezoutPairs := 1 }
  | .certifiedBlock => { certifiedBlocks := 1 }

@[simp] public theorem add_zero (count : OperationCount) :
    count.add {} = count := by
  cases count
  rfl

@[simp] public theorem zero_add (count : OperationCount) :
    ({} : OperationCount).add count = count := by
  cases count
  simp [add]

@[simp] public theorem total_add (left right : OperationCount) :
    (left.add right).total = left.total + right.total := by
  cases left
  cases right
  simp [total, add]
  omega

@[simp] public theorem total_singleton (kind : RowOperationKind) :
    (singleton kind).total = 1 := by
  cases kind <;> rfl

end OperationCount

/--
One full-size reversible row step.  Both inverse equations are stored, so
replay never reconstructs an inverse through a determinant or choice.
-/
public structure ReversibleRowStep (R : Type*) (m : Nat)
    [CommRing R] where
  kind : RowOperationKind
  forward : _root_.Matrix (Fin m) (Fin m) R
  backward : _root_.Matrix (Fin m) (Fin m) R
  backward_forward : backward * forward = 1
  forward_backward : forward * backward = 1

/-- Put a square transform below one fixed leading row. -/
@[expose] public def leadingLiftMatrix {R : Type*} {m : Nat} [CommRing R]
    (U : _root_.Matrix (Fin m) (Fin m) R) :
    _root_.Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  fun i j =>
    Fin.cases
      (Fin.cases (1 : R) (fun _ => 0) j)
      (fun i' => Fin.cases 0 (fun j' => U i' j') j)
      i

@[simp] public theorem leadingLiftMatrix_one {R : Type*} {m : Nat} [CommRing R] :
    leadingLiftMatrix (1 : _root_.Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp [leadingLiftMatrix, _root_.Matrix.one_apply]
      | succ j =>
          have h : (0 : Fin (m + 1)) ≠ j.succ := by
            intro hEq
            exact Fin.succ_ne_zero j hEq.symm
          simp [leadingLiftMatrix, _root_.Matrix.one_apply, h]
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have h : (i.succ : Fin (m + 1)) ≠ 0 := by simp
          simp [leadingLiftMatrix, _root_.Matrix.one_apply, h]
      | succ j => simp [leadingLiftMatrix, _root_.Matrix.one_apply]

@[simp] public theorem leadingLiftMatrix_mul {R : Type*} {m : Nat} [CommRing R]
    (U V : _root_.Matrix (Fin m) (Fin m) R) :
    leadingLiftMatrix U * leadingLiftMatrix V = leadingLiftMatrix (U * V) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases <;>
        simp [leadingLiftMatrix, _root_.Matrix.mul_apply,
          NormalForms.Matrix.Constructive.sum_univ_succ]
  | succ i =>
      cases j using Fin.cases <;>
        simp [leadingLiftMatrix, _root_.Matrix.mul_apply,
          NormalForms.Matrix.Constructive.sum_univ_succ]

namespace ReversibleRowStep

/-- View the stored equations as the core explicit-inverse certificate. -/
@[expose] public def certificate {R : Type*} {m : Nat} [CommRing R]
    (step : ReversibleRowStep R m) :
    MatrixInverseCertificate step.forward :=
  { inverse := step.backward
    left_inv := step.backward_forward
    right_inv := step.forward_backward }

/-- Attach a semantic operation class to an explicit inverse certificate. -/
@[expose] public def ofCertificate {R : Type*} {m : Nat} [CommRing R]
    (kind : RowOperationKind)
    {U : _root_.Matrix (Fin m) (Fin m) R}
    (cert : MatrixInverseCertificate U) : ReversibleRowStep R m :=
  { kind
    forward := U
    backward := cert.inverse
    backward_forward := cert.left_inv
    forward_backward := cert.right_inv }

/-- A reversible row swap. -/
@[expose] public def swap {R : Type*} {m : Nat} [CommRing R]
    (i j : Fin m) : ReversibleRowStep R m := by
  let forward := rowOperationMatrix (.swap i j : RowOperation R (Fin m))
  have selfInverse : forward * forward = 1 := by
    rw [rowOperationMatrix_mul]
    ext r c
    by_cases hij : i = j
    · subst j
      by_cases hri : r = i
      · subst r
        simp [forward, rowOperationMatrix, applyRowOperation]
      · simp [forward, rowOperationMatrix, applyRowOperation, hri]
    · by_cases hri : r = i
      · subst r
        have hji : j ≠ i := fun h => hij h.symm
        simp [forward, rowOperationMatrix, applyRowOperation, hji]
      · by_cases hrj : r = j
        · subst r
          simp [forward, rowOperationMatrix, applyRowOperation, hri]
        · simp [forward, rowOperationMatrix, applyRowOperation, hri, hrj]
  exact
    { kind := .swap
      forward
      backward := forward
      backward_forward := selfInverse
      forward_backward := selfInverse }

/-- Add `coefficient` times `src` to a distinct destination row. -/
@[expose] public def add {R : Type*} {m : Nat} [CommRing R]
    (src dst : Fin m) (coefficient : R) (hne : src ≠ dst) :
    ReversibleRowStep R m := by
  let forward := rowOperationMatrix (.add src dst coefficient : RowOperation R (Fin m))
  let backward := rowOperationMatrix (.add src dst (-coefficient) : RowOperation R (Fin m))
  have backwardForward : backward * forward = 1 := by
    rw [rowOperationMatrix_mul]
    ext i j
    by_cases hi : i = dst
    · subst i
      simp [forward, applyRowOperation, rowOperationMatrix, hne]
    · simp [forward, applyRowOperation, rowOperationMatrix, hi]
  have forwardBackward : forward * backward = 1 := by
    rw [rowOperationMatrix_mul]
    ext i j
    by_cases hi : i = dst
    · subst i
      simp [backward, applyRowOperation, rowOperationMatrix, hne]
    · simp [backward, applyRowOperation, rowOperationMatrix, hi]
  exact
    { kind := .add
      forward
      backward
      backward_forward := backwardForward
      forward_backward := forwardBackward }

/-- Scale one row by a unit. -/
@[expose] public def unitScale {R : Type*} {m : Nat} [CommRing R]
    (i : Fin m) (unit : Rˣ) : ReversibleRowStep R m := by
  let forward := rowOperationMatrix (.smul i (unit : R) : RowOperation R (Fin m))
  let backward := rowOperationMatrix (.smul i (↑unit⁻¹ : R) : RowOperation R (Fin m))
  have backwardForward : backward * forward = 1 := by
    rw [rowOperationMatrix_mul]
    ext r c
    by_cases hr : r = i
    · subst r
      simp [forward, applyRowOperation, rowOperationMatrix, rowScaleMatrix]
    · simp [forward, applyRowOperation, rowOperationMatrix, rowScaleMatrix, hr]
  have forwardBackward : forward * backward = 1 := by
    rw [rowOperationMatrix_mul]
    ext r c
    by_cases hr : r = i
    · subst r
      simp [backward, applyRowOperation, rowOperationMatrix, rowScaleMatrix]
    · simp [backward, applyRowOperation, rowOperationMatrix, rowScaleMatrix, hr]
  exact
    { kind := .unitScale
      forward
      backward
      backward_forward := backwardForward
      forward_backward := forwardBackward }

/--
The two-row extended-gcd primitive in the first two rows, with identity on the
remaining rows.
-/
@[expose] public def bezoutPair {R : Type*}
    [EuclideanDomain R] [NormalizationMonoid R] [ComputableEuclideanOps R]
    (a b : R) : ReversibleRowStep R 2 :=
  { kind := .bezoutPair
    forward := bezoutReductionMatrix a b
    backward := bezoutReductionInverseMatrix a b
    backward_forward := bezoutReductionInverseMatrix_mul a b
    forward_backward := bezoutReductionMatrix_mul_inverse a b }

/--
Treat an arbitrary already-certified transform as one opaque block.  This is
semantically valid but intentionally fails `RowTrace.IsPrimitive`.
-/
@[expose] public def certifiedBlock {R : Type*} {m : Nat} [CommRing R]
    {U : _root_.Matrix (Fin m) (Fin m) R}
    (cert : MatrixInverseCertificate U) : ReversibleRowStep R m :=
  ofCertificate .certifiedBlock cert

/-- Lift one row step below a fixed leading row without changing its class. -/
@[expose] public def leadingLift {R : Type*} {m : Nat} [CommRing R]
    (step : ReversibleRowStep R m) : ReversibleRowStep R (m + 1) :=
  { kind := step.kind
    forward := leadingLiftMatrix step.forward
    backward := leadingLiftMatrix step.backward
    backward_forward := by
      rw [leadingLiftMatrix_mul, step.backward_forward, leadingLiftMatrix_one]
    forward_backward := by
      rw [leadingLiftMatrix_mul, step.forward_backward, leadingLiftMatrix_one] }

@[simp] public theorem leadingLift_kind {R : Type*} {m : Nat} [CommRing R]
    (step : ReversibleRowStep R m) :
    step.leadingLift.kind = step.kind :=
  rfl

end ReversibleRowStep

/-- A replayable list of full-size reversible row steps. -/
public abbrev RowTrace (R : Type*) (m : Nat) [CommRing R] :=
  List (ReversibleRowStep R m)

namespace RowTrace

/-- Apply all row steps in execution order. -/
@[expose] public def replay {R : Type*} {m n : Nat} [CommRing R]
    (A : _root_.Matrix (Fin m) (Fin n) R) (trace : RowTrace R m) :
    _root_.Matrix (Fin m) (Fin n) R :=
  trace.foldl (fun current step => step.forward * current) A

/-- Accumulated left transform in replay order. -/
@[expose] public def accumulator {R : Type*} {m : Nat} [CommRing R] :
    RowTrace R m → _root_.Matrix (Fin m) (Fin m) R
  | [] => 1
  | step :: tail => accumulator tail * step.forward

/-- Constructively accumulated inverse of `accumulator`. -/
@[expose] public def inverseAccumulator {R : Type*} {m : Nat} [CommRing R] :
    RowTrace R m → _root_.Matrix (Fin m) (Fin m) R
  | [] => 1
  | step :: tail => step.backward * inverseAccumulator tail

/-- Explicit inverse certificate accumulated directly from the trace. -/
@[expose] public def accumulatorCertificate {R : Type*} {m : Nat} [CommRing R] :
    (trace : RowTrace R m) → MatrixInverseCertificate (accumulator trace)
  | [] => MatrixInverseCertificate.one
  | step :: tail => (accumulatorCertificate tail).mul step.certificate

@[simp] public theorem accumulatorCertificate_inverse {R : Type*} {m : Nat}
    [CommRing R] (trace : RowTrace R m) :
    (accumulatorCertificate trace).inverse = inverseAccumulator trace := by
  induction trace with
  | nil => rfl
  | cons step tail ih =>
      simp [accumulatorCertificate, inverseAccumulator,
        MatrixInverseCertificate.mul, ReversibleRowStep.certificate, ih]

public theorem inverse_mul_accumulator {R : Type*} {m : Nat} [CommRing R]
    (trace : RowTrace R m) :
    inverseAccumulator trace * accumulator trace = 1 := by
  simpa using (accumulatorCertificate trace).left_inv

public theorem accumulator_mul_inverse {R : Type*} {m : Nat} [CommRing R]
    (trace : RowTrace R m) :
    accumulator trace * inverseAccumulator trace = 1 := by
  simpa using (accumulatorCertificate trace).right_inv

public theorem replay_eq_accumulator_mul {R : Type*} {m n : Nat} [CommRing R]
    (A : _root_.Matrix (Fin m) (Fin n) R) (trace : RowTrace R m) :
    replay A trace = accumulator trace * A := by
  induction trace generalizing A with
  | nil => simp [replay, accumulator]
  | cons step tail ih =>
      change replay (step.forward * A) tail =
        accumulator tail * step.forward * A
      rw [ih]
      simp only [Matrix.mul_assoc]

public theorem replay_append {R : Type*} {m n : Nat} [CommRing R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (first second : RowTrace R m) :
    replay A (first ++ second) = replay (replay A first) second := by
  induction first generalizing A with
  | nil => rfl
  | cons step tail ih =>
      simp only [List.cons_append]
      change replay (step.forward * A) (tail ++ second) =
        replay (replay (step.forward * A) tail) second
      exact ih _

public theorem accumulator_append {R : Type*} {m : Nat} [CommRing R]
    (first second : RowTrace R m) :
    accumulator (first ++ second) = accumulator second * accumulator first := by
  induction first with
  | nil => simp [accumulator]
  | cons step tail ih =>
      simp [accumulator, ih, Matrix.mul_assoc]

public theorem inverseAccumulator_append {R : Type*} {m : Nat} [CommRing R]
    (first second : RowTrace R m) :
    inverseAccumulator (first ++ second) =
      inverseAccumulator first * inverseAccumulator second := by
  induction first with
  | nil => simp [inverseAccumulator]
  | cons step tail ih =>
      simp [inverseAccumulator, ih, Matrix.mul_assoc]

/-- Count every represented row-step class exactly once. -/
@[expose] public def operationCount {R : Type*} {m : Nat} [CommRing R] :
    RowTrace R m → OperationCount
  | [] => {}
  | step :: tail => (OperationCount.singleton step.kind).add (operationCount tail)

/-- A trace is primitive precisely when it has no opaque certified blocks. -/
@[expose] public def IsPrimitive {R : Type*} {m : Nat} [CommRing R]
    (trace : RowTrace R m) : Prop :=
  (operationCount trace).certifiedBlocks = 0

instance {R : Type*} {m : Nat} [CommRing R] (trace : RowTrace R m) :
    Decidable trace.IsPrimitive :=
  inferInstanceAs (Decidable ((operationCount trace).certifiedBlocks = 0))

@[simp] public theorem operationCount_append {R : Type*} {m : Nat} [CommRing R]
    (first second : RowTrace R m) :
    operationCount (first ++ second) =
      (operationCount first).add (operationCount second) := by
  induction first with
  | nil => simp [operationCount]
  | cons step tail ih =>
      simp only [List.cons_append, operationCount, ih]
      cases OperationCount.singleton step.kind
      cases operationCount tail
      cases operationCount second
      simp [OperationCount.add, Nat.add_assoc]

@[simp] public theorem operationCount_total_eq_length {R : Type*} {m : Nat}
    [CommRing R] (trace : RowTrace R m) :
    (operationCount trace).total = trace.length := by
  induction trace with
  | nil => rfl
  | cons step tail ih =>
      simp [operationCount, ih]
      omega

public theorem operationCount_components_le_length {R : Type*} {m : Nat}
    [CommRing R] (trace : RowTrace R m) :
    (operationCount trace).swaps ≤ trace.length ∧
      (operationCount trace).additions ≤ trace.length ∧
      (operationCount trace).unitScales ≤ trace.length ∧
      (operationCount trace).bezoutPairs ≤ trace.length ∧
      (operationCount trace).certifiedBlocks ≤ trace.length := by
  have htotal := operationCount_total_eq_length trace
  unfold OperationCount.total at htotal
  omega

@[simp] public theorem isPrimitive_append {R : Type*} {m : Nat} [CommRing R]
    (first second : RowTrace R m) :
    IsPrimitive (first ++ second) ↔ IsPrimitive first ∧ IsPrimitive second := by
  simp [IsPrimitive, OperationCount.add]

/-- Lift an entire trace below one fixed leading row. -/
@[expose] public def leadingLift {R : Type*} {m : Nat} [CommRing R]
    (trace : RowTrace R m) : RowTrace R (m + 1) :=
  trace.map ReversibleRowStep.leadingLift

@[simp] public theorem operationCount_leadingLift {R : Type*} {m : Nat} [CommRing R]
    (trace : RowTrace R m) :
    operationCount trace.leadingLift = operationCount trace := by
  induction trace with
  | nil => rfl
  | cons step tail ih =>
      change (OperationCount.singleton step.kind).add
          (operationCount (leadingLift tail)) =
        (OperationCount.singleton step.kind).add (operationCount tail)
      rw [ih]

@[simp] public theorem accumulator_leadingLift {R : Type*} {m : Nat} [CommRing R]
    (trace : RowTrace R m) :
    accumulator trace.leadingLift = leadingLiftMatrix (accumulator trace) := by
  induction trace with
  | nil => simp [leadingLift, accumulator]
  | cons step tail ih =>
      change accumulator (leadingLift tail) * leadingLiftMatrix step.forward =
        leadingLiftMatrix (accumulator tail * step.forward)
      rw [ih, leadingLiftMatrix_mul]

@[simp] public theorem inverseAccumulator_leadingLift {R : Type*} {m : Nat}
    [CommRing R] (trace : RowTrace R m) :
    inverseAccumulator trace.leadingLift =
      leadingLiftMatrix (inverseAccumulator trace) := by
  induction trace with
  | nil => simp [leadingLift, inverseAccumulator]
  | cons step tail ih =>
      change leadingLiftMatrix step.backward * inverseAccumulator (leadingLift tail) =
        leadingLiftMatrix (step.backward * inverseAccumulator tail)
      rw [ih, leadingLiftMatrix_mul]

end RowTrace

end NormalForms.Research.KannanBachem.Hermite
