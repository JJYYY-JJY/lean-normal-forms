/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.Semantics
import all NormalForms.Matrix.Hermite.Transform
import all NormalForms.Matrix.Hermite.Bezout
import all NormalForms.Matrix.Hermite.Algorithm
import all NormalForms.Matrix.Hermite.Uniqueness

/-!
# Primitive Trace Instrumentation for the Integer HNF Kernel

This module mirrors the semantic HNF state transitions while retaining every
reversible row primitive.  The recursive state remains private; the public
surface exports only the existing strong `HNFResultFin` and its trace witness.

The operation trace establishes semantic stage infrastructure.  Polynomial
operation, coefficient-growth, and bit-complexity bounds are separate later
theorems and are not claimed here.
-/

set_option linter.privateModule false

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite

namespace Traced

/-- Private row-transform state paired with a primitive reversible trace. -/
structure LeftTransform {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) where
  base : NormalForms.Matrix.Hermite.LeftTransform A
  steps : RowTrace Int m
  accumulator_eq : steps.accumulator = base.U
  inverseAccumulator_eq : steps.inverseAccumulator = base.U_cert.inverse
  primitive : steps.IsPrimitive

def LeftTransform.refl {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : LeftTransform A :=
  { base := NormalForms.Matrix.Hermite.LeftTransform.refl A
    steps := []
    accumulator_eq := by
      simp [RowTrace.accumulator, NormalForms.Matrix.Hermite.LeftTransform.refl]
    inverseAccumulator_eq := by
      simp [RowTrace.inverseAccumulator,
        NormalForms.Matrix.Hermite.LeftTransform.refl,
        MatrixInverseCertificate.one]
    primitive := by simp [RowTrace.IsPrimitive, RowTrace.operationCount] }

def LeftTransform.trans {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (first : LeftTransform A) (second : LeftTransform first.base.B) :
    LeftTransform A :=
  { base := first.base.trans second.base
    steps := first.steps ++ second.steps
    accumulator_eq := by
      rw [RowTrace.accumulator_append, second.accumulator_eq, first.accumulator_eq]
      rfl
    inverseAccumulator_eq := by
      rw [RowTrace.inverseAccumulator_append, first.inverseAccumulator_eq,
        second.inverseAccumulator_eq]
      rfl
    primitive := (RowTrace.isPrimitive_append first.steps second.steps).2
      ⟨first.primitive, second.primitive⟩ }

private def LeftTransform.ofPrimitive {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (base : NormalForms.Matrix.Hermite.LeftTransform A)
    (kind : RowOperationKind) (hkind : kind ≠ .certifiedBlock) :
    LeftTransform A :=
  { base
    steps := [ReversibleRowStep.ofCertificate kind base.U_cert]
    accumulator_eq := by
      simp [RowTrace.accumulator, ReversibleRowStep.ofCertificate]
    inverseAccumulator_eq := by
      simp [RowTrace.inverseAccumulator, ReversibleRowStep.ofCertificate]
    primitive := by
      cases kind <;>
        simp_all [RowTrace.IsPrimitive, RowTrace.operationCount,
          OperationCount.singleton, OperationCount.add,
          ReversibleRowStep.ofCertificate] }

def LeftTransform.swap {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (i j : Fin m) : LeftTransform A :=
  LeftTransform.ofPrimitive
    (NormalForms.Matrix.Hermite.LeftTransform.swap A i j) .swap (by decide)

def LeftTransform.add {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (src dst : Fin m) (coefficient : Int) (hne : src ≠ dst) : LeftTransform A :=
  LeftTransform.ofPrimitive
    (NormalForms.Matrix.Hermite.LeftTransform.add A src dst coefficient hne)
    .add (by decide)

def LeftTransform.unitScale {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (i : Fin m) (unit : Intˣ) :
    LeftTransform A :=
  LeftTransform.ofPrimitive
    (NormalForms.Matrix.Hermite.LeftTransform.unitSmul A i unit)
    .unitScale (by decide)

def LeftTransform.topBezout {m n : Nat}
    (A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int) : LeftTransform A :=
  LeftTransform.ofPrimitive
    (NormalForms.Matrix.Hermite.LeftTransform.topBezout A)
    .bezoutPair (by decide)

/--
Reuse a traced row transform on another matrix.  The source matrix is an
explicit argument solely to retain its dependent type.
-/
def LeftTransform.actOnFrom {m n k : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    {sourceMatrix : _root_.Matrix (Fin m) (Fin k) Int}
    (source : LeftTransform sourceMatrix) : LeftTransform A :=
  { base :=
      { U := source.base.U
        U_cert := source.base.U_cert
        B := source.base.U * A
        left_mul := rfl }
    steps := source.steps
    accumulator_eq := source.accumulator_eq
    inverseAccumulator_eq := source.inverseAccumulator_eq
    primitive := source.primitive }

def LeftTransform.leadingLift {m n k : Nat}
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) Int)
    {sourceMatrix : _root_.Matrix (Fin m) (Fin k) Int}
    (source : LeftTransform sourceMatrix) : LeftTransform A :=
  { base := NormalForms.Matrix.Hermite.LeftTransform.diagLift
      A source.base.U source.base.U_cert
    steps := source.steps.leadingLift
    accumulator_eq := by
      rw [RowTrace.accumulator_leadingLift, source.accumulator_eq]
      rfl
    inverseAccumulator_eq := by
      rw [RowTrace.inverseAccumulator_leadingLift, source.inverseAccumulator_eq]
      rfl
    primitive := by
      simpa [RowTrace.IsPrimitive] using source.primitive }

private def firstNonzeroExec? : {m : Nat} → (Fin m → Int) → Option (Fin m)
  | 0, _ => none
  | _ + 1, entries =>
      if ComputableEuclideanOps.isZeroB (entries 0) = true then
        Option.map Fin.succ (firstNonzeroExec? fun i => entries i.succ)
      else
        some 0

@[simp] theorem firstNonzeroExec?_eq_firstNonzero? :
    {m : Nat} → (entries : Fin m → Int) →
      firstNonzeroExec? entries = firstNonzero? entries
  | 0, _ => rfl
  | _ + 1, entries => by
      by_cases hzero : entries 0 = 0
      · simp [firstNonzeroExec?, firstNonzero?, hzero,
          firstNonzeroExec?_eq_firstNonzero?]
      · have hbool : ComputableEuclideanOps.isZeroB (entries 0) ≠ true :=
          fun h => hzero ((ComputableEuclideanOps.isZeroB_eq_true_iff _).1 h)
        simp [firstNonzeroExec?, firstNonzero?, hzero, hbool]

def clearFirstColumnStep {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (i : Fin (m + 1)) (state : LeftTransform A) : LeftTransform A :=
  if _hzero : ComputableEuclideanOps.isZeroB (state.base.B i.succ 0) = true then
    state
  else
    let swapped := state.trans (LeftTransform.swap state.base.B i.succ 1)
    let bezout := swapped.trans (LeftTransform.topBezout swapped.base.B)
    bezout.trans <| LeftTransform.unitScale bezout.base.B 0 <|
      ComputableEuclideanOps.normUnitUnit (bezout.base.B 0 0)

theorem clearFirstColumnStep_base {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (i : Fin (m + 1)) (state : LeftTransform A) :
    (clearFirstColumnStep i state).base =
      NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep i state.base := by
  by_cases hzero :
      ComputableEuclideanOps.isZeroB (state.base.B i.succ 0) = true
  · simp [clearFirstColumnStep,
      NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep, hzero]
  · simp [clearFirstColumnStep,
      NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep, hzero,
      LeftTransform.trans, LeftTransform.swap, LeftTransform.topBezout,
      LeftTransform.unitScale, LeftTransform.ofPrimitive]

theorem clearFirstColumnStep_steps_length_le {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (i : Fin (m + 1)) (state : LeftTransform A) :
    (clearFirstColumnStep i state).steps.length ≤ state.steps.length + 3 := by
  by_cases hzero :
      ComputableEuclideanOps.isZeroB (state.base.B i.succ 0) = true
  · simp [clearFirstColumnStep, hzero]
  · simp [clearFirstColumnStep, hzero, LeftTransform.trans,
      LeftTransform.swap, LeftTransform.topBezout, LeftTransform.unitScale,
      LeftTransform.ofPrimitive]

def clearFirstColumnLoop {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int} :
    (k : Nat) → k ≤ m + 1 → LeftTransform A → LeftTransform A
  | 0, _, state => state
  | k + 1, hk, state =>
      let hk' := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let previous := clearFirstColumnLoop k hk' state
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      clearFirstColumnStep i previous

theorem clearFirstColumnLoop_base {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (k : Nat) (hk : k ≤ m + 1) (state : LeftTransform A) :
    (clearFirstColumnLoop k hk state).base =
      NormalForms.Matrix.Hermite.Internal.clearFirstColumnLoop k hk state.base := by
  induction k generalizing state with
  | zero => rfl
  | succ k ih =>
      let hk' : k ≤ m + 1 :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let previous := clearFirstColumnLoop k hk' state
      let i : Fin (m + 1) :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      calc
        (clearFirstColumnLoop (k + 1) hk state).base =
            (clearFirstColumnStep i previous).base := by rfl
        _ = NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep
              i previous.base := clearFirstColumnStep_base i previous
        _ = NormalForms.Matrix.Hermite.Internal.clearFirstColumnStep i
              (NormalForms.Matrix.Hermite.Internal.clearFirstColumnLoop
                k hk' state.base) := by rw [ih hk' state]
        _ = NormalForms.Matrix.Hermite.Internal.clearFirstColumnLoop
              (k + 1) hk state.base := by rfl

theorem clearFirstColumnLoop_steps_length_le {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (k : Nat) (hk : k ≤ m + 1) (state : LeftTransform A) :
    (clearFirstColumnLoop k hk state).steps.length ≤
      state.steps.length + 3 * k := by
  induction k generalizing state with
  | zero => simp [clearFirstColumnLoop]
  | succ k ih =>
      let hk' : k ≤ m + 1 :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let previous := clearFirstColumnLoop k hk' state
      let i : Fin (m + 1) :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      calc
        (clearFirstColumnLoop (k + 1) hk state).steps.length =
            (clearFirstColumnStep i previous).steps.length := by rfl
        _ ≤ previous.steps.length + 3 :=
          clearFirstColumnStep_steps_length_le i previous
        _ ≤ (state.steps.length + 3 * k) + 3 :=
          Nat.add_le_add_right (ih hk' state) 3
        _ = state.steps.length + 3 * (k + 1) := by omega

def reduceTopRowStep {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (i : Fin (m + 1)) (state : LeftTransform A) : LeftTransform A :=
  match firstNonzeroExec? (fun j : Fin n => state.base.B i.succ j.succ) with
  | none => state
  | some j =>
      state.trans <| LeftTransform.add state.base.B i.succ 0
        (NormalForms.Matrix.Hermite.Internal.topReductionCoeff state.base.B i j)
        (by simp)

theorem reduceTopRowStep_base {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (i : Fin (m + 1)) (state : LeftTransform A) :
    (reduceTopRowStep i state).base =
      NormalForms.Matrix.Hermite.Internal.reduceTopRowStep i state.base := by
  unfold reduceTopRowStep
  rw [firstNonzeroExec?_eq_firstNonzero?]
  unfold NormalForms.Matrix.Hermite.Internal.reduceTopRowStep
  rw [NormalForms.Matrix.Hermite.Internal.firstNonzeroWithOps?_eq_firstNonzero?]
  cases firstNonzero? (fun j : Fin n => state.base.B i.succ j.succ) <;>
    simp [LeftTransform.trans, LeftTransform.add, LeftTransform.ofPrimitive]

theorem reduceTopRowStep_steps_length_le {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (i : Fin (m + 1)) (state : LeftTransform A) :
    (reduceTopRowStep i state).steps.length ≤ state.steps.length + 1 := by
  unfold reduceTopRowStep
  cases firstNonzeroExec? (fun j : Fin n => state.base.B i.succ j.succ) <;>
    simp [LeftTransform.trans, LeftTransform.add, LeftTransform.ofPrimitive]

def reduceTopRowLoop {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int} :
    (k : Nat) → k ≤ m + 1 → LeftTransform A → LeftTransform A
  | 0, _, state => state
  | k + 1, hk, state =>
      let hk' := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let previous := reduceTopRowLoop k hk' state
      let i : Fin (m + 1) := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      reduceTopRowStep i previous

theorem reduceTopRowLoop_base {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (k : Nat) (hk : k ≤ m + 1) (state : LeftTransform A) :
    (reduceTopRowLoop k hk state).base =
      NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop k hk state.base := by
  induction k generalizing state with
  | zero => rfl
  | succ k ih =>
      let hk' : k ≤ m + 1 :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let previous := reduceTopRowLoop k hk' state
      let i : Fin (m + 1) :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      calc
        (reduceTopRowLoop (k + 1) hk state).base =
            (reduceTopRowStep i previous).base := by rfl
        _ = NormalForms.Matrix.Hermite.Internal.reduceTopRowStep
              i previous.base := reduceTopRowStep_base i previous
        _ = NormalForms.Matrix.Hermite.Internal.reduceTopRowStep i
              (NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop
                k hk' state.base) := by rw [ih hk' state]
        _ = NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop
              (k + 1) hk state.base := by rfl

theorem reduceTopRowLoop_steps_length_le {m n : Nat}
    {A : _root_.Matrix (Fin (m + 2)) (Fin (n + 1)) Int}
    (k : Nat) (hk : k ≤ m + 1) (state : LeftTransform A) :
    (reduceTopRowLoop k hk state).steps.length ≤
      state.steps.length + k := by
  induction k generalizing state with
  | zero => simp [reduceTopRowLoop]
  | succ k ih =>
      let hk' : k ≤ m + 1 :=
        Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      let previous := reduceTopRowLoop k hk' state
      let i : Fin (m + 1) :=
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      calc
        (reduceTopRowLoop (k + 1) hk state).steps.length =
            (reduceTopRowStep i previous).steps.length := by rfl
        _ ≤ previous.steps.length + 1 :=
          reduceTopRowStep_steps_length_le i previous
        _ ≤ (state.steps.length + k) + 1 :=
          Nat.add_le_add_right (ih hk' state) 1
        _ = state.steps.length + (k + 1) := by omega

abbrev Computation {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) :=
  Σ result : HNFResultFin A,
    { trace : ExecutionTrace A result //
      trace.steps.IsPrimitive ∧ trace.steps.length ≤ 4 * m * n }

def compute {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : Computation A := by
  let finish := fun {m n : Nat}
      {A : _root_.Matrix (Fin m) (Fin n) Int}
      (transform : LeftTransform A)
      (isHermite : IsHermiteNormalFormFin transform.base.B)
      (lengthBound : transform.steps.length ≤ 4 * m * n) =>
    let result : HNFResultFin A :=
      { U := transform.base.U
        U_cert := transform.base.U_cert
        H := transform.base.B
        equation := transform.base.left_mul
        isHermite }
    let trace : ExecutionTrace A result :=
      { steps := transform.steps
        accumulator_eq := transform.accumulator_eq
        inverseAccumulator_eq := transform.inverseAccumulator_eq }
    (show Computation A from
      ⟨result, trace, transform.primitive, lengthBound⟩)
  let restore := fun {m n : Nat}
      {A : _root_.Matrix (Fin m) (Fin n) Int}
      (bundle : Computation A) =>
    (show LeftTransform A from
      { base :=
          { U := bundle.1.U
            U_cert := bundle.1.U_cert
            B := bundle.1.H
            left_mul := bundle.1.equation }
        steps := bundle.2.1.steps
        accumulator_eq := bundle.2.1.accumulator_eq
        inverseAccumulator_eq := bundle.2.1.inverseAccumulator_eq
        primitive := bundle.2.2.1 })
  induction n generalizing m with
  | zero =>
      exact finish (LeftTransform.refl A) (IsHermiteNormalFormFin.emptyCols _) (by
        simp [LeftTransform.refl])
  | succ n ih =>
      cases m with
      | zero =>
          exact finish (LeftTransform.refl A) (IsHermiteNormalFormFin.emptyRows _) (by
            simp [LeftTransform.refl])
      | succ m =>
          by_cases hcol :
              firstNonzeroExec? (fun i : Fin (m + 1) => A i 0) = none
          · let tail := ih (m := m + 1) (tailCols A)
            let tailTransform := restore tail
            let transformed := LeftTransform.actOnFrom A tailTransform
            apply finish transformed
            · refine IsHermiteNormalFormFin.zeroCol transformed.base.B ?_ ?_
              · exact
                  NormalForms.Matrix.Hermite.firstCol_zero_mul
                    tailTransform.base.U A <|
                    firstNonzero?_eq_none (fun i : Fin (m + 1) => A i 0) (by
                      simpa using hcol)
              · simpa [transformed, LeftTransform.actOnFrom,
                  NormalForms.Matrix.Hermite.tailCols_mul,
                  tailTransform.base.left_mul] using tail.1.isHermite
            · change tail.2.1.steps.length ≤ 4 * (m + 1) * (n + 1)
              exact tail.2.2.2.trans <|
                Nat.mul_le_mul_left (4 * (m + 1)) (Nat.le_succ n)
          · cases m with
            | zero =>
                have h00 : A 0 0 ≠ 0 := by
                  cases hfirst :
                      firstNonzeroExec? (fun i : Fin 1 => A i 0) with
                  | none => exact False.elim (hcol hfirst)
                  | some i =>
                      cases i using Fin.cases with
                      | zero =>
                          exact firstNonzero?_some_ne_zero
                            (fun i : Fin 1 => A i 0) (by simpa using hfirst)
                      | succ i => exact Fin.elim0 i
                let normalized := LeftTransform.unitScale A 0 <|
                  ComputableEuclideanOps.normUnitUnit (A 0 0)
                have hNormEq : normalized.base.B 0 0 = normalize (A 0 0) := by
                  simp [normalized, LeftTransform.unitScale,
                    LeftTransform.ofPrimitive,
                    NormalForms.Matrix.Hermite.LeftTransform.unitSmul,
                    NormalForms.Matrix.Elementary.applyRowOperation,
                    normalize_apply, mul_comm]
                apply finish normalized
                · refine IsHermiteNormalFormFin.pivot normalized.base.B ?_ ?_ ?_ ?_ ?_
                  · rw [hNormEq]
                    exact mt normalize_eq_zero.mp h00
                  · rw [hNormEq]
                    exact
                      (ComputableEuclideanOps.normalize_idem_constructive (A 0 0)).symm
                  · intro i
                    exact Fin.elim0 i
                  · exact IsHermiteNormalFormFin.emptyRows _
                  · intro i
                    exact Fin.elim0 i
                · simp [normalized, LeftTransform.unitScale,
                    LeftTransform.ofPrimitive]
                  omega
            | succ m =>
                cases hfirst :
                    firstNonzeroExec? (fun i : Fin (m + 2) => A i 0) with
                | none => exact False.elim (hcol hfirst)
                | some i =>
                    let swapped := LeftTransform.swap A i 0
                    let normalized := swapped.trans <|
                      LeftTransform.unitScale swapped.base.B 0 <|
                        ComputableEuclideanOps.normUnitUnit (swapped.base.B 0 0)
                    have hi0 : A i 0 ≠ 0 := by
                      exact firstNonzero?_some_ne_zero
                        (fun i : Fin (m + 2) => A i 0) (by simpa using hfirst)
                    have hNormEq : normalized.base.B 0 0 = normalize (A i 0) := by
                      by_cases hi : i = 0
                      · subst hi
                        simp [normalized, swapped, LeftTransform.trans,
                          LeftTransform.unitScale, LeftTransform.swap,
                          LeftTransform.ofPrimitive,
                          NormalForms.Matrix.Hermite.LeftTransform.unitSmul,
                          NormalForms.Matrix.Hermite.LeftTransform.swap,
                          NormalForms.Matrix.Hermite.LeftTransform.trans,
                          NormalForms.Matrix.Elementary.applyRowOperation,
                          normalize_apply, mul_comm]
                      · simp [normalized, swapped, LeftTransform.trans,
                          LeftTransform.unitScale, LeftTransform.swap,
                          LeftTransform.ofPrimitive,
                          NormalForms.Matrix.Hermite.LeftTransform.unitSmul,
                          NormalForms.Matrix.Hermite.LeftTransform.swap,
                          NormalForms.Matrix.Hermite.LeftTransform.trans,
                          NormalForms.Matrix.Elementary.applyRowOperation,
                          normalize_apply, mul_comm,
                          show ¬ (0 : Fin (m + 2)) = i by simpa [eq_comm] using hi]
                    have hNormTopNonzero : normalized.base.B 0 0 ≠ 0 := by
                      rw [hNormEq]
                      exact mt normalize_eq_zero.mp hi0
                    have hNormTopNormalized :
                        normalized.base.B 0 0 = normalize (normalized.base.B 0 0) := by
                      rw [hNormEq]
                      exact (ComputableEuclideanOps.normalize_idem_constructive (A i 0)).symm
                    let cleared :=
                      clearFirstColumnLoop (A := A) (m + 1) le_rfl normalized
                    let lower := ih (m := m + 1) (lowerRight cleared.base.B)
                    let lowerTransform := restore lower
                    let lifted :=
                      LeftTransform.leadingLift cleared.base.B lowerTransform
                    let afterLift := cleared.trans lifted
                    let final :=
                      reduceTopRowLoop (A := A) (m + 1) le_rfl afterLift
                    have hClearTopNonzero : cleared.base.B 0 0 ≠ 0 := by
                      rw [clearFirstColumnLoop_base]
                      exact
                        NormalForms.Matrix.Hermite.Internal.clearFirstColumnLoop_topLeft_ne_zero
                          (m + 1) le_rfl normalized.base hNormTopNonzero
                    have hClearTopNormalized :
                        cleared.base.B 0 0 = normalize (cleared.base.B 0 0) := by
                      rw [clearFirstColumnLoop_base]
                      exact
                        NormalForms.Matrix.Hermite.Internal.clearFirstColumnLoop_topLeft_normalized
                          (m + 1) le_rfl normalized.base hNormTopNormalized
                    have hClearBelow :
                        ∀ r : Fin (m + 1), cleared.base.B r.succ 0 = 0 := by
                      intro r
                      rw [clearFirstColumnLoop_base]
                      exact
                        NormalForms.Matrix.Hermite.Internal.clearFirstColumnLoop_prefix_zero
                          (m + 1) le_rfl normalized.base r r.is_lt
                    have hAfterLiftLower :
                        lowerRight afterLift.base.B = lowerTransform.base.B := by
                      simp [afterLift, lifted, LeftTransform.leadingLift,
                        LeftTransform.trans,
                        NormalForms.Matrix.Hermite.LeftTransform.diagLift,
                        NormalForms.Matrix.Hermite.LeftTransform.trans,
                        NormalForms.Matrix.Hermite.lowerRight_diagLiftMatrix_mul,
                        lowerTransform.base.left_mul]
                    have hAfterLiftTop : afterLift.base.B 0 0 = cleared.base.B 0 0 := by
                      simp [afterLift, lifted, LeftTransform.leadingLift,
                        LeftTransform.trans,
                        NormalForms.Matrix.Hermite.LeftTransform.diagLift,
                        NormalForms.Matrix.Hermite.LeftTransform.trans,
                        NormalForms.Matrix.Hermite.diagLiftMatrix_mul_topRow]
                    have hAfterLiftBelow :
                        ∀ r : Fin (m + 1), afterLift.base.B r.succ 0 = 0 := by
                      intro r
                      simp [afterLift, lifted, LeftTransform.leadingLift,
                        LeftTransform.trans,
                        NormalForms.Matrix.Hermite.LeftTransform.diagLift,
                        NormalForms.Matrix.Hermite.LeftTransform.trans,
                        _root_.Matrix.mul_apply,
                        NormalForms.Matrix.Hermite.diagLiftMatrix, hClearBelow,
                        NormalForms.Matrix.Constructive.sum_univ_succ]
                    have hFinalTop : final.base.B 0 0 = afterLift.base.B 0 0 := by
                      rw [reduceTopRowLoop_base]
                      exact
                        NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop_topLeft
                          (m + 1) le_rfl afterLift.base hAfterLiftBelow
                    have hFinalBelow :
                        ∀ r : Fin (m + 1), final.base.B r.succ 0 = 0 := by
                      rw [reduceTopRowLoop_base]
                      exact
                        NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop_below_zero
                          (m + 1) le_rfl afterLift.base hAfterLiftBelow
                    have hFinalLower :
                        lowerRight final.base.B = lowerTransform.base.B := by
                      rw [reduceTopRowLoop_base,
                        NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop_lowerRight,
                        hAfterLiftLower]
                    have hFinalReduced :
                        ∀ r : Fin (m + 1),
                          match firstNonzero? (fun s : Fin n => final.base.B r.succ s.succ) with
                          | none => True
                          | some j =>
                              final.base.B 0 j.succ =
                                final.base.B 0 j.succ % final.base.B r.succ j.succ := by
                      intro r
                      rw [reduceTopRowLoop_base]
                      have hLowerHNF : IsHermiteNormalFormFin (lowerRight afterLift.base.B) := by
                        simpa [hAfterLiftLower] using lower.1.isHermite
                      have hRowEq :
                          (NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop
                            (m + 1) le_rfl afterLift.base).B r.succ =
                            afterLift.base.B r.succ :=
                        NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop_lowerRow
                          (m + 1) le_rfl afterLift.base r
                      rw [hRowEq]
                      cases hrow :
                          firstNonzero? (fun s : Fin n => afterLift.base.B r.succ s.succ) with
                      | none => simp
                      | some j =>
                          have hReduced :=
                            NormalForms.Matrix.Hermite.Internal.reduceTopRowLoop_reduced_prefix
                              (m + 1) le_rfl afterLift.base hLowerHNF hAfterLiftBelow r r.is_lt
                          rw [hrow] at hReduced
                          exact hReduced
                    apply finish final
                    · refine IsHermiteNormalFormFin.pivot final.base.B ?_ ?_ ?_ ?_ ?_
                      · rw [hFinalTop, hAfterLiftTop]
                        exact hClearTopNonzero
                      · rw [hFinalTop, hAfterLiftTop]
                        exact hClearTopNormalized
                      · exact hFinalBelow
                      · simpa [hFinalLower] using lower.1.isHermite
                      · exact hFinalReduced
                    · have hNormalizedLength : normalized.steps.length = 2 := by
                        simp [normalized, swapped, LeftTransform.trans,
                          LeftTransform.swap, LeftTransform.unitScale,
                          LeftTransform.ofPrimitive]
                      have hClearedLength :=
                        clearFirstColumnLoop_steps_length_le
                          (m + 1) le_rfl normalized
                      have hClearedLength' :
                          cleared.steps.length ≤ 2 + 3 * (m + 1) := by
                        calc
                          cleared.steps.length ≤
                              normalized.steps.length + 3 * (m + 1) := by
                            simpa [cleared] using hClearedLength
                          _ = 2 + 3 * (m + 1) := by rw [hNormalizedLength]
                      have hLowerLength :
                          lower.2.1.steps.length ≤ 4 * (m + 1) * n :=
                        lower.2.2.2
                      have hAfterLiftLength :
                          afterLift.steps.length =
                            cleared.steps.length + lower.2.1.steps.length := by
                        simp [afterLift, lifted, lowerTransform,
                          LeftTransform.trans, LeftTransform.leadingLift,
                          RowTrace.leadingLift, restore]
                      have hFinalLength :=
                        reduceTopRowLoop_steps_length_le
                          (m + 1) le_rfl afterLift
                      calc
                        final.steps.length ≤
                            afterLift.steps.length + (m + 1) := hFinalLength
                        _ = cleared.steps.length + lower.2.1.steps.length +
                            (m + 1) := by rw [hAfterLiftLength]
                        _ ≤ (2 + 3 * (m + 1)) + (4 * (m + 1) * n) +
                            (m + 1) :=
                          Nat.add_le_add_right
                            (Nat.add_le_add hClearedLength' hLowerLength) (m + 1)
                        _ ≤ 4 * (m + 2) * (n + 1) := by nlinarith

public def _root_.NormalForms.Research.KannanBachem.Hermite.primitiveHermiteNormalForm
    {m n : Nat} (A : _root_.Matrix (Fin m) (Fin n) Int) : HNFResultFin A :=
  (compute A).1

public def _root_.NormalForms.Research.KannanBachem.Hermite.primitiveHermiteTrace
    {m n : Nat} (A : _root_.Matrix (Fin m) (Fin n) Int) :
    ExecutionTrace A (primitiveHermiteNormalForm A) :=
  (compute A).2.1

public theorem _root_.NormalForms.Research.KannanBachem.Hermite.primitiveHermiteTrace_isPrimitive
    {m n : Nat} (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (primitiveHermiteTrace A).steps.IsPrimitive := by
  simpa [primitiveHermiteTrace] using (compute A).2.2.1

public theorem _root_.NormalForms.Research.KannanBachem.Hermite.primitiveHermiteTrace_length_le
    {m n : Nat} (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (primitiveHermiteTrace A).steps.length ≤ 4 * m * n := by
  simpa [primitiveHermiteTrace] using (compute A).2.2.2

public theorem _root_.NormalForms.Research.KannanBachem.Hermite.primitiveHermite_equation
    {m n : Nat} (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (primitiveHermiteNormalForm A).U * A = (primitiveHermiteNormalForm A).H :=
  (primitiveHermiteNormalForm A).equation

public theorem _root_.NormalForms.Research.KannanBachem.Hermite.primitiveHermite_isHermite
    {m n : Nat} (A : _root_.Matrix (Fin m) (Fin n) Int) :
    IsHermiteNormalFormFin (primitiveHermiteNormalForm A).H :=
  (primitiveHermiteNormalForm A).isHermite

public theorem _root_.NormalForms.Research.KannanBachem.Hermite.primitiveHermite_inverse_equation
    {m n : Nat} (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (primitiveHermiteNormalForm A).U_cert.inverse *
        (primitiveHermiteNormalForm A).H = A := by
  rw [← (primitiveHermiteTrace A).inverseAccumulator_eq]
  exact (primitiveHermiteTrace A).inverse_mul_result

public theorem _root_.NormalForms.Research.KannanBachem.Hermite.primitiveHermite_eq_reference
    {m n : Nat} (A : _root_.Matrix (Fin m) (Fin n) Int) :
    (primitiveHermiteNormalForm A).H = (semanticReference A).H := by
  let primitive := primitiveHermiteNormalForm A
  let reference := semanticReference A
  let change := reference.U * primitive.U_cert.inverse
  have changeCert : MatrixInverseCertificate change :=
    reference.U_cert.mul primitive.U_cert.symm
  apply isHermiteNormalFormFin_unique_of_left_equiv
    primitive.isHermite reference.isHermite changeCert.unimodular
  calc
    change * primitive.H =
        reference.U * (primitive.U_cert.inverse * primitive.H) := by
      rw [_root_.Matrix.mul_assoc]
    _ = reference.U * A := by
      rw [show primitive.U_cert.inverse * primitive.H = A by
        simpa [primitive] using primitiveHermite_inverse_equation A]
    _ = reference.H := reference.equation

end Traced

end NormalForms.Research.KannanBachem.Hermite
