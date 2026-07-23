/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.Trace
public import NormalForms.Euclidean.Int

/-! Public instrumentation types for the principal-minor HNF schedule. -/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix

/-- One paper-level event in the transposed principal-minor schedule. -/
public inductive PrincipalEvent where
  | gcdEliminate (pivot target : Nat)
  | reduceAbove (source destination : Nat)
  | normalize (row : Nat)
  deriving DecidableEq, Repr

namespace PrincipalEvent

/-- Every event index lies in range and has the strict order used by the paper. -/
@[expose] public def Valid (n : Nat) : PrincipalEvent → Prop
  | .gcdEliminate pivot target => pivot < target ∧ target < n
  | .reduceAbove source destination => source < destination ∧ destination < n
  | .normalize row => row < n

end PrincipalEvent

/-- Arithmetic operands consumed by one paper-level principal transition. -/
public inductive PrincipalArithmeticEvent where
  | xgcd (pivot target : Nat) (left right : Int)
  | divMod (source destination : Nat) (numerator divisor : Int)
  | normalize (row : Nat) (value : Int)
  deriving DecidableEq, Repr

namespace PrincipalArithmeticEvent

/-- The indices attached to every arithmetic event lie in range. -/
@[expose] public def Valid (n : Nat) : PrincipalArithmeticEvent → Prop
  | .xgcd pivot target _ _ => pivot < target ∧ target < n
  | .divMod source destination _ _ => source < destination ∧ destination < n
  | .normalize row _ => row < n

end PrincipalArithmeticEvent

/--
An executable principal-minor run.  This is instrumentation, not a competing
normal-form result type: the transformed matrix is not asserted to be HNF.
-/
public structure PrincipalRun {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) where
  matrix : _root_.Matrix (Fin n) (Fin n) Int
  steps : RowTrace Int n
  events : List PrincipalEvent
  arithmeticEvents : List PrincipalArithmeticEvent
  equation : steps.accumulator * A = matrix
  primitive : steps.IsPrimitive
  validEvents : events.Forall (PrincipalEvent.Valid n)
  validArithmeticEvents :
    arithmeticEvents.Forall (PrincipalArithmeticEvent.Valid n)

/--
Control-only principal schedule used by value-producing executions.  It
contains no candidate matrix or multiplier value.
-/
public structure PrincipalSchedule (n : Nat) where
  steps : RowTrace Int n
  arithmeticEvents : List PrincipalArithmeticEvent
  validArithmeticEvents :
    arithmeticEvents.Forall (PrincipalArithmeticEvent.Valid n)

end NormalForms.Research.KannanBachem.Hermite
