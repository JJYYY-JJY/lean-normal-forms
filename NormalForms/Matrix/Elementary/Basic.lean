import NormalForms.Basic

/-!
# Elementary Matrix Operations

This module provides executable row and column operations, operation
logs, and small-step replay semantics.
-/

namespace NormalForms.Matrix.Elementary

inductive RowOperation (R : Type _) (m : Type _)
  | swap (i j : m)
  | add (src dst : m) (c : R)
  | smul (i : m) (c : R)

inductive ColumnOperation (R : Type _) (n : Type _)
  | swap (i j : n)
  | add (src dst : n) (c : R)
  | smul (i : n) (c : R)

inductive MatrixStep (R : Type _) (m n : Type _)
  | row (op : RowOperation R m)
  | col (op : ColumnOperation R n)

abbrev OperationLog (R : Type _) (m n : Type _) := List (MatrixStep R m n)

open scoped Matrix

def applyRowOperation {m n R : Type _} [DecidableEq m] [Add R] [Mul R]
    (A : _root_.Matrix m n R) : RowOperation R m -> _root_.Matrix m n R
  | .swap i j => fun r c =>
      if r = i then
        A j c
      else if r = j then
        A i c
      else
        A r c
  | .add src dst k => fun r c =>
      if r = dst then
        A dst c + k * A src c
      else
        A r c
  | .smul i k => fun r c =>
      if r = i then
        k * A i c
      else
        A r c

def applyColumnOperation {m n R : Type _} [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) : ColumnOperation R n -> _root_.Matrix m n R
  | .swap i j => fun r c =>
      if c = i then
        A r j
      else if c = j then
        A r i
      else
        A r c
  | .add src dst k => fun r c =>
      if c = dst then
        A r dst + k * A r src
      else
        A r c
  | .smul i k => fun r c =>
      if c = i then
        k * A r i
      else
        A r c

def applyStep {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) : MatrixStep R m n -> _root_.Matrix m n R
  | .row op => applyRowOperation A op
  | .col op => applyColumnOperation A op

def replayLog {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) (log : OperationLog R m n) : _root_.Matrix m n R :=
  log.foldl applyStep A

@[simp] theorem replayLog_nil {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) :
    replayLog A ([] : OperationLog R m n) = A := by
  rfl

@[simp] theorem replayLog_cons {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) (step : MatrixStep R m n) (log : OperationLog R m n) :
    replayLog A (step :: log) = replayLog (applyStep A step) log := by
  rfl

theorem replayLog_append {m n R : Type _} [DecidableEq m] [DecidableEq n] [Add R] [Mul R]
    (A : _root_.Matrix m n R) (log₁ log₂ : OperationLog R m n) :
    replayLog A (log₁ ++ log₂) = replayLog (replayLog A log₁) log₂ := by
  induction log₁ generalizing A with
  | nil =>
      rfl
  | cons step rest ih =>
      simp [ih]

end NormalForms.Matrix.Elementary
