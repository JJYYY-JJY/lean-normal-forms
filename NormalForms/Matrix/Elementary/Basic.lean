import NormalForms.Basic

/-!
# Elementary Matrix Operations

This module reserves the namespace for row and column operations, operation
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

def applyStep {m n R} (A : _root_.Matrix m n R) (_ : MatrixStep R m n) : _root_.Matrix m n R :=
  A

def replayLog {m n R} (A : _root_.Matrix m n R) (log : OperationLog R m n) : _root_.Matrix m n R :=
  log.foldl applyStep A

end NormalForms.Matrix.Elementary
