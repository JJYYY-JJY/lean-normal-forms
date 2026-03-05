import NormalForms.Matrix.Smith

/-!
# PID Bridge

Placeholder bridge statements that will align executable Smith normal forms
with mathlib's PID-side structural theorems.
-/

namespace NormalForms.Bridge.MathlibPID

def InvariantFactorsAgreeUpToNormalization {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    (_ : _root_.Matrix m n R) : Prop :=
  True

theorem executableSNFMatchesPID {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    (A : _root_.Matrix m n R) : InvariantFactorsAgreeUpToNormalization A := by
  trivial

end NormalForms.Bridge.MathlibPID
