import NormalForms.Matrix.Elementary

/-!
# Certificates

Reusable certificate shapes for left and two-sided normal-form transforms.
-/

namespace NormalForms.Matrix.Certificates

open scoped Matrix

def Unimodular {m R : Type _} [Fintype m] [DecidableEq m] [CommRing R]
    (U : _root_.Matrix m m R) : Prop :=
  IsUnit U.det

structure LeftCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  result : _root_.Matrix m n R
  equation : U * A = result

structure TwoSidedCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  result : _root_.Matrix m n R
  V : _root_.Matrix n n R
  equation : U * A * V = result

end NormalForms.Matrix.Certificates
