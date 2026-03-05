import NormalForms.Matrix.Certificates

/-!
# Smith Normal Form API

This is the top-level API skeleton for two-sided Smith normal forms.
-/

namespace NormalForms.Matrix.Smith

open scoped Matrix

def IsSmithNormalForm {m n R : Type _} [Zero R] (_ : _root_.Matrix m n R) : Prop :=
  True

structure SNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  S : _root_.Matrix m n R
  V : _root_.Matrix n n R
  two_sided_mul : U * A * V = S
  isSmith : IsSmithNormalForm S

def SNFResult.toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    NormalForms.Matrix.Certificates.TwoSidedCertificate A :=
  { U := result.U
    result := result.S
    V := result.V
    equation := result.two_sided_mul }

def smithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    (A : _root_.Matrix m n R) : Option (SNFResult A) :=
  none

end NormalForms.Matrix.Smith
