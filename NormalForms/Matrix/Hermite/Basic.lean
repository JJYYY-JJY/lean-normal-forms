import NormalForms.Matrix.Certificates

/-!
# Hermite Normal Form API

This is the top-level API skeleton for row-style Hermite normal forms.
-/

namespace NormalForms.Matrix.Hermite

open scoped Matrix

def IsHermiteNormalForm {m n R : Type _} [Zero R] (_ : _root_.Matrix m n R) : Prop :=
  True

structure HNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  H : _root_.Matrix m n R
  left_mul : U * A = H
  isHermite : IsHermiteNormalForm H

def HNFResult.toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing R]
    {A : _root_.Matrix m n R} (result : HNFResult A) :
    NormalForms.Matrix.Certificates.LeftCertificate A :=
  { U := result.U
    result := result.H
    equation := result.left_mul }

def hermiteNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    (A : _root_.Matrix m n R) : Option (HNFResult A) :=
  none

end NormalForms.Matrix.Hermite
