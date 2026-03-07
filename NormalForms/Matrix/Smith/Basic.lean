import NormalForms.Matrix.Certificates
import NormalForms.Matrix.Hermite.Basic

/-!
# Smith Normal Form API

Frozen public API scaffold for two-sided Smith normal forms.

The declarations in this module are the Phase 3 public interface checkpoint.
The executable Smith algorithm and its correctness / uniqueness proofs are
deliberately deferred to later work; the current predicate and algorithm
remain scaffolds.
-/

namespace NormalForms.Matrix.Smith

open scoped Matrix

/-- Placeholder public predicate for Smith normal form.

This remains a scaffold during the API-freeze milestone: it carries the
intended specification-side typeclass boundary, but its body is still `True`
until the later algorithmic and proof phases fill in the real invariant.
-/
def IsSmithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (_ : _root_.Matrix m n R) : Prop :=
  True

/-- Public result package for a two-sided Smith normal form transform.

This records only the left matrix `U`, the Smith-form candidate `S`, the right
matrix `V`, the equation `U * A * V = S`, and the Smith-form witness. Future
phases will expose unimodularity of `U` and `V` via separate helper theorems,
not as fields of this structure.
-/
structure SNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  S : _root_.Matrix m n R
  V : _root_.Matrix n n R
  two_sided_mul : U * A * V = S
  isSmith : IsSmithNormalForm S

/-- Forget the Smith witness and keep only the two-sided transformation data. -/
def SNFResult.toCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) :
    NormalForms.Matrix.Certificates.TwoSidedCertificate A :=
  { U := result.U
    result := result.S
    V := result.V
    equation := result.two_sided_mul }

/-- Frozen executable entrypoint for Smith normal form.

The signature already matches the intended public boundary, including the
`CanonicalMod` assumption used to express exact canonical representatives.
The implementation is still a scaffold and currently returns `none`.
-/
noncomputable def smithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [NormalForms.Matrix.Hermite.CanonicalMod R]
    (A : _root_.Matrix m n R) : Option (SNFResult A) :=
  none

end NormalForms.Matrix.Smith
