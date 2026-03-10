import NormalForms.Matrix.Smith

/-!
# PID Bridge Shapes

Bridge-side frozen object shapes for comparing executable Smith data with
mathlib's PID-side `Submodule.smithNormalForm` API in a later phase.
-/

namespace NormalForms.Bridge.MathlibPID

abbrev pidSmithColumnSpan {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    (A : _root_.Matrix m n R) : Submodule R (m -> R) :=
  NormalForms.Matrix.Smith.smithColumnSpan A

@[simp] theorem pidSmithColumnSpan_eq_range_mulVecLin {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [EuclideanDomain R]
    (A : _root_.Matrix m n R) :
    pidSmithColumnSpan A = LinearMap.range A.mulVecLin := by
  unfold pidSmithColumnSpan NormalForms.Matrix.Smith.smithColumnSpan
  rfl

noncomputable def pidExecutableInvariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (S : _root_.Matrix m n R) : List R :=
  NormalForms.Matrix.Smith.smithInvariantFactors S

noncomputable def pidSmithNormalFormData {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) :
    Σ k : ℕ, Module.Basis.SmithNormalForm (pidSmithColumnSpan A) m k :=
  Submodule.smithNormalForm (Pi.basisFun R m) (pidSmithColumnSpan A)

noncomputable def pidSmithNormalFormCoeffs {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) :
    Fin (pidSmithNormalFormData A).1 -> R :=
  (pidSmithNormalFormData A).2.a

noncomputable def pidFullRankSmithNormalFormCoeffs {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R)
    (hfull : Module.finrank R (pidSmithColumnSpan A) = Fintype.card m) :
    m -> R :=
  let b := Pi.basisFun R m
  let hfull' : Module.finrank R (pidSmithColumnSpan A) = Module.finrank R (m -> R) := by
    simpa [Module.finrank_eq_card_basis b] using hfull
  Submodule.smithNormalFormCoeffs b hfull'

end NormalForms.Bridge.MathlibPID
