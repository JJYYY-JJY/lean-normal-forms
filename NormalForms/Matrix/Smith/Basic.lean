import NormalForms.Matrix.Smith.Algorithm

/-!
# Smith Normal Form API

Public Smith result packaging and the executable wrapper over arbitrary finite index types.
-/

namespace NormalForms.Matrix.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

structure SNFResult {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix m n R) where
  U : _root_.Matrix m m R
  S : _root_.Matrix m n R
  V : _root_.Matrix n n R
  two_sided_mul : U * A * V = S
  isSmith : IsSmithNormalForm S

noncomputable def SNFResult.invariantFactors {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R} (result : SNFResult A) : List R :=
  smithInvariantFactors result.S

/-- Package an existing two-sided certificate together with a Smith witness.

This is the intended public constructor when an external proof or example has
already produced a concrete two-sided certificate and a separate Smith witness.
It keeps the public result API lightweight without forcing users to build the
internal Smith recursion infrastructure.
-/
def SNFResult.ofCertificate {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix m n R}
    (cert : NormalForms.Matrix.Certificates.TwoSidedCertificate A)
    (hSmith : IsSmithNormalForm cert.result) :
    SNFResult A :=
  { U := cert.U
    S := cert.result
    V := cert.V
    two_sided_mul := cert.equation
    isSmith := hSmith }


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


/-- Executable Smith-normal-form entrypoint. -/
noncomputable def smithNormalForm {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [CanonicalMod R]
    (A : _root_.Matrix m n R) : Option (SNFResult A) :=
  let em := Fintype.equivFin m
  let en := Fintype.equivFin n
  let Afin : _root_.Matrix (Fin (Fintype.card m)) (Fin (Fintype.card n)) R :=
    _root_.Matrix.reindex em en A
  let result := Internal.smithNormalFormFin Afin
  some
    { U := _root_.Matrix.reindex em.symm em.symm result.U
      S := _root_.Matrix.reindex em.symm en.symm result.S
      V := _root_.Matrix.reindex en.symm en.symm result.V
      two_sided_mul := by
        have hmulRight :
            _root_.Matrix.reindex em.symm en.symm (result.U * Afin * result.V) =
              _root_.Matrix.reindex em.symm en.symm (result.U * Afin) *
                _root_.Matrix.reindex en.symm en.symm result.V := by
          have h :=
            Matrix.reindexLinearEquiv_mul R R em.symm en.symm en.symm
              (result.U * Afin) result.V
          convert h using 1
          simp [Matrix.reindexLinearEquiv, Matrix.mul_assoc]
        have hmulLeft :
            _root_.Matrix.reindex em.symm en.symm (result.U * Afin) =
              _root_.Matrix.reindex em.symm em.symm result.U *
                _root_.Matrix.reindex em.symm en.symm Afin := by
          have h :=
            Matrix.reindexLinearEquiv_mul R R em.symm em.symm en.symm result.U Afin
          convert h using 1
          simp [Matrix.reindexLinearEquiv]
        have hEq := congrArg (_root_.Matrix.reindex em.symm en.symm) result.two_sided_mul
        calc
          _root_.Matrix.reindex em.symm em.symm result.U * A *
              _root_.Matrix.reindex en.symm en.symm result.V
              = _root_.Matrix.reindex em.symm en.symm (result.U * Afin * result.V) := by
                  rw [hmulRight, hmulLeft]
                  simp [Afin, Matrix.mul_assoc]
          _ = _root_.Matrix.reindex em.symm en.symm result.S := hEq
      isSmith := by
        unfold IsSmithNormalForm
        convert Internal.isSmithNormalFormFin_toDiag result.isSmith using 1
        ext i j
        simp [em, en] }


theorem smithNormalForm_exists {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    (A : _root_.Matrix m n R) : ∃ result, smithNormalForm A = some result := by
  unfold smithNormalForm
  simp


theorem smithNormalForm_leftUnimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix m n R} {result : SNFResult A}
    (hresult : smithNormalForm A = some result) :
    Unimodular result.U := by
  unfold smithNormalForm at hresult
  dsimp at hresult
  injection hresult with hEq
  subst hEq
  exact unimodular_reindex (Fintype.equivFin m).symm
    (Internal.smithNormalFormFin
      (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)).leftUnimodular


theorem smithNormalForm_rightUnimodular {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R] [CanonicalMod R]
    {A : _root_.Matrix m n R} {result : SNFResult A}
    (hresult : smithNormalForm A = some result) :
    Unimodular result.V := by
  unfold smithNormalForm at hresult
  dsimp at hresult
  injection hresult with hEq
  subst hEq
  exact unimodular_reindex (Fintype.equivFin n).symm
    (Internal.smithNormalFormFin
      (_root_.Matrix.reindex (Fintype.equivFin m) (Fintype.equivFin n) A)).rightUnimodular


theorem smithNormalForm_isSmith {m n R : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    [CanonicalMod R]
    {A : _root_.Matrix m n R} {result : SNFResult A}
    (_hresult : smithNormalForm A = some result) :
    IsSmithNormalForm result.S := by
  exact result.isSmith

end NormalForms.Matrix.Smith
