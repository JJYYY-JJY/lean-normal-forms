/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.RationalCanonical.SmithResult
public import NormalForms.Applications.RationalCanonical.Invariants
public import NormalForms.Presentation.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval
import all NormalForms.Bridge.MathlibPID.Quotient

/-!
# Endomorphism Modules and Cyclic Decomposition

For a rational matrix `A`, the characteristic presentation `XI - A` presents
the polynomial module induced by `A`.  This module proves that statement by
constructing inverse linear maps, then composes it with the complete strong
Smith result to obtain the cyclic decomposition.

The theorem-facing decomposition retains every Smith entry, including units.
`endomorphismDisplayInvariantFactors` separately removes unit factors for
human-facing output.
-/

namespace NormalForms.RationalCanonical

open Polynomial
open scoped Matrix

public abbrev EndomorphismModule {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :=
  Module.AEval' A.toLin'

noncomputable def evaluationMap
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    (Fin n → Rat[X]) →ₗ[Rat[X]] EndomorphismModule A :=
  (Pi.basisFun Rat[X] (Fin n)).constr Rat[X] fun i =>
    Module.AEval'.of A.toLin'
      (Pi.single i 1)

@[simp]
theorem evaluationMap_apply
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (v : Fin n → Rat[X]) :
    evaluationMap A v =
      ∑ i, v i •
        Module.AEval'.of A.toLin' (Pi.single i 1) := by
  exact (Pi.basisFun Rat[X] (Fin n)).constr_apply_fintype
    Rat[X] _ v

public abbrev endomorphismPresentation
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    FiniteFreePresentation Rat[X] where
  numGenerators := n
  numRelations := n
  relationMatrix := endomorphismPresentationMatrix A

private theorem evaluationMap_column
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (j : Fin n) :
    evaluationMap A
        ((endomorphismPresentationMatrix A).mulVec
          (Pi.single j 1)) =
      0 := by
  classical
  rw [Matrix.mulVec_single_one]
  rw [evaluationMap_apply]
  apply (Module.AEval'.of A.toLin').symm.injective
  simp only [map_sum, Module.AEval.of_symm_smul, map_zero]
  simp only [LinearEquiv.symm_apply_apply]
  funext k
  simp only [Finset.sum_apply]
  simp only [Module.End.smul_def]
  have hterm (c : Fin n) :
      ((aeval A.toLin')
          ((endomorphismPresentationMatrix A).col j c)
          (Pi.single c 1)) k =
        if c = j then
          A k j - (if k = j then A j j else 0)
        else if k = c then -A c j else 0 := by
    by_cases hc : c = j
    · subst c
      simp [endomorphismPresentationMatrix_apply_eq,
        Matrix.toLin'_apply]
      by_cases hk : k = j <;> simp [hk]
    · simp [Matrix.col_apply, hc]
      by_cases hk : k = c <;> simp [hk]
  simp_rw [hterm]
  by_cases hk : k = j
  · subst k
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = j
    · simp [hx]
    · simp [hx, Ne.symm hx]
  · simp only [hk, if_false, sub_zero, Pi.zero_apply]
    let f : Fin n → Rat := fun x =>
        if x = j then A k j
        else if k = x then -A x j else 0
    change ∑ x, f x = 0
    have hrest :
        ∑ x ∈ Finset.univ.erase j, f x = f k := by
      apply Finset.sum_eq_single k
      · intro b hb hbk
        have hbj : b ≠ j := (Finset.mem_erase.mp hb).1
        have hkb : k ≠ b := fun h => hbk h.symm
        simp [f, hbj, hkb]
      · intro hnot
        exact False.elim (hnot (by simp [hk]))
    calc
      ∑ x, f x =
          (∑ x ∈ Finset.univ.erase j, f x) + f j :=
        (Finset.sum_erase_add Finset.univ f
          (Finset.mem_univ j)).symm
      _ = f k + f j := by rw [hrest]
      _ = 0 := by simp [f, hk]

private theorem evaluationMap_comp_relationMap_eq_zero
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    (evaluationMap A).comp
        (endomorphismPresentation A).relationMap =
      0 := by
  apply (Pi.basisFun Rat[X] (Fin n)).ext
  intro j
  change
    evaluationMap A
        ((endomorphismPresentationMatrix A).mulVec
          ((Pi.basisFun Rat[X] (Fin n)) j)) =
      0
  rw [Pi.basisFun_apply]
  exact evaluationMap_column A j

noncomputable def presentationToAEval
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    (endomorphismPresentation A).presentedModule →ₗ[Rat[X]]
      EndomorphismModule A :=
  (endomorphismPresentation A).relationSubmodule.liftQ
    (evaluationMap A) (by
      rintro _ ⟨v, rfl⟩
      change
        evaluationMap A
            ((endomorphismPresentation A).relationMap v) =
          0
      have h := LinearMap.congr_fun
        (evaluationMap_comp_relationMap_eq_zero A) v
      change
        evaluationMap A
            ((endomorphismPresentation A).relationMap v) =
          0 at h
      exact h)

@[simp]
theorem presentationToAEval_mk
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (v : Fin n → Rat[X]) :
    presentationToAEval A
        (Submodule.Quotient.mk v) =
      evaluationMap A v :=
  rfl

noncomputable def constantVectorMap
    {n : Nat} :
    (Fin n → Rat) →ₗ[Rat] (Fin n → Rat[X]) where
  toFun v i := C (v i)
  map_add' x y := by
    ext i
    simp
  map_smul' r x := by
    ext i
    simp [Algebra.smul_def]

@[simp]
theorem constantVectorMap_apply
    {n : Nat}
    (v : Fin n → Rat)
    (i : Fin n) :
    constantVectorMap v i = C (v i) :=
  rfl

private theorem relationMap_constantVector
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (v : Fin n → Rat) :
    (endomorphismPresentation A).relationMap
        (constantVectorMap v) =
      fun i =>
        X * C (v i) -
          C (A.mulVec v i) := by
  change
    (endomorphismPresentationMatrix A).mulVec
        (constantVectorMap v) =
      fun i =>
        X * C (v i) -
          C (A.mulVec v i)
  funext i
  change
    ∑ j, endomorphismPresentationMatrix A i j * C (v j) =
      X * C (v i) - C (∑ j, A i j * v j)
  rw [endomorphismPresentationMatrix_eq_charmatrix]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [map_sum, map_mul]
  simp

noncomputable def constantQuotientMap
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    (Fin n → Rat) →ₗ[Rat]
      (endomorphismPresentation A).presentedModule :=
  (((endomorphismPresentation A).relationSubmodule.mkQ).restrictScalars
    Rat).comp constantVectorMap

private theorem constantQuotientMap_X
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (v : Fin n → Rat) :
    constantQuotientMap A (A.toLin' v) =
      (X : Rat[X]) • constantQuotientMap A v := by
  change
    Submodule.Quotient.mk (constantVectorMap (A.mulVec v)) =
      Submodule.Quotient.mk
        ((X : Rat[X]) • constantVectorMap v)
  apply
    ((Submodule.Quotient.eq
      (endomorphismPresentation A).relationSubmodule)).mpr
  change
    constantVectorMap (A.mulVec v) -
        (X : Rat[X]) • constantVectorMap v ∈
      (endomorphismPresentation A).relationSubmodule
  refine ⟨-constantVectorMap v, ?_⟩
  rw [map_neg, relationMap_constantVector]
  funext i
  simp [constantVectorMap]

noncomputable def aEvalToPresentation
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    EndomorphismModule A →ₗ[Rat[X]]
      (endomorphismPresentation A).presentedModule :=
  LinearMap.ofAEval A.toLin' (constantQuotientMap A)
    (constantQuotientMap_X A)

@[simp]
theorem aEvalToPresentation_of
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (v : Fin n → Rat) :
    aEvalToPresentation A
        (Module.AEval'.of A.toLin' v) =
      Submodule.Quotient.mk (constantVectorMap v) :=
  rfl

private theorem presentationToAEval_constant
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (v : Fin n → Rat) :
    presentationToAEval A
        (Submodule.Quotient.mk (constantVectorMap v)) =
      Module.AEval'.of A.toLin' v := by
  rw [presentationToAEval_mk, evaluationMap_apply]
  apply (Module.AEval'.of A.toLin').symm.injective
  simp only [map_sum, Module.AEval.of_symm_smul,
    LinearEquiv.symm_apply_apply]
  simp only [constantVectorMap_apply, aeval_C]
  change ∑ x, v x • Pi.single x 1 = v
  simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
    (Pi.basisFun Rat (Fin n)).sum_repr v

private theorem presentationToAEval_aEvalToPresentation
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (x : EndomorphismModule A) :
    presentationToAEval A (aEvalToPresentation A x) = x := by
  rw [← (Module.AEval'.of A.toLin').apply_symm_apply x]
  rw [aEvalToPresentation_of, presentationToAEval_constant]

private theorem aEvalToPresentation_presentationToAEval
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (x : (endomorphismPresentation A).presentedModule) :
    aEvalToPresentation A (presentationToAEval A x) = x := by
  classical
  induction x using Submodule.Quotient.induction_on with
  | _ v =>
      rw [presentationToAEval_mk, evaluationMap_apply, map_sum]
      simp_rw [map_smul, aEvalToPresentation_of]
      have hv :
          (∑ x, v x • constantVectorMap (Pi.single x 1)) = v := by
        have hconstant (x : Fin n) :
            constantVectorMap (Pi.single x 1) =
              (Pi.single x 1 : Fin n → Rat[X]) := by
          ext k
          by_cases h : x = k <;>
            simp [constantVectorMap, h]
        simp_rw [hconstant]
        simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
          (Pi.basisFun Rat[X] (Fin n)).sum_repr v
      calc
        ∑ x, v x •
              Submodule.Quotient.mk
                (constantVectorMap (Pi.single x 1)) =
            (endomorphismPresentation A).relationSubmodule.mkQ
              (∑ x, v x •
                constantVectorMap (Pi.single x 1)) := by
          simp
        _ = Submodule.Quotient.mk v := by
          rw [hv]
          rfl

/--
The cokernel presentation by `XI - A` is the polynomial module induced by
the endomorphism `A`.
-/
public noncomputable def endomorphismPresentationEquivAEval
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    (endomorphismPresentation A).presentedModule ≃ₗ[Rat[X]]
      EndomorphismModule A where
  toFun := presentationToAEval A
  invFun := aEvalToPresentation A
  map_add' x y := by simp
  map_smul' p x := by simp
  left_inv := aEvalToPresentation_presentationToAEval A
  right_inv := presentationToAEval_aEvalToPresentation A

/--
Human-facing invariant factors.  Unit factors are omitted because their
cyclic quotients are zero; theorem-facing decompositions retain them.
-/
public noncomputable def endomorphismDisplayInvariantFactors
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    List Rat[X] :=
  FiniteFreePresentation.displayFactors
    (endomorphismInvariantFactors A)

@[simp]
public theorem mem_endomorphismDisplayInvariantFactors
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat)
    (factor : Rat[X]) :
    factor ∈ endomorphismDisplayInvariantFactors A ↔
      factor ∈ endomorphismInvariantFactors A ∧
        ¬ IsUnit factor := by
  exact FiniteFreePresentation.mem_displayFactors _ _

/--
The cyclic Smith decomposition of the polynomial module induced by `A`.

Every diagonal Smith entry is retained, including units.  Thus a unit factor
appears as a zero quotient module instead of being silently discarded.
-/
public noncomputable def endomorphismCyclicDecomposition
    {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    EndomorphismModule A ≃ₗ[Rat[X]]
      ((i : Fin n) →
        Rat[X] ⧸
          Ideal.span
            ({endomorphismInvariantFactor A i} :
              Set Rat[X])) := by
  let quotientEquiv :
      (endomorphismPresentation A).presentedModule ≃ₗ[Rat[X]]
        ((i : Fin n) →
          Rat[X] ⧸
            Ideal.span
              ({(endomorphismSmithResult A).S i i} :
                Set Rat[X])) := by
    exact
      (NormalForms.Bridge.MathlibPID.quotientEquivPiSpanOfResultFin
        (endomorphismPresentationMatrix A)
        (endomorphismSmithResult A))
  let factorEquiv :
      ((i : Fin n) →
          Rat[X] ⧸
            Ideal.span
              ({(endomorphismSmithResult A).S i i} :
                Set Rat[X])) ≃ₗ[Rat[X]]
        ((i : Fin n) →
          Rat[X] ⧸
            Ideal.span
              ({endomorphismInvariantFactor A i} :
                Set Rat[X])) :=
    LinearEquiv.piCongrRight fun i =>
      Submodule.quotEquivOfEq _ _ (by
        rw [endomorphismSmithResult_diagonal])
  exact ((endomorphismPresentationEquivAEval A).symm.trans
    quotientEquiv).trans factorEquiv

end NormalForms.RationalCanonical
