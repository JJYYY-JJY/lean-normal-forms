/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalCorrectness
public import NormalForms.Research.KannanBachem.Hermite.Semantics
import all NormalForms.Matrix.Hermite.Uniqueness

/-!
# Proof-Producing Check for Principal-Minor HNF Runs

The principal-minor transition system is executable before its total
correctness proof is complete.  This module closes the trust chain for every
successful run: recursive recognition constructs the project HNF predicate,
and success returns the existing strong `HNFResultFin` with the trace's
explicit inverse certificate.  Failure is not silently replaced by the
reference algorithm.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite

/-- A principal-minor candidate failed independent HNF recognition. -/
public inductive PrincipalCheckError where
  | notHermite
  deriving DecidableEq, Repr

namespace PrincipalRecognition

def reducedRowDecidable {m n : Nat}
    (A : _root_.Matrix (Fin (m + 1)) (Fin (n + 1)) Int) (i : Fin m) :
    Decidable
      (match firstNonzero? (fun j : Fin n => A i.succ j.succ) with
      | none => True
      | some j => A 0 j.succ = A 0 j.succ % A i.succ j.succ) := by
  cases hFirst : firstNonzero? (fun j : Fin n => A i.succ j.succ) with
  | none => exact isTrue trivial
  | some _ => exact inferInstance

/-- Proof-producing recognition, local to the research checker. -/
@[expose] public def hermiteProof? :
    {m n : Nat} → (A : _root_.Matrix (Fin m) (Fin n) Int) →
      Option (PLift (IsHermiteNormalFormFin A))
  | 0, _, A => some ⟨.emptyRows A⟩
  | _ + 1, 0, A => some ⟨.emptyCols A⟩
  | m + 1, n + 1, A =>
      if hzero : ∀ i, A i 0 = 0 then
        match hermiteProof? (tailCols A) with
        | none => none
        | some ⟨hTail⟩ => some ⟨.zeroCol A hzero hTail⟩
      else if hpivot : A 0 0 ≠ 0 then
        if hnorm : A 0 0 = normalize (A 0 0) then
          if hbelow : ∀ i : Fin m, A i.succ 0 = 0 then
            match hermiteProof? (lowerRight A) with
            | none => none
            | some ⟨hLower⟩ =>
                letI (i : Fin m) := reducedRowDecidable A i
                if hreduced : ∀ i : Fin m,
                    match firstNonzero? (fun j : Fin n => A i.succ j.succ) with
                    | none => True
                    | some j =>
                        A 0 j.succ = A 0 j.succ % A i.succ j.succ then
                  some ⟨.pivot A hpivot hnorm hbelow hLower hreduced⟩
                else
                  none
          else
            none
        else
          none
      else
        none
termination_by m n _ => m + n
decreasing_by
  · exact Nat.add_lt_add_left (Nat.lt_succ_self n) (m + 1)
  · exact Nat.add_lt_add (Nat.lt_succ_self m) (Nat.lt_succ_self n)

private theorem hermiteProof?_emptyCols_isSome :
    (m : Nat) → (A : _root_.Matrix (Fin m) (Fin 0) Int) →
      ∃ proof, hermiteProof? A = some proof
  | 0, A => ⟨⟨.emptyRows A⟩, by rw [hermiteProof?]⟩
  | _ + 1, A => ⟨⟨.emptyCols A⟩, by rw [hermiteProof?]⟩

/-- Recognition is complete for the project HNF predicate. -/
public theorem hermiteProof?_isSome {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (hA : IsHermiteNormalFormFin A) :
    ∃ proof, hermiteProof? A = some proof := by
  induction hA with
  | emptyRows A =>
      exact ⟨⟨.emptyRows A⟩, by simp [hermiteProof?]⟩
  | emptyCols A =>
      exact hermiteProof?_emptyCols_isSome _ A
  | @zeroCol m n A hzero hTail ih =>
      rcases ih with ⟨proof, hproof⟩
      cases proof with
      | up tailProof =>
          exact ⟨⟨.zeroCol A hzero tailProof⟩, by
            rw [hermiteProof?]
            rw [dif_pos hzero, hproof]⟩
  | @pivot m n A hpivot hnorm hbelow hLower hreduced ih =>
      have notZeroColumn : ¬∀ i, A i 0 = 0 := by
        intro hzero
        exact hpivot (hzero 0)
      rcases ih with ⟨proof, hproof⟩
      cases proof with
      | up lowerProof =>
          exact ⟨⟨.pivot A hpivot hnorm hbelow lowerProof hreduced⟩, by
            rw [hermiteProof?]
            rw [dif_neg notZeroColumn, dif_pos hpivot, dif_pos hnorm,
              dif_pos hbelow, hproof]
            simp only
            split
            · rfl
            · rename_i hnot
              exact (hnot hreduced).elim⟩

end PrincipalRecognition

/--
Check one principal-minor run and, on success, return the existing strong HNF
result.  No fallback algorithm is invoked on failure.
-/
@[expose] public def checkPrincipalRun {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    Except PrincipalCheckError (HNFResultFin A) :=
  let run := principalRun A
  match PrincipalRecognition.hermiteProof? run.matrix with
  | none => .error .notHermite
  | some ⟨isHermite⟩ =>
      .ok
        { U := run.steps.accumulator
          U_cert := run.steps.accumulatorCertificate
          H := run.matrix
          equation := run.equation
          isHermite }

/-- Successful checking identifies the strong result with the candidate run. -/
public theorem checkPrincipalRun_result {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    {result : HNFResultFin A}
    (success : checkPrincipalRun A = .ok result) :
    result.H = (principalRun A).matrix ∧
      result.U = (principalRun A).steps.accumulator ∧
      result.U_cert.inverse = (principalRun A).steps.inverseAccumulator := by
  unfold checkPrincipalRun at success
  dsimp only at success
  generalize hproof :
      PrincipalRecognition.hermiteProof? (principalRun A).matrix = proof at success
  cases proof with
  | none => simp at success
  | some lifted =>
      cases lifted with
      | up isHermite =>
          simp at success
          subst result
          simp [RowTrace.accumulatorCertificate_inverse]

/-- A successful principal run carries the original primitive execution trace. -/
public def checkedPrincipalTrace {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    {result : HNFResultFin A}
    (success : checkPrincipalRun A = .ok result) : ExecutionTrace A result :=
  { steps := (principalRun A).steps
    accumulator_eq := (checkPrincipalRun_result success).2.1.symm
    inverseAccumulator_eq := (checkPrincipalRun_result success).2.2.symm }

public theorem checkedPrincipalTrace_isPrimitive {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    {result : HNFResultFin A}
    (success : checkPrincipalRun A = .ok result) :
    (checkedPrincipalTrace success).steps.IsPrimitive :=
  (principalRun A).primitive

/-- Successful principal-minor output agrees with the frozen canonical HNF. -/
public theorem checkPrincipalRun_eq_reference {n : Nat}
    {A : _root_.Matrix (Fin n) (Fin n) Int}
    {result : HNFResultFin A}
    (_success : checkPrincipalRun A = .ok result) :
    result.H = (semanticReference A).H := by
  let reference := semanticReference A
  let change := reference.U * result.U_cert.inverse
  have changeCert : MatrixInverseCertificate change :=
    reference.U_cert.mul result.U_cert.symm
  apply isHermiteNormalFormFin_unique_of_left_equiv
    result.isHermite reference.isHermite changeCert.unimodular
  calc
    change * result.H =
        reference.U * (result.U_cert.inverse * result.H) := by
      rw [_root_.Matrix.mul_assoc]
    _ = reference.U * A := by
      rw [← result.equation]
      calc
        reference.U * (result.U_cert.inverse * (result.U * A)) =
            reference.U * ((result.U_cert.inverse * result.U) * A) := by
          rw [_root_.Matrix.mul_assoc]
        _ = reference.U * (1 * A) := by rw [result.U_cert.left_inv]
        _ = reference.U * A := by simp
    _ = reference.H := reference.equation

/-- The checker cannot fail on a nonsingular square input. -/
public theorem checkPrincipalRun_isOk_of_det_ne_zero {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    ∃ result, checkPrincipalRun A = .ok result := by
  rcases PrincipalRecognition.hermiteProof?_isSome
      (principalRun_isHermite_of_det_ne_zero A hdet) with ⟨proof, hproof⟩
  unfold checkPrincipalRun
  dsimp only
  rw [hproof]
  cases proof with
  | up isHermite =>
      exact ⟨
        { U := (principalRun A).steps.accumulator
          U_cert := (principalRun A).steps.accumulatorCertificate
          H := (principalRun A).matrix
          equation := (principalRun A).equation
          isHermite }, rfl⟩

/-- Total principal output is the frozen canonical HNF. -/
public theorem principalHermiteNormalForm_eq_reference {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) (hdet : A.det ≠ 0) :
    (principalHermiteNormalForm A hdet).H = (semanticReference A).H := by
  rcases checkPrincipalRun_isOk_of_det_ne_zero A hdet with ⟨result, success⟩
  calc
    (principalHermiteNormalForm A hdet).H = (principalRun A).matrix :=
      principalHermiteNormalForm_H A hdet
    _ = result.H := (checkPrincipalRun_result success).1.symm
    _ = (semanticReference A).H := checkPrincipalRun_eq_reference success

end NormalForms.Research.KannanBachem.Hermite
