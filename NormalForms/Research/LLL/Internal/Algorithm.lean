/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.Result
public import NormalForms.Matrix.Elementary.Basic

/-!
# Fuelled exact LLL transition system

This module is intentionally internal.  It implements the exact transition
system and maintains the strong transform invariant at every row operation.
The public full-rank entry point is defined in `FullRank`.
-/

namespace NormalForms.Research.LLL.Internal

@[expose] public section

open scoped Matrix
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Research.LLL

def rowSwapCertificate {m : Nat} (left right : Fin m) :
    MatrixInverseCertificate
      (rowOperationMatrix (.swap left right : RowOperation Int (Fin m))) := by
  let elementary :=
    rowOperationMatrix (.swap left right : RowOperation Int (Fin m))
  have selfInverse : elementary * elementary = 1 := by
    rw [rowOperationMatrix_mul]
    ext row column
    by_cases equal : left = right
    · subst right
      by_cases atLeft : row = left
      · subst row
        simp [elementary, rowOperationMatrix, applyRowOperation]
      · simp [elementary, rowOperationMatrix, applyRowOperation, atLeft]
    · by_cases atLeft : row = left
      · subst row
        have rightNotLeft : right ≠ left := fun h => equal h.symm
        simp [elementary, rowOperationMatrix, applyRowOperation, rightNotLeft]
      · by_cases atRight : row = right
        · subst row
          simp [elementary, rowOperationMatrix, applyRowOperation, atLeft]
        · simp [elementary, rowOperationMatrix, applyRowOperation, atLeft, atRight]
  exact
    { inverse := elementary
      left_inv := selfInverse
      right_inv := selfInverse }

def rowAddCertificate {m : Nat} (source target : Fin m)
    (coefficient : Int) (distinct : source ≠ target) :
    MatrixInverseCertificate
      (rowOperationMatrix (.add source target coefficient : RowOperation Int (Fin m))) := by
  let forward :=
    rowOperationMatrix (.add source target coefficient : RowOperation Int (Fin m))
  let backward :=
    rowOperationMatrix (.add source target (-coefficient) : RowOperation Int (Fin m))
  have backwardForward : backward * forward = 1 := by
    rw [rowOperationMatrix_mul]
    ext row column
    by_cases atTarget : row = target
    · subst row
      simp [forward, applyRowOperation, rowOperationMatrix, distinct]
    · simp [forward, applyRowOperation, rowOperationMatrix, atTarget]
  have forwardBackward : forward * backward = 1 := by
    rw [rowOperationMatrix_mul]
    ext row column
    by_cases atTarget : row = target
    · subst row
      simp [backward, applyRowOperation, rowOperationMatrix, distinct]
    · simp [backward, applyRowOperation, rowOperationMatrix, atTarget]
  exact
    { inverse := backward
      left_inv := backwardForward
      right_inv := forwardBackward }

structure OperationCount where
  sizeReductions : Nat := 0
  swaps : Nat := 0
  gramSchmidtRefreshes : Nat := 0
  deriving DecidableEq, Repr

namespace OperationCount

def total (count : OperationCount) : Nat :=
  count.sizeReductions + count.swaps + count.gramSchmidtRefreshes

def addSizeReduction (count : OperationCount) : OperationCount :=
  { count with
    sizeReductions := count.sizeReductions + 1
    gramSchmidtRefreshes := count.gramSchmidtRefreshes + 1 }

def addSwap (count : OperationCount) : OperationCount :=
  { count with
    swaps := count.swaps + 1
    gramSchmidtRefreshes := count.gramSchmidtRefreshes + 1 }

end OperationCount

structure State {m n : Nat} (input : Matrix (Fin m) (Fin n) Int) where
  transform : Matrix (Fin m) (Fin m) Int
  transformCert : MatrixInverseCertificate transform
  basis : Matrix (Fin m) (Fin n) Int
  equation : transform * input = basis
  index : Nat
  operations : OperationCount

def State.initial {m n : Nat} (input : Matrix (Fin m) (Fin n) Int) : State input :=
  { transform := 1
    transformCert := MatrixInverseCertificate.one
    basis := input
    equation := NormalForms.Matrix.Constructive.one_mul input
    index := 1
    operations := {} }

def State.withIndex {m n : Nat} {input : Matrix (Fin m) (Fin n) Int}
    (state : State input) (index : Nat) : State input :=
  { state with index }

def State.addRow {m n : Nat} {input : Matrix (Fin m) (Fin n) Int}
    (state : State input) (source target : Fin m) (coefficient : Int)
    (distinct : source ≠ target) : State input := by
  let elementary :=
    rowOperationMatrix (.add source target coefficient : RowOperation Int (Fin m))
  let certificate := rowAddCertificate source target coefficient distinct
  let nextBasis := applyRowOperation state.basis (.add source target coefficient)
  exact
    { transform := elementary * state.transform
      transformCert := certificate.mul state.transformCert
      basis := nextBasis
      equation := by
        calc
          (elementary * state.transform) * input =
              elementary * (state.transform * input) := by
                rw [NormalForms.Matrix.Constructive.mul_assoc]
          _ = elementary * state.basis := by rw [state.equation]
          _ = nextBasis := rowOperationMatrix_mul state.basis _
      index := state.index
      operations := state.operations.addSizeReduction }

def State.swapRows {m n : Nat} {input : Matrix (Fin m) (Fin n) Int}
    (state : State input) (left right : Fin m) : State input := by
  let elementary :=
    rowOperationMatrix (.swap left right : RowOperation Int (Fin m))
  let certificate := rowSwapCertificate left right
  let nextBasis := applyRowOperation state.basis (.swap left right)
  exact
    { transform := elementary * state.transform
      transformCert := certificate.mul state.transformCert
      basis := nextBasis
      equation := by
        calc
          (elementary * state.transform) * input =
              elementary * (state.transform * input) := by
                rw [NormalForms.Matrix.Constructive.mul_assoc]
          _ = elementary * state.basis := by rw [state.equation]
          _ = nextBasis := rowOperationMatrix_mul state.basis _
      index := state.index
      operations := state.operations.addSwap }

def reduceCoefficient {m n : Nat} {input : Matrix (Fin m) (Fin n) Int}
    (state : State input) (row column : Fin m) (less : column < row) : State input :=
  let coefficient :=
    -nearestInteger (gramSchmidtCoefficient state.basis row column)
  if _hzero : coefficient = 0 then
    state
  else
    state.addRow column row coefficient (Fin.ne_of_lt less)

def sizeReduceRowAux {m n : Nat} {input : Matrix (Fin m) (Fin n) Int}
    (row : Fin m) : Nat -> State input -> State input
  | 0, state => state
  | remaining + 1, state =>
      if hremaining : remaining < row.1 then
        let column : Fin m :=
          ⟨remaining, Nat.lt_trans hremaining row.2⟩
        sizeReduceRowAux row remaining
          (reduceCoefficient state row column hremaining)
      else
        sizeReduceRowAux row remaining state

def sizeReduceRow {m n : Nat} {input : Matrix (Fin m) (Fin n) Int}
    (state : State input) (row : Fin m) : State input :=
  sizeReduceRowAux row row.1 state

def previousIndex {m : Nat} (row : Fin m) : Fin m :=
  ⟨row.1 - 1, Nat.lt_of_le_of_lt (Nat.sub_le row.1 1) row.2⟩

def lovaszAt {m n : Nat} (basis : Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (_positive : 0 < row.1) : Bool :=
  let previous := previousIndex row
  decide
    (delta * gramSchmidtNormSq basis previous <=
      gramSchmidtNormSq basis row +
        (gramSchmidtCoefficient basis row previous) ^ 2 *
          gramSchmidtNormSq basis previous)

inductive Status where
  | complete
  | exhausted
  deriving DecidableEq, Repr

structure Run {m n : Nat} (input : Matrix (Fin m) (Fin n) Int) where
  status : Status
  state : State input

def loop {m n : Nat} {input : Matrix (Fin m) (Fin n) Int} :
    Nat -> State input -> Run input
  | 0, state => { status := .exhausted, state }
  | fuel + 1, state =>
      if hdone : m <= state.index then
        { status := .complete, state }
      else
        have hindex : state.index < m := Nat.lt_of_not_ge hdone
        if hzero : state.index = 0 then
          loop fuel (state.withIndex 1)
        else
          let row : Fin m := ⟨state.index, hindex⟩
          let reduced := sizeReduceRow state row
          if lovaszAt reduced.basis row (Nat.zero_lt_of_ne_zero hzero) then
            loop fuel (reduced.withIndex (state.index + 1))
          else
            let previous := previousIndex row
            let swapped := reduced.swapRows previous row
            loop fuel (swapped.withIndex (Nat.max 1 (state.index - 1)))

def run {m n : Nat} (basis : Matrix (Fin m) (Fin n) Int) (fuel : Nat) : Run basis :=
  loop fuel (State.initial basis)

def certify? {m n : Nat} {input : Matrix (Fin m) (Fin n) Int}
    (run : Run input) : Option (FullRankLLLResult input) :=
  if _hstatus : run.status = .complete then
    if hreduced : isLLLReducedB run.state.basis = true then
      some
        { U := run.state.transform
          U_cert := run.state.transformCert
          reducedBasis := run.state.basis
          equation := run.state.equation
          reduced := isLLLReducedB_sound run.state.basis hreduced }
    else
      none
  else
    none

/-- Compiled implementation of the public fuelled diagnostic entry. -/
def publicFuelledRun {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) (fuel : Nat) : FuelledLLLRun basis :=
  let raw := run basis fuel
  let operations := raw.state.operations
  { complete := decide (raw.status = .complete)
    iterations := fuel
    operations :=
      { sizeReductions := operations.sizeReductions
        swaps := operations.swaps
        gramSchmidtRefreshes := operations.gramSchmidtRefreshes }
    candidate := raw.state.basis
    certified := certify? raw }

end

end NormalForms.Research.LLL.Internal
