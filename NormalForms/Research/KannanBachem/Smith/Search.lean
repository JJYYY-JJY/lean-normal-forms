/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.PassCorrectness
public import NormalForms.Matrix.Elementary.Basic
import all NormalForms.Matrix.Certificates.Basic

/-!
# Executable Smith Pass Searches

All control-flow decisions use `ComputableEuclideanOps.isZeroB` or
`ComputableEuclideanOps.dvdB`.  The accompanying lemmas expose their exact
propositional meaning for the stabilization proof.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Hermite

/-- First structurally nonzero entry, using the executable integer zero test. -/
@[expose] public def firstNonzeroIndex? : {n : Nat} →
    (Fin n → Int) → Option (Fin n)
  | 0, _ => none
  | _ + 1, entries =>
      if ComputableEuclideanOps.isZeroB (entries 0) = true then
        Option.map Fin.succ (firstNonzeroIndex? fun i => entries i.succ)
      else
        some 0

@[simp] public theorem firstNonzeroIndex?_eq_firstNonzero? :
    {n : Nat} → (entries : Fin n → Int) →
      firstNonzeroIndex? entries = firstNonzero? entries
  | 0, _ => rfl
  | _ + 1, entries => by
      by_cases hzero : entries 0 = 0
      · simp [firstNonzeroIndex?, firstNonzero?, hzero,
          firstNonzeroIndex?_eq_firstNonzero?]
      · have hbool : ComputableEuclideanOps.isZeroB (entries 0) ≠ true :=
          fun h => hzero ((ComputableEuclideanOps.isZeroB_eq_true_iff _).1 h)
        simp [firstNonzeroIndex?, firstNonzero?, hzero, hbool]

/-- First nonzero entry below the active pivot. -/
@[expose] public def firstNonzeroBelow? {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    Option (Fin n) :=
  firstNonzeroIndex? fun row => A row.succ 0

public theorem firstNonzeroBelow?_eq_none {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hnone : firstNonzeroBelow? A = none) :
    FirstColumnCleared A := by
  rw [firstNonzeroBelow?, firstNonzeroIndex?_eq_firstNonzero?] at hnone
  exact firstNonzero?_eq_none (fun row : Fin n => A row.succ 0) hnone

public theorem firstNonzeroBelow?_some_ne_zero {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    {row : Fin n} (hsome : firstNonzeroBelow? A = some row) :
    A row.succ 0 ≠ 0 := by
  rw [firstNonzeroBelow?, firstNonzeroIndex?_eq_firstNonzero?] at hsome
  exact firstNonzero?_some_ne_zero (fun index : Fin n => A index.succ 0)
    hsome

/-- First entry not divisible by a supplied pivot. -/
@[expose] public def firstUndivisibleIndex? : {n : Nat} →
    Int → (Fin n → Int) → Option (Fin n)
  | 0, _, _ => none
  | _ + 1, pivot, entries =>
      if ComputableEuclideanOps.dvdB pivot (entries 0) = true then
        Option.map Fin.succ
          (firstUndivisibleIndex? pivot fun i => entries i.succ)
      else
        some 0

public theorem firstUndivisibleIndex?_eq_none :
    {n : Nat} → (pivot : Int) → (entries : Fin n → Int) →
      firstUndivisibleIndex? pivot entries = none →
        ∀ i : Fin n, pivot ∣ entries i
  | 0, _, _, _, i => Fin.elim0 i
  | _ + 1, pivot, entries, hnone, i => by
      by_cases hdiv :
          ComputableEuclideanOps.dvdB pivot (entries 0) = true
      · have htail :
            firstUndivisibleIndex? pivot (fun j => entries j.succ) = none := by
          simpa [firstUndivisibleIndex?, hdiv] using hnone
        cases i using Fin.cases with
        | zero =>
            exact (ComputableEuclideanOps.dvdB_eq_true_iff _ _).1 hdiv
        | succ i =>
            exact firstUndivisibleIndex?_eq_none pivot
              (fun j => entries j.succ) htail i
      · have hsome : firstUndivisibleIndex? pivot entries =
            some (0 : Fin (_ + 1)) := by
          simp [firstUndivisibleIndex?, hdiv]
        rw [hnone] at hsome
        cases hsome

public theorem firstUndivisibleIndex?_some_not_dvd :
    {n : Nat} → (pivot : Int) → (entries : Fin n → Int) →
      {i : Fin n} → firstUndivisibleIndex? pivot entries = some i →
        ¬ pivot ∣ entries i
  | 0, _, _, i, _ => Fin.elim0 i
  | _ + 1, pivot, entries, i, hsome => by
      by_cases hdiv :
          ComputableEuclideanOps.dvdB pivot (entries 0) = true
      · rw [firstUndivisibleIndex?, hdiv] at hsome
        cases i using Fin.cases with
        | zero =>
            cases htail :
                firstUndivisibleIndex? pivot (fun j => entries j.succ) <;>
              simp [htail] at hsome
        | succ i =>
            cases htail :
                firstUndivisibleIndex? pivot (fun j => entries j.succ) with
            | none => simp [htail] at hsome
            | some j =>
                have hji : j = i := by simpa [htail] using hsome
                subst j
                exact firstUndivisibleIndex?_some_not_dvd pivot
                  (fun j => entries j.succ) htail
      · have hnot : ¬ pivot ∣ entries 0 :=
          fun hdvd => hdiv
            ((ComputableEuclideanOps.dvdB_eq_true_iff _ _).2 hdvd)
        have hzero : firstUndivisibleIndex? pivot entries =
            some (0 : Fin (_ + 1)) := by
          simp [firstUndivisibleIndex?, hdiv]
        have hi : (0 : Fin (_ + 1)) = i :=
          Option.some.inj (hzero.symm.trans hsome)
        subst i
        exact hnot

/-- First below-pivot entry not divisible by the active pivot. -/
@[expose] public def firstUndivisibleBelow? {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    Option (Fin n) :=
  firstUndivisibleIndex? (A 0 0) fun row => A row.succ 0

public theorem firstUndivisibleBelow?_eq_none {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hnone : firstUndivisibleBelow? A = none) :
    ∀ row : Fin n, A 0 0 ∣ A row.succ 0 :=
  firstUndivisibleIndex?_eq_none (A 0 0)
    (fun row => A row.succ 0) hnone

public theorem firstUndivisibleBelow?_some_not_dvd {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    {row : Fin n} (hsome : firstUndivisibleBelow? A = some row) :
    ¬ A 0 0 ∣ A row.succ 0 :=
  firstUndivisibleIndex?_some_not_dvd (A 0 0)
    (fun index => A index.succ 0) hsome

/-- Row-major first entry of a rectangular block not divisible by `pivot`. -/
@[expose] public def firstUndivisibleMatrix? : {m n : Nat} →
    Int → (Fin m → Fin n → Int) → Option (Fin m × Fin n)
  | 0, _, _, _ => none
  | _ + 1, _n, pivot, entries =>
      match firstUndivisibleIndex? pivot (entries 0) with
      | some column => some (0, column)
      | none =>
          Option.map (fun position => (position.1.succ, position.2))
            (firstUndivisibleMatrix? pivot fun row => entries row.succ)

public theorem firstUndivisibleMatrix?_eq_none :
    {m n : Nat} → (pivot : Int) → (entries : Fin m → Fin n → Int) →
      firstUndivisibleMatrix? pivot entries = none →
        ∀ row column, pivot ∣ entries row column
  | 0, _, _, _, _, row, _ => Fin.elim0 row
  | _ + 1, n, pivot, entries, hnone, row, column => by
      cases hrow : firstUndivisibleIndex? pivot (entries 0) with
      | some witness =>
          simp [firstUndivisibleMatrix?, hrow] at hnone
      | none =>
          have htail : firstUndivisibleMatrix? pivot
              (fun row => entries row.succ) = none := by
            simpa [firstUndivisibleMatrix?, hrow] using hnone
          cases row using Fin.cases with
          | zero =>
              exact firstUndivisibleIndex?_eq_none pivot (entries 0)
                hrow column
          | succ row =>
              exact firstUndivisibleMatrix?_eq_none pivot
                (fun row => entries row.succ) htail row column

public theorem firstUndivisibleMatrix?_some_not_dvd :
    {m n : Nat} → (pivot : Int) → (entries : Fin m → Fin n → Int) →
      {position : Fin m × Fin n} →
        firstUndivisibleMatrix? pivot entries = some position →
          ¬ pivot ∣ entries position.1 position.2
  | 0, _, _, _, position, _ => Fin.elim0 position.1
  | _ + 1, n, pivot, entries, position, hsome => by
      cases hrow : firstUndivisibleIndex? pivot (entries 0) with
      | some column =>
          have positionEq : position = (0, column) := by
            simpa [firstUndivisibleMatrix?, hrow] using hsome.symm
          subst position
          exact firstUndivisibleIndex?_some_not_dvd pivot (entries 0) hrow
      | none =>
          cases htail : firstUndivisibleMatrix? pivot
              (fun row => entries row.succ) with
          | none => simp [firstUndivisibleMatrix?, hrow, htail] at hsome
          | some tailPosition =>
              have positionEq : position =
                  (tailPosition.1.succ, tailPosition.2) := by
                simpa [firstUndivisibleMatrix?, hrow, htail] using hsome.symm
              subst position
              exact firstUndivisibleMatrix?_some_not_dvd pivot
                (fun row => entries row.succ) htail

/-- First lower-right entry not divisible by the active pivot. -/
@[expose] public def firstUndivisibleLower? {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    Option (Fin n × Fin n) :=
  firstUndivisibleMatrix? (A 0 0) fun row column =>
    A row.succ column.succ

public theorem firstUndivisibleLower?_eq_none {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hnone : firstUndivisibleLower? A = none) :
    PivotDividesLower A :=
  firstUndivisibleMatrix?_eq_none (A 0 0)
    (fun row column => A row.succ column.succ) hnone

public theorem firstUndivisibleLower?_some_not_dvd {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    {position : Fin n × Fin n}
    (hsome : firstUndivisibleLower? A = some position) :
    ¬ A 0 0 ∣ A position.1.succ position.2.succ :=
  firstUndivisibleMatrix?_some_not_dvd (A 0 0)
    (fun row column => A row.succ column.succ) hsome

/-- Explicit inverse for a Smith-schedule column addition. -/
@[expose] public def columnAddCertificate {n : Nat}
    (source destination : Fin n) (coefficient : Int)
    (hne : source ≠ destination) :
    MatrixInverseCertificate
      (columnOperationMatrix (.add source destination coefficient)) :=
  { inverse :=
      columnOperationMatrix (.add source destination (-coefficient))
    left_inv := by
      rw [mul_columnOperationMatrix]
      ext row column
      by_cases hcolumn : column = destination
      · subst column
        simp [applyColumnOperation, columnOperationMatrix, hne]
      · simp [applyColumnOperation, columnOperationMatrix, hcolumn]
    right_inv := by
      rw [mul_columnOperationMatrix]
      ext row column
      by_cases hcolumn : column = destination
      · subst column
        simp [applyColumnOperation, columnOperationMatrix, hne]
      · simp [applyColumnOperation, columnOperationMatrix, hcolumn] }

/-- Step 7: add one offending lower-right column into the pivot column. -/
@[expose] public def injectLowerWitness {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (column : Fin n) : TwoSidedCertificate A :=
  { U := 1
    U_cert := MatrixInverseCertificate.one
    result := applyColumnOperation A (.add column.succ 0 1)
    V := columnOperationMatrix (.add column.succ 0 1)
    V_cert := columnAddCertificate column.succ 0 1 (by simp)
    equation := by
      rw [_root_.Matrix.one_mul, mul_columnOperationMatrix] }

/-- The injected first-column witness is exactly the offending block entry. -/
public theorem injectLowerWitness_target {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (row column : Fin n) (hcleared : FirstColumnCleared A) :
    (injectLowerWitness A column).result row.succ 0 =
      A row.succ column.succ := by
  simp [injectLowerWitness, applyColumnOperation, hcleared row]

end NormalForms.Research.KannanBachem.Smith
