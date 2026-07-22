/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Smith.Search

/-!
# Fuelled Kannan--Bachem Pivot Stabilization

This is the bounded diagnostic control loop of Steps 4--7. A successful value
carries the same strong two-sided certificate used by the core API together
with the paper's stable-pivot invariant. Fuel exhaustion returns `none`, and
this module makes no hidden fallback to the generic Smith kernel. The separate
`Smith.Totality` module supplies the primary well-founded total entry point.
-/

public section

namespace NormalForms.Research.KannanBachem.Smith

open scoped Matrix
open NormalForms.Matrix.Certificates

/-- The complete invariant required before the outer Smith recursion advances. -/
public structure StablePivot {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) : Prop where
  pivot_ne_zero : A 0 0 ≠ 0
  pivot_normalized : A 0 0 = _root_.normalize (A 0 0)
  firstRowCleared : FirstRowCleared A
  firstColumnCleared : FirstColumnCleared A
  pivotDividesLower : PivotDividesLower A

/-- A successful fuelled stabilization, with paper-level phase counts. -/
public structure Stabilization {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) where
  certificate : TwoSidedCertificate A
  stable : StablePivot certificate.result
  passes : Nat
  injections : Nat

public theorem stableOfSearches {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (hdet : A.det ≠ 0)
    (hcolumn : firstNonzeroBelow? (pass A hdet).result = none)
    (hdivides : firstUndivisibleLower? (pass A hdet).result = none) :
    StablePivot (pass A hdet).result := by
  obtain ⟨pivotNonzero, pivotNormalized, rowCleared⟩ := pass_shape A hdet
  exact
    { pivot_ne_zero := pivotNonzero
      pivot_normalized := pivotNormalized
      firstRowCleared := rowCleared
      firstColumnCleared := firstNonzeroBelow?_eq_none _ hcolumn
      pivotDividesLower := firstUndivisibleLower?_eq_none _ hdivides }

/--
Run at most `fuel` Step-4/Step-5 passes.  The injection branch is exactly Step
7: add the first offending lower-right column into the pivot column before the
next pass.
-/
@[expose] public def stabilize? {n : Nat} :
    (fuel : Nat) →
      (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) →
        A.det ≠ 0 → Option (Stabilization A)
  | 0, _A, _hdet => none
  | fuel + 1, A, hdet =>
      let current := pass A hdet
      match hcolumn : firstNonzeroBelow? current.result with
      | some _row =>
          match stabilize? fuel current.result
              (pass_result_det_ne_zero A hdet) with
          | none => none
          | some next =>
              some
                { certificate := compose current next.certificate
                  stable := next.stable
                  passes := next.passes + 1
                  injections := next.injections }
      | none =>
          match hdivides : firstUndivisibleLower? current.result with
          | none =>
              some
                { certificate := current
                  stable := stableOfSearches A hdet hcolumn hdivides
                  passes := 1
                  injections := 0 }
          | some position =>
              let injection := injectLowerWitness current.result position.2
              let accumulated := compose current injection
              match stabilize? fuel accumulated.result
                  (result_det_ne_zero accumulated hdet) with
              | none => none
              | some next =>
                  some
                    { certificate := compose accumulated next.certificate
                      stable := next.stable
                      passes := next.passes + 1
                      injections := next.injections + 1 }

public theorem Stabilization.equation {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (result : Stabilization A) :
    result.certificate.U * A * result.certificate.V =
      result.certificate.result :=
  result.certificate.equation

public theorem Stabilization.inverse_equation {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (result : Stabilization A) :
    result.certificate.U_cert.inverse * result.certificate.result *
        result.certificate.V_cert.inverse = A :=
  NormalForms.Research.KannanBachem.Smith.inverse_equation
    result.certificate

public theorem Stabilization.result_det_ne_zero {n : Nat}
    {A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int}
    (result : Stabilization A) (hdet : A.det ≠ 0) :
    result.certificate.result.det ≠ 0 :=
  NormalForms.Research.KannanBachem.Smith.result_det_ne_zero
    result.certificate hdet

end NormalForms.Research.KannanBachem.Smith
