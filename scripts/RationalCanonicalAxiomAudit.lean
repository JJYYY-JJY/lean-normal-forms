/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms.Applications.RationalCanonical
meta import NormalForms.Applications.RationalCanonical
import Lean.Elab.Command
import Lean.Util.CollectAxioms
public meta import NormalForms.Tests.AuditEngine

/-!
# Rational Canonical Application Axiom Audit

The application is a semantic layer over the constructive polynomial Smith
kernel. Its basis and quotient constructions may use `Classical.choice`; no
project axiom, `sorryAx`, or compiler/native trust axiom is allowed.
-/

open Lean Elab Command

run_cmd do
  let declarations : Array Name :=
    #[``NormalForms.RationalCanonical.endomorphismPresentationMatrix_eq_charmatrix,
      ``NormalForms.RationalCanonical.endomorphismSmithResult,
      ``NormalForms.RationalCanonical.endomorphismInvariantFactors_product,
      ``NormalForms.RationalCanonical.endomorphismCyclicDecomposition,
      ``NormalForms.RationalCanonical.companionMatrix_charpoly,
      ``NormalForms.RationalCanonical.rationalCanonicalChangeCertificate,
      ``NormalForms.RationalCanonical.rationalCanonicalMatrix_eq_blocks,
      ``NormalForms.RationalCanonical.rationalCanonicalResult,
      ``NormalForms.RationalCanonical.lastInvariantFactor_eq_minpoly,
      ``NormalForms.RationalCanonical.largestInvariantFactor?_eq_minpoly,
      ``NormalForms.RationalCanonical.endomorphismInvariantFactors_eq_of_similarity,
      ``NormalForms.RationalCanonical.rationalCanonicalBlockMatrix_eq_of_similarity,
      ``NormalForms.RationalCanonical.endomorphismInvariantFactors_toMatrix_eq,
      ``NormalForms.RationalCanonical.rationalCanonicalBlockMatrix_toMatrix_eq]
  let allowed : Array Name :=
    #[``propext, ``Quot.sound, ``Classical.choice]
  NormalFormsScripts.AuditEngine.run declarations allowed
    [ ("schema",
        Lean.Json.str "normalforms.rational-canonical-axiom-audit/v1")
    ]
    "rational canonical audit found forbidden axioms"
