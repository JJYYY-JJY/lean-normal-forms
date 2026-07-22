/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

import NormalForms
import Lean.Util.CollectAxioms
public meta import NormalForms.Tests.AuditEngine

/-!
# Public axiom audit

Discovers every theorem or axiom declaration exported by the `NormalForms`
facade, emits one JSON record per declaration, and rejects any axiom outside
the public-wrapper allowlist. The arbitrary-`Fintype` API is intentionally allowed to use
`Classical.choice`; `sorryAx`, project-defined axioms, and compiler/native trust
axioms are not allowed.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let importedNames :=
    env.constants.map₁.fold (init := #[]) fun result name _ =>
      if name.toString.startsWith "NormalForms." then result.push name else result
  let allNormalFormsNames :=
    env.constants.map₂.foldl (init := importedNames) fun result name _ =>
      if name.toString.startsWith "NormalForms." then result.push name else result
  let names :=
    (allNormalFormsNames.filter fun name =>
        match env.find? name with
        | some (.thmInfo _) | some (.axiomInfo _) => true
        | _ => false).qsort Name.quickLt
  let allowed : Array Name := #[``propext, ``Quot.sound, ``Classical.choice]
  NormalFormsScripts.AuditEngine.run names allowed
    [ ("schema", Lean.Json.str "normalforms.axiom-audit/v1")
    , ("declarationCount", toJson names.size)
    ]
    "public axiom audit found unregistered axioms"
