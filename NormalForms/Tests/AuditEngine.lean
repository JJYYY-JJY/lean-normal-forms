/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

/-!
# Shared axiom-audit engine

Audit wrappers retain their own declaration roots, allowlists, schemas, and
profile fields. This module only performs the common collection, filtering,
and JSON rendering.
-/

namespace NormalFormsScripts.AuditEngine

open Lean Elab Command

public def run
    (declarations allowed : Array Name)
    (header : List (String × Lean.Json))
    (failureMessage : String) : CommandElabM Unit := do
  let mut rows : Array Lean.Json := #[]
  let mut violations : Array (Name × Array Name) := #[]
  for name in declarations do
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun ax => !allowed.contains ax
    if !forbidden.isEmpty then
      violations := violations.push (name, forbidden)
    rows := rows.push <| Lean.Json.mkObj
      [ ("declaration", Lean.Json.str name.toString)
      , ("axioms", Lean.Json.arr <| axioms.map fun ax => Lean.Json.str ax.toString)
      ]
  let report := Lean.Json.mkObj <| header ++
    [ ("allowlist", Lean.Json.arr <| allowed.map fun ax => Lean.Json.str ax.toString)
    , ("declarations", Lean.Json.arr rows)
    ]
  liftIO <| IO.println report.compress
  if !violations.isEmpty then
    throwError "{failureMessage}: {violations}"

end NormalFormsScripts.AuditEngine
