/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.Homology

/-!
# Finite Normalized Simplicial Examples

These examples exercise repeated faces, explicit degeneracy elimination, and
ordinary nondegenerate triangle boundaries.
-/

public section

namespace NormalForms.Examples.Homology

open NormalForms.Applications.Homology
open FiniteNormalizedSimplicialData

public def circleEdgeFace
    (_ : Fin 2) (_ : Fin 1) : Option (Fin 1) :=
  some 0

public def noTriangleFace
    (_ : Fin 3) (simplex : Fin 0) : Option (Fin 1) :=
  Fin.elim0 simplex

/--
Minimal normalized simplicial circle: one vertex and one nondegenerate edge.
The two equal endpoint faces cancel with opposite signs.
-/
@[expose] public def simplicialCircle :
    FiniteNormalizedSimplicialData :=
  ofDimensionTwo
    1 1 0
    circleEdgeFace
    noTriangleFace
    (by decide)

public def noEdgeFace
    (_ : Fin 2) (simplex : Fin 0) : Option (Fin 1) :=
  Fin.elim0 simplex

public def collapsedSphereTriangleFace
    (_ : Fin 3) (_ : Fin 1) : Option (Fin 0) :=
  none

/--
The normalized model `Δ² / ∂Δ²`: one vertex, no nondegenerate edges, and one
nondegenerate two-simplex. Every two-simplex face is explicitly degenerate.
-/
@[expose] public def collapsedBoundarySphere :
    FiniteNormalizedSimplicialData :=
  ofDimensionTwo
    1 0 1
    noEdgeFace
    collapsedSphereTriangleFace
    (by decide)

public def filledTriangleEdgeFace
    (i : Fin 2) (edge : Fin 3) : Option (Fin 3) :=
  match edge.1, i.1 with
  | 0, 0 => some 1
  | 0, _ => some 0
  | 1, 0 => some 2
  | 1, _ => some 0
  | _, 0 => some 2
  | _, _ => some 1

public def filledTriangleTriangleFace
    (i : Fin 3) (_ : Fin 1) : Option (Fin 3) :=
  match i.1 with
  | 0 => some 2
  | 1 => some 1
  | _ => some 0

/--
The standard filled two-simplex with vertices `0,1,2`, edges
`01,02,12`, and one nondegenerate triangle.
-/
@[expose] public def filledTriangle :
    FiniteNormalizedSimplicialData :=
  ofDimensionTwo
    3 3 1
    filledTriangleEdgeFace
    filledTriangleTriangleFace
    (by decide)

end NormalForms.Examples.Homology
