/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Hermite.PrincipalInternal

/-!
# Principal-Minor Kannan--Bachem HNF Transitions

Public instrumentation for Steps 3--6 of the 1979 Kannan--Bachem HNF
algorithm, transposed to the project's row-oriented convention.  Recursive
state and transition helpers in the implementation module are not exported.
-/

public section
