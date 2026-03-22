import NormalForms.Bridge.MathlibPID

/-!
# Abelian Groups from Presentation Matrices

Public `Int`-specialized wrappers around the executable Smith/PID bridge for
presentation quotients `ℤ^m / im(A)`.

The API keeps the executable invariant-factor data exactly as produced by the
current Smith layer, including unit factors `1`.
-/

namespace NormalForms.Applications.AbelianGroups

open NormalForms.Bridge.MathlibPID

/-- The submodule presented by the columns of `A`. -/
abbrev presentationSubmodule {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : _root_.Matrix m n Int) : Submodule Int (m → Int) :=
  pidSmithColumnSpan A

/-- The quotient `ℤ^m / im(A)` attached to a presentation matrix `A`. -/
abbrev presentationQuotient {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : _root_.Matrix m n Int) :=
  (m → Int) ⧸ presentationSubmodule A

/-- Number of executable invariant factors produced by the chosen Smith result. -/
noncomputable abbrev presentationInvariantFactorCount {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) : Nat :=
  pidExecutableInvariantFactorCount A

/-- The `i`-th executable invariant factor, read as a natural number via `natAbs`. -/
noncomputable abbrev presentationInvariantFactorFn {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) :
    Fin (presentationInvariantFactorCount A) → Nat :=
  fun i => (pidExecutableInvariantFactorFn A i).natAbs

/-- The executable invariant factors as a sorted list of natural numbers. -/
noncomputable abbrev presentationInvariantFactors {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) : List Nat :=
  pidExecutableSmithCoeffNatAbsList A

/-- The rank of the free `ℤ` summand in the presentation quotient. -/
noncomputable abbrev presentationFreeRank {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) : Nat :=
  Fintype.card m - presentationInvariantFactorCount A

@[simp] theorem presentationInvariantFactors_length {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) :
    (presentationInvariantFactors A).length = presentationInvariantFactorCount A := by
  exact pidExecutableSmithCoeffNatAbsList_length_eq_count A

/-- The public torsion-plus-free decomposition attached to a presentation matrix. -/
noncomputable def presentationQuotientEquivPiZModProd {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int) :
    presentationQuotient A ≃+
      (((i : Fin (presentationInvariantFactorCount A)) →
          ZMod (presentationInvariantFactorFn A i)) ×
        (Fin (presentationFreeRank A) → Int)) := by
  simpa [presentationQuotient, presentationSubmodule, presentationInvariantFactorCount,
    presentationInvariantFactorFn, presentationFreeRank] using
    pidExecutableQuotientEquivPiZModProd A

/-- In full-rank row cases, the executable invariant-factor count equals the row count. -/
theorem presentationInvariantFactorCount_eq_card_rows_of_finrank_eq_card_rows
    {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int)
    (hfull : Module.finrank Int (presentationSubmodule A) = Fintype.card m) :
    presentationInvariantFactorCount A = Fintype.card m := by
  simpa [presentationSubmodule, presentationInvariantFactorCount] using
    pidExecutableInvariantFactorCount_eq_card_rows_of_finrank_eq_card A hfull

/-- Full-rank presentation quotients are purely torsion, with no free `ℤ` summand. -/
noncomputable def presentationQuotientEquivPiZMod_of_fullRank {m n : Type _}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [NormalForms.Matrix.Hermite.CanonicalMod Int]
    (A : _root_.Matrix m n Int)
    (hfull : Module.finrank Int (presentationSubmodule A) = Fintype.card m) :
    presentationQuotient A ≃+
      ((i : Fin (presentationInvariantFactorCount A)) →
        ZMod (presentationInvariantFactorFn A i)) := by
  let hcount := presentationInvariantFactorCount_eq_card_rows_of_finrank_eq_card_rows A hfull
  simpa [presentationQuotient, presentationSubmodule, presentationInvariantFactorCount,
    presentationInvariantFactorFn] using
    pidExecutableQuotientEquivPiZMod A hcount

end NormalForms.Applications.AbelianGroups
