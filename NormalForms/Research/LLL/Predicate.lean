/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.LLL.GramSchmidt
public import NormalForms.Research.LLL.HexBackend

/-!
# Exact LLL predicates

The predicate uses the fixed `delta = 3/4` and `eta = 1/2` parameters.  It is
stated for row bases and uses exact rational arithmetic throughout.
-/

@[expose] public section

namespace NormalForms.Research.LLL

/-- Executable independence, equivalent to positivity of all leading Gram data. -/
public def HasPositiveGramSchmidtLengths {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Prop :=
  (toDense basis).independent

/-- All lower Gram--Schmidt coefficients lie in the fixed size-reduction window. -/
public def IsSizeReduced {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Prop :=
  let coefficients := Hex.GramSchmidt.Int.coeffs (toDense basis)
  ∀ row column, (row_lt : row < m) → (column_lt : column < row) →
    let rowFin : Fin m := ⟨row, row_lt⟩
    let columnFin : Fin m := ⟨column, Nat.lt_trans column_lt row_lt⟩
    let coefficient := coefficients[rowFin][columnFin]
    coefficient * coefficient ≤ eta * eta

/-- The fixed Lovasz condition on every adjacent pair. -/
public def SatisfiesLovasz {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Prop :=
  let orthogonal := Hex.GramSchmidt.Int.basis (toDense basis)
  let coefficients := Hex.GramSchmidt.Int.coeffs (toDense basis)
  ∀ row, (row_lt : row + 1 < m) →
    let rowFin : Fin m := ⟨row, Nat.lt_trans (Nat.lt_succ_self row) row_lt⟩
    let nextFin : Fin m := ⟨row + 1, row_lt⟩
    let coefficient := coefficients[nextFin][rowFin]
    delta * Hex.Internal.LLLCore.basisNormSq orthogonal rowFin ≤
      Hex.Internal.LLLCore.basisNormSq orthogonal nextFin +
        coefficient * coefficient *
          Hex.Internal.LLLCore.basisNormSq orthogonal rowFin

/-- A row basis is LLL reduced at the profile's fixed exact parameters. -/
public structure IsLLLReduced {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Prop where
  positive : HasPositiveGramSchmidtLengths basis
  sizeReduced : IsSizeReduced basis
  lovasz : SatisfiesLovasz basis

/-- Exact executable reducedness checker used by every public result path. -/
public def isLLLReducedB {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int) : Bool :=
  Hex.lllReduced (toDense basis) delta eta

/-- Acceptance by the exact integer checker entails the public rational contract. -/
public theorem isLLLReducedB_sound {m n : Nat}
    (basis : Matrix (Fin m) (Fin n) Int)
    (accepted : isLLLReducedB basis = true) : IsLLLReduced basis := by
  have checked := HexLLLMathlib.lllReduced_sound
    (toDense basis) delta eta accepted
  exact
    { positive := checked.2
      sizeReduced := by
        simpa [IsSizeReduced, Hex.isLLLReduced] using checked.1.1
      lovasz := by
        simpa [SatisfiesLovasz, Hex.isLLLReduced] using checked.1.2 }

end NormalForms.Research.LLL
