/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.ModularHNF.Contracts

/-!
# Executable DKT modular HNF value kernel

This is a direct, pure Lean transcription of FLINT 3.6.0's
`fmpz_mat_hnf_modular` transition order.  It deliberately returns only an
untrusted candidate and telemetry at this layer.  A later correctness module
connects a legal modulus witness to the canonical strong HNF result.
-/

public section

namespace NormalForms.Research.ModularHNF

open scoped Matrix
open NormalForms

/-- Exact scalar-operation telemetry for the modular value kernel. -/
public structure ModularOperationCount where
  additions : Nat := 0
  multiplications : Nat := 0
  xgcdCalls : Nat := 0
  exactDivisions : Nat := 0
  modularReductions : Nat := 0
  comparisons : Nat := 0
  deriving DecidableEq, Repr

namespace ModularOperationCount

@[expose] public def add (left right : ModularOperationCount) : ModularOperationCount :=
  { additions := left.additions + right.additions
    multiplications := left.multiplications + right.multiplications
    xgcdCalls := left.xgcdCalls + right.xgcdCalls
    exactDivisions := left.exactDivisions + right.exactDivisions
    modularReductions := left.modularReductions + right.modularReductions
    comparisons := left.comparisons + right.comparisons }

instance : Add ModularOperationCount := ⟨add⟩

@[simp] public theorem add_apply (left right : ModularOperationCount) :
    left + right = add left right := rfl

@[expose] public def total (count : ModularOperationCount) : Nat :=
  count.additions + count.multiplications + count.xgcdCalls +
    count.exactDivisions + count.modularReductions + count.comparisons

end ModularOperationCount

/-- One observable stage of the DKT modulus schedule. -/
public structure ModularStageEvent where
  column : Nat
  modulusBefore : Int
  gcdWithPivot : Int
  modulusAfter : Int
  deriving DecidableEq, Repr

/-- Candidate matrix plus an exact operation trace; this is not a certificate. -/
public structure RawModularRun (m n : Nat) where
  candidate : _root_.Matrix (Fin m) (Fin n) Int
  finalModulus : Int
  stages : List ModularStageEvent
  operations : ModularOperationCount

namespace Internal

def setEntry {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (row : Fin m) (column : Fin n) (value : Int) :
    _root_.Matrix (Fin m) (Fin n) Int :=
  Function.update A row (Function.update (A row) column value)

/-- FLINT's positive centered representative in `(-R/2, R/2]`. -/
@[expose] def centeredMod (value modulus : Int) : Int :=
  let residue := value % modulus
  if modulus / 2 < residue then residue - modulus else residue

def replacePairSuffix {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) (modulus : Int)
    (u v pivotDivGcd targetDivGcd : Int) :
    _root_.Matrix (Fin m) (Fin n) Int :=
  fun row currentColumn =>
    if currentColumn < column then
      A row currentColumn
    else if row = pivot then
      centeredMod
        (u * A pivot currentColumn + v * A target currentColumn) modulus
    else if row = target then
      centeredMod
        (pivotDivGcd * A target currentColumn -
          targetDivGcd * A pivot currentColumn) modulus
    else
      A row currentColumn

def reduceBelowRow {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) (modulus : Int) :
    _root_.Matrix (Fin m) (Fin n) Int × ModularOperationCount :=
  if A target column = 0 then
    (A, { comparisons := 1 })
  else
    let gcdData := ComputableEuclideanOps.xgcd (A pivot column) (A target column)
    let pivotDivGcd := A pivot column / gcdData.gcd
    let targetDivGcd := A target column / gcdData.gcd
    let width := n - column.val
    (replacePairSuffix A pivot target column modulus
      gcdData.leftCoeff gcdData.rightCoeff pivotDivGcd targetDivGcd,
      { additions := 2 * width
        multiplications := 4 * width
        xgcdCalls := 1
        exactDivisions := 2
        modularReductions := 2 * width
        comparisons := 1 + 2 * width })

def reduceBelow {m n : Nat}
    (pivot : Fin m) (column : Fin n) (modulus : Int) :
    List (Fin m) →
      _root_.Matrix (Fin m) (Fin n) Int →
      _root_.Matrix (Fin m) (Fin n) Int × ModularOperationCount
  | [] => fun A => (A, {})
  | target :: tail => fun A =>
      if pivot < target then
        let current := reduceBelowRow A pivot target column modulus
        let rest := reduceBelow pivot column modulus tail current.1
        (rest.1, current.2 + rest.2)
      else
        reduceBelow pivot column modulus tail A

def scalePivotSuffix {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot : Fin m) (column : Fin n) (coefficient modulus : Int) :
    _root_.Matrix (Fin m) (Fin n) Int :=
  fun row currentColumn =>
    if row = pivot ∧ column ≤ currentColumn then
      (coefficient * A row currentColumn) % modulus
    else
      A row currentColumn

def reduceAboveRow {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (pivot target : Fin m) (column : Fin n) :
    _root_.Matrix (Fin m) (Fin n) Int :=
  let quotient := A target column / A pivot column
  fun row currentColumn =>
    if row = target ∧ column ≤ currentColumn then
      A row currentColumn - quotient * A pivot currentColumn
    else
      A row currentColumn

def reduceAbove {m n : Nat}
    (pivot : Fin m) (column : Fin n) :
    List (Fin m) → _root_.Matrix (Fin m) (Fin n) Int →
      _root_.Matrix (Fin m) (Fin n) Int
  | [], A => A
  | target :: tail, A =>
      if target < pivot then
        reduceAbove pivot column tail (reduceAboveRow A pivot target column)
      else
        reduceAbove pivot column tail A

def stage {m n : Nat} (columns_le_rows : n ≤ m)
    (state : RawModularRun m n) (column : Fin n) : RawModularRun m n :=
  let pivot : Fin m := Fin.castLE columns_le_rows column
  let modulus := state.finalModulus
  let prepared :=
    if state.candidate pivot column = 0 then
      setEntry state.candidate pivot column modulus
    else
      state.candidate
  let below := reduceBelow pivot column modulus (List.finRange m) prepared
  let gcdData := ComputableEuclideanOps.xgcd (below.1 pivot column) modulus
  let scaled := scalePivotSuffix below.1 pivot column gcdData.leftCoeff modulus
  let restored :=
    if scaled pivot column = 0 then
      setEntry scaled pivot column modulus
    else
      scaled
  let reduced := reduceAbove pivot column (List.finRange m).reverse restored
  let width := n - column.val
  let rowsAbove := column.val
  let stageOperations : ModularOperationCount :=
    below.2 +
      { additions := rowsAbove * width
        multiplications := width + rowsAbove * width
        xgcdCalls := 1
        exactDivisions := rowsAbove + 1
        modularReductions := width
        comparisons := 2 + width }
  { candidate := reduced
    finalModulus := modulus / gcdData.gcd
    stages := state.stages ++
      [{ column := column.val
         modulusBefore := modulus
         gcdWithPivot := gcdData.gcd
         modulusAfter := modulus / gcdData.gcd }]
    operations := state.operations + stageOperations }

def runColumns {m n : Nat} (columns_le_rows : n ≤ m) :
    List (Fin n) → RawModularRun m n → RawModularRun m n
  | [], state => state
  | column :: tail, state =>
      runColumns columns_le_rows tail (stage columns_le_rows state column)

end Internal

/--
Execute the DKT value kernel using an arbitrary positive input modulus.  The
function is total even for an invalid modulus, but only the typed witness
entry point below is eligible for a later correctness theorem.
-/
@[expose] public def runRaw {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (columns_le_rows : n ≤ m) (modulus : Int) : RawModularRun m n :=
  Internal.runColumns columns_le_rows (List.finRange n)
    { candidate := A
      finalModulus := modulus
      stages := []
      operations := {} }

/--
Execute the DKT determinant-modulus kernel through its documented contract.
The elementary-divisor contract belongs to FLINT's distinct strong-echelon
kernel and is intentionally not accepted here.
-/
@[expose] public def runWithDeterminantWitness {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A)
    (modulus : DeterminantModulusWitness A fullRank) : RawModularRun m n :=
  runRaw A fullRank.columns_le_rows modulus.modulus

end NormalForms.Research.ModularHNF
