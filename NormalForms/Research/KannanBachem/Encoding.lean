/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Research.KannanBachem.Execution.Smith

/-! # Concrete Self-delimiting Binary Encoding -/

public section

namespace NormalForms.Research.KannanBachem

open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Smith
open NormalForms.Research.BitCost

/-- Least-significant-constructor-first positive binary payload. -/
@[expose] public def encodePosNum : PosNum → List Bool
  | .one => [true]
  | .bit0 rest => false :: encodePosNum rest
  | .bit1 rest => true :: encodePosNum rest

/-- Decode one complete positive binary payload. -/
@[expose] public def decodePosNum : List Bool → Option PosNum
  | [] => none
  | [true] => some .one
  | false :: rest => .bit0 <$> decodePosNum rest
  | true :: bit :: rest => .bit1 <$> decodePosNum (bit :: rest)

@[simp] public theorem decodePosNum_encode (magnitude : PosNum) :
    decodePosNum (encodePosNum magnitude) = some magnitude := by
  induction magnitude with
  | one => rfl
  | bit0 rest ih => simp [encodePosNum, decodePosNum, ih]
  | bit1 rest ih =>
      cases encoded : encodePosNum rest with
      | nil =>
          have nonempty : encodePosNum rest ≠ [] := by
            cases rest <;> simp [encodePosNum]
          exact (nonempty encoded).elim
      | cons bit tail =>
          simpa [encodePosNum, decodePosNum, encoded] using
            congrArg (Option.map PosNum.bit1) ih

public theorem encodePosNum_length_eq_bitLength (magnitude : PosNum) :
    (encodePosNum magnitude).length = magnitude.natSize := by
  induction magnitude with
  | one => rfl
  | bit0 rest ih | bit1 rest ih =>
      simp [encodePosNum, PosNum.natSize, ih]

/-- Raw canonical binary magnitude of a natural number. -/
@[expose] public def encodeNat (value : Nat) : List Bool :=
  match Num.ofNat' value with
  | .zero => []
  | .pos magnitude => encodePosNum magnitude

/-- Decode one complete raw natural-number magnitude. -/
@[expose] public def decodeNat : List Bool → Option Nat
  | [] => some 0
  | bits => (fun magnitude : PosNum ↦ (magnitude : Nat)) <$> decodePosNum bits

public theorem decodeNat_encodePosNum (magnitude : PosNum) :
    decodeNat (encodePosNum magnitude) = some (magnitude : Nat) := by
  cases encoded : encodePosNum magnitude with
  | nil =>
      have nonempty : encodePosNum magnitude ≠ [] := by
        cases magnitude <;> simp [encodePosNum]
      exact (nonempty encoded).elim
  | cons bit rest =>
      have decoded := decodePosNum_encode magnitude
      rw [encoded] at decoded
      simp [decodeNat, decoded]

@[simp] public theorem decodeNat_encode (value : Nat) :
    decodeNat (encodeNat value) = some value := by
  rw [encodeNat]
  cases converted : Num.ofNat' value with
  | zero =>
      have valueZero : value = 0 := by
        have := congrArg (fun number : Num ↦ (number : Nat)) converted
        simpa [Num.ofNat'_eq] using this
      simp [valueZero, decodeNat]
  | pos magnitude =>
      have magnitudeValue : (magnitude : Nat) = value := by
        have := congrArg (fun number : Num ↦ (number : Nat)) converted
        simpa [Num.ofNat'_eq] using this.symm
      rw [decodeNat_encodePosNum, magnitudeValue]

public theorem encodeNat_length_eq_natSize (value : Nat) :
    (encodeNat value).length = value.size := by
  rw [encodeNat]
  cases converted : Num.ofNat' value with
  | zero =>
      have valueZero : value = 0 := by
        have := congrArg (fun number : Num ↦ (number : Nat)) converted
        simpa [Num.ofNat'_eq] using this
      simp [valueZero]
  | pos magnitude =>
      rw [encodePosNum_length_eq_bitLength]
      have magnitudeValue : (magnitude : Nat) = value := by
        have := congrArg (fun number : Num ↦ (number : Nat)) converted
        simpa [Num.ofNat'_eq] using this.symm
      have sizeEquality := Num.natSize_to_nat (Num.pos magnitude)
      change magnitude.natSize = ((magnitude : Nat)).size at sizeEquality
      simpa [magnitudeValue] using sizeEquality

/-- Canonical integer payload before pair framing. -/
@[expose] public def intPayload : Int → List Bool
  | .ofNat 0 => [false]
  | .ofNat (value + 1) =>
      false :: encodeNat (value + 1)
  | .negSucc value =>
      true :: encodeNat (value + 1)

/-- Decode a complete canonical integer payload; `[true]` is rejected. -/
@[expose] public def decodeIntPayload : List Bool → Option Int
  | [false] => some 0
  | false :: bit :: magnitude =>
      (fun value : Nat ↦ (value : Int)) <$> decodeNat (bit :: magnitude)
  | [true] => none
  | true :: bit :: magnitude =>
      (fun value : Nat ↦ -((value : Int))) <$> decodeNat (bit :: magnitude)
  | [] => none

@[simp] public theorem intPayload_zero : intPayload 0 = [false] := rfl

public theorem intPayload_pos (value : Nat) :
    intPayload (Int.ofNat (value + 1)) =
      false :: encodeNat (value + 1) :=
  rfl

public theorem intPayload_neg (value : Nat) :
    intPayload (Int.negSucc value) =
      true :: encodeNat (value + 1) :=
  rfl

@[simp] public theorem decodeIntPayload_encode (value : Int) :
    decodeIntPayload (intPayload value) = some value := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => rfl
      | succ value =>
          cases encoded : encodeNat (value + 1) with
          | nil =>
              have lengthPositive :
                  0 < (encodeNat (value + 1)).length := by
                rw [encodeNat_length_eq_natSize]
                exact Nat.size_pos.mpr (by omega)
              simp [encoded] at lengthPositive
          | cons bit rest =>
              have decoded :
                  decodeNat (bit :: rest) = some (value + 1) := by
                simpa [encoded] using decodeNat_encode (value + 1)
              simp [intPayload, decodeIntPayload, encoded, decoded]
  | negSucc value =>
      cases encoded : encodeNat (value + 1) with
      | nil =>
          have lengthPositive :
              0 < (encodeNat (value + 1)).length := by
            rw [encodeNat_length_eq_natSize]
            exact Nat.size_pos.mpr (by omega)
          simp [encoded] at lengthPositive
      | cons bit rest =>
          have decoded :
              decodeNat (bit :: rest) = some (value + 1) := by
            simpa [encoded] using decodeNat_encode (value + 1)
          simp only [intPayload, decodeIntPayload, encoded, decoded]
          rw [Int.negSucc_eq]
          rfl

public theorem intPayload_injective : Function.Injective intPayload := by
  intro left right equality
  have decoded := congrArg decodeIntPayload equality
  simpa using decoded

/--
Pair framing: `00` carries false, `11` carries true, `01` terminates, and
`10` is invalid.
-/
@[expose] public def framePayload : List Bool → List Bool
  | [] => [false, true]
  | false :: rest => false :: false :: framePayload rest
  | true :: rest => true :: true :: framePayload rest

/-- Decode one framed prefix and return the untouched suffix. -/
@[expose] public def decodeFramedPrefix :
    List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => do
      let (payload, suffix) ← decodeFramedPrefix rest
      some (false :: payload, suffix)
  | true :: true :: rest => do
      let (payload, suffix) ← decodeFramedPrefix rest
      some (true :: payload, suffix)
  | false :: true :: rest => some ([], rest)
  | _ => none

public theorem decodeFramedPrefix_encode_append
    (payload suffix : List Bool) :
    decodeFramedPrefix (framePayload payload ++ suffix) =
      some (payload, suffix) := by
  induction payload with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp [framePayload, decodeFramedPrefix, ih]

@[simp] public theorem framePayload_length (payload : List Bool) :
    (framePayload payload).length = 2 * payload.length + 2 := by
  induction payload with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> simp [framePayload, ih] <;> omega

/-- One self-delimiting integer atom. -/
@[expose] public def encodeIntegerAtom (value : Int) : List Bool :=
  framePayload (intPayload value)

/-- Decode one self-delimiting integer atom. -/
@[expose] public def decodeIntegerAtomPrefix
    (bits : List Bool) : Option (Int × List Bool) := do
  let (payload, suffix) ← decodeFramedPrefix bits
  let value ← decodeIntPayload payload
  some (value, suffix)

public theorem decodeIntegerAtomPrefix_encode_append
    (value : Int) (suffix : List Bool) :
    decodeIntegerAtomPrefix (encodeIntegerAtom value ++ suffix) =
      some (value, suffix) := by
  simp [decodeIntegerAtomPrefix, encodeIntegerAtom,
    decodeFramedPrefix_encode_append]

/-- Magnitude-bit length of a canonical integer. -/
@[expose] public def integerBitLength (value : Int) : Nat :=
  value.natAbs.size

/-- Concrete atom length in the abstract binary alphabet. -/
@[expose] public def integerAtomLength (value : Int) : Nat :=
  (encodeIntegerAtom value).length

public theorem intPayload_length (value : Int) :
    (intPayload value).length = integerBitLength value + 1 := by
  cases value with
  | ofNat value =>
      cases value with
      | zero => rfl
      | succ value =>
          simp only [intPayload, List.length_cons,
            encodeNat_length_eq_natSize, integerBitLength]
          rfl
  | negSucc value =>
      simp [intPayload, integerBitLength,
        encodeNat_length_eq_natSize]

public theorem integerAtomLength_eq (value : Int) :
    integerAtomLength value = 2 * (integerBitLength value + 2) := by
  rw [integerAtomLength, encodeIntegerAtom, framePayload_length,
    intPayload_length]
  omega

/-- A dependently typed square integer matrix. -/
@[ext] public structure PackedMatrix where
  n : Nat
  matrix : Matrix (Fin n) (Fin n) Int

/-- Row-major entries using the standard finite-product equivalence. -/
@[expose] public def matrixEntries {n : Nat}
    (matrix : Matrix (Fin n) (Fin n) Int) : List Int :=
  List.ofFn fun index : Fin (n * n) ↦
    let position := finProdFinEquiv.symm index
    matrix position.1 position.2

/-- Reconstruct a square matrix from row-major entries. -/
@[expose] public def matrixOfEntries (n : Nat) (entries : List Int) :
    Matrix (Fin n) (Fin n) Int :=
  fun row column ↦ entries.getD (finProdFinEquiv (row, column)).val 0

public theorem matrixOfEntries_matrixEntries {n : Nat}
    (matrix : Matrix (Fin n) (Fin n) Int) :
    matrixOfEntries n (matrixEntries matrix) = matrix := by
  ext row column
  let index := finProdFinEquiv (row, column)
  have indexLt : index.val < (matrixEntries matrix).length := by
    simp only [matrixEntries, List.length_ofFn]
    exact index.isLt
  rw [matrixOfEntries, List.getD_eq_getElem _ _ indexLt]
  change
    (List.ofFn (fun index : Fin (n * n) ↦
      let position := finProdFinEquiv.symm index
      matrix position.1 position.2))[index.val] = matrix row column
  rw [List.getElem_ofFn]
  simpa only [index] using congrArg (fun position ↦ matrix position.1 position.2)
    (finProdFinEquiv.symm_apply_apply (row, column))

/-- Parse exactly `count` integer atoms. -/
@[expose] public def decodeIntegerAtoms :
    Nat → List Bool → Option (List Int × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← decodeIntegerAtomPrefix bits
      let (tail, suffix) ← decodeIntegerAtoms count rest
      some (head :: tail, suffix)

public theorem decodeIntegerAtoms_encode_append
    (values : List Int) (suffix : List Bool) :
    decodeIntegerAtoms values.length
        (values.flatMap encodeIntegerAtom ++ suffix) =
      some (values, suffix) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp [decodeIntegerAtoms, decodeIntegerAtomPrefix_encode_append, ih]

/-- Unframed typed-matrix payload. -/
@[expose] public def matrixPayload (packed : PackedMatrix) : List Bool :=
  framePayload (encodeNat packed.n) ++
    (matrixEntries packed.matrix).flatMap encodeIntegerAtom

/-- Concrete typed square-matrix encoding. -/
@[expose] public def encodeMatrix (packed : PackedMatrix) : List Bool :=
  framePayload (matrixPayload packed)

/-- Prefix decoder returning a packed square matrix and arbitrary suffix. -/
@[expose] public def decodePackedMatrixPrefix
    (bits : List Bool) : Option (PackedMatrix × List Bool) := do
  let (payload, suffix) ← decodeFramedPrefix bits
  let (dimensionBits, entriesBits) ← decodeFramedPrefix payload
  let dimension ← decodeNat dimensionBits
  let (entries, rest) ← decodeIntegerAtoms (dimension * dimension) entriesBits
  if rest.isEmpty then
    some (⟨dimension, matrixOfEntries dimension entries⟩, suffix)
  else
    none

public theorem decodePackedMatrixPrefix_encode_append
    (packed : PackedMatrix) (suffix : List Bool) :
    decodePackedMatrixPrefix (encodeMatrix packed ++ suffix) =
      some (packed, suffix) := by
  cases packed with
  | mk n matrix =>
      have atoms := decodeIntegerAtoms_encode_append
        (matrixEntries matrix) ([] : List Bool)
      simp only [List.append_nil] at atoms
      have entryLength : (matrixEntries matrix).length = n * n := by
        simp [matrixEntries]
      rw [entryLength] at atoms
      simp only [decodePackedMatrixPrefix, encodeMatrix, matrixPayload,
        decodeFramedPrefix_encode_append]
      simp only [Option.bind_eq_bind]
      simp [decodeFramedPrefix_encode_append, decodeNat_encode, atoms,
        matrixOfEntries_matrixEntries]

/-- Matrix payload length before its outer framing. -/
@[expose] public def matrixBinarySize (packed : PackedMatrix) : Nat :=
  (matrixPayload packed).length

/-- Concrete matrix encoding length. -/
@[expose] public def matrixEncodingLength (packed : PackedMatrix) : Nat :=
  (encodeMatrix packed).length

public theorem matrixEncodingLength_eq (packed : PackedMatrix) :
    matrixEncodingLength packed = 2 * matrixBinarySize packed + 2 := by
  simp [matrixEncodingLength, matrixBinarySize, encodeMatrix]

public theorem packedMatrix_dimension_le_binarySize (packed : PackedMatrix) :
    packed.n ≤ matrixBinarySize packed := by
  cases packed with
  | mk n matrix =>
      have atoms :
          (matrixEntries matrix).length ≤
            ((matrixEntries matrix).map integerAtomLength).sum := by
        calc
          (matrixEntries matrix).length =
              ((matrixEntries matrix).map fun _ ↦ 1).sum := by simp
          _ ≤ ((matrixEntries matrix).map integerAtomLength).sum := by
            apply List.sum_le_sum
            intro value member
            rw [integerAtomLength_eq]
            omega
      have entryLength : (matrixEntries matrix).length = n * n := by
        simp [matrixEntries]
      have dimensionSquare : n ≤ n * n := by
        cases n <;> nlinarith
      simp only [matrixBinarySize, matrixPayload, List.length_append,
        framePayload_length, List.length_flatMap]
      change n ≤ 2 * (encodeNat n).length + 2 +
        ((matrixEntries matrix).map integerAtomLength).sum
      omega

public theorem matrixBitLength_le_binarySize (packed : PackedMatrix) :
    Hermite.matrixBitLength packed.matrix ≤ matrixBinarySize packed := by
  cases packed with
  | mk n matrix =>
      let entries := matrixEntries matrix
      let atomLengths := entries.map integerAtomLength
      have atomSumLe :
          atomLengths.sum ≤ matrixBinarySize (⟨n, matrix⟩ : PackedMatrix) := by
        simp only [matrixBinarySize, matrixPayload, List.length_append,
          framePayload_length, List.length_flatMap]
        change atomLengths.sum ≤
          2 * (encodeNat n).length + 2 + atomLengths.sum
        omega
      have entryBound (row column : Fin n) :
          integerBitLength (matrix row column) ≤
            matrixBinarySize (⟨n, matrix⟩ : PackedMatrix) := by
        have member : matrix row column ∈ entries := by
          change matrix row column ∈ matrixEntries matrix
          rw [matrixEntries, List.mem_ofFn]
          exact ⟨finProdFinEquiv (row, column), by simp⟩
        have atomMember :
            integerAtomLength (matrix row column) ∈ atomLengths :=
          List.mem_map.mpr ⟨matrix row column, member, rfl⟩
        have atomLeSum :
            integerAtomLength (matrix row column) ≤ atomLengths.sum :=
          List.le_sum_of_mem atomMember
        rw [integerAtomLength_eq] at atomLeSum
        omega
      change Hermite.matrixBitLength matrix ≤
        matrixBinarySize (⟨n, matrix⟩ : PackedMatrix)
      unfold Hermite.matrixBitLength
      rw [Nat.size_le]
      have heightLe :
          Hermite.matrixHeight matrix ≤
            2 ^ matrixBinarySize (⟨n, matrix⟩ : PackedMatrix) - 1 := by
        apply Hermite.matrixHeight_le
        intro row column
        have entryLt :
            (matrix row column).natAbs <
              2 ^ matrixBinarySize (⟨n, matrix⟩ : PackedMatrix) :=
          Nat.size_le.mp (entryBound row column)
        have powerPositive :
            0 < 2 ^ matrixBinarySize (⟨n, matrix⟩ : PackedMatrix) :=
          pow_pos (by omega) _
        omega
      have powerPositive :
          0 < 2 ^ matrixBinarySize (⟨n, matrix⟩ : PackedMatrix) :=
        pow_pos (by omega) _
      omega

/-- No encoded packed matrix is a proper prefix of another. -/
public theorem packedMatrixEncoding_prefixFree
    (left right : PackedMatrix) (suffix : List Bool)
    (equality : encodeMatrix left ++ suffix = encodeMatrix right) :
    suffix = [] ∧ left = right := by
  have decoded := congrArg decodePackedMatrixPrefix equality
  rw [decodePackedMatrixPrefix_encode_append] at decoded
  have rightDecoded :
      decodePackedMatrixPrefix (encodeMatrix right) =
        some (right, []) := by
    simpa using decodePackedMatrixPrefix_encode_append right []
  rw [rightDecoded] at decoded
  exact ⟨congrArg (fun result ↦ result.2) (Option.some.inj decoded),
    congrArg (fun result ↦ result.1) (Option.some.inj decoded)⟩

/-- Data-only packed form of the five Smith output matrices. -/
public structure PackedSmithOutput where
  n : Nat
  S : Matrix (Fin n) (Fin n) Int
  U : Matrix (Fin n) (Fin n) Int
  Uinv : Matrix (Fin n) (Fin n) Int
  V : Matrix (Fin n) (Fin n) Int
  Vinv : Matrix (Fin n) (Fin n) Int

/-- Forget certificate proofs while retaining all five output matrices. -/
@[expose] public def _root_.NormalForms.Matrix.Smith.SNFResultFin.toPackedOutput
    {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) :
    PackedSmithOutput :=
  { n
    S := result.S
    U := result.U
    Uinv := result.U_cert.inverse
    V := result.V
    Vinv := result.V_cert.inverse }

/-- Unframed payload containing five independently typed matrices. -/
@[expose] public def smithOutputPayload {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) :
    List Bool :=
  encodeMatrix ⟨n, result.S⟩ ++
    encodeMatrix ⟨n, result.U⟩ ++
    encodeMatrix ⟨n, result.U_cert.inverse⟩ ++
    encodeMatrix ⟨n, result.V⟩ ++
    encodeMatrix ⟨n, result.V_cert.inverse⟩

/-- Concrete data-only Smith output encoding. -/
@[expose] public def encodeSmithOutput {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) :
    List Bool :=
  framePayload (smithOutputPayload result)

/-- Decode five typed matrices and require their dimensions to agree. -/
@[expose] public def decodePackedSmithOutputPrefix
    (bits : List Bool) : Option (PackedSmithOutput × List Bool) := do
  let (payload, suffix) ← decodeFramedPrefix bits
  let (s, rest) ← decodePackedMatrixPrefix payload
  let (u, rest) ← decodePackedMatrixPrefix rest
  let (uinv, rest) ← decodePackedMatrixPrefix rest
  let (v, rest) ← decodePackedMatrixPrefix rest
  let (vinv, rest) ← decodePackedMatrixPrefix rest
  if h : u.n = s.n ∧ uinv.n = s.n ∧ v.n = s.n ∧ vinv.n = s.n ∧
      rest.isEmpty then
    some
      ({ n := s.n
         S := s.matrix
         U := h.1 ▸ u.matrix
         Uinv := h.2.1 ▸ uinv.matrix
         V := h.2.2.1 ▸ v.matrix
         Vinv := h.2.2.2.1 ▸ vinv.matrix },
        suffix)
  else
    none

public theorem decodePackedSmithOutputPrefix_encode_append {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int}
    (result : SNFResultFin A) (suffix : List Bool) :
    decodePackedSmithOutputPrefix (encodeSmithOutput result ++ suffix) =
      some (result.toPackedOutput, suffix) := by
  have vinvDecoded :
      decodePackedMatrixPrefix
          (encodeMatrix ⟨n, result.V_cert.inverse⟩) =
        some (⟨n, result.V_cert.inverse⟩, []) := by
    simpa using decodePackedMatrixPrefix_encode_append
      (⟨n, result.V_cert.inverse⟩ : PackedMatrix) []
  simp [decodePackedSmithOutputPrefix, encodeSmithOutput,
    smithOutputPayload, decodeFramedPrefix_encode_append,
    decodePackedMatrixPrefix_encode_append, vinvDecoded,
    SNFResultFin.toPackedOutput]

/-- Smith-output payload length before outer framing. -/
@[expose] public def smithOutputBinarySize {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) : Nat :=
  (smithOutputPayload result).length

/-- Concrete five-matrix output encoding length. -/
@[expose] public def smithOutputEncodingLength {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) : Nat :=
  (encodeSmithOutput result).length

public theorem smithOutputEncodingLength_eq {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) :
    smithOutputEncodingLength result =
      2 * smithOutputBinarySize result + 2 := by
  simp [smithOutputEncodingLength, smithOutputBinarySize,
    encodeSmithOutput]

public theorem packedSmithOutputEncoding_prefixFree {n m : Nat}
    {A : Matrix (Fin n) (Fin n) Int} {B : Matrix (Fin m) (Fin m) Int}
    (left : SNFResultFin A) (right : SNFResultFin B) (suffix : List Bool)
    (equality : encodeSmithOutput left ++ suffix = encodeSmithOutput right) :
    suffix = [] ∧ left.toPackedOutput = right.toPackedOutput := by
  have decoded := congrArg decodePackedSmithOutputPrefix equality
  rw [decodePackedSmithOutputPrefix_encode_append] at decoded
  have rightDecoded :
      decodePackedSmithOutputPrefix (encodeSmithOutput right) =
        some (right.toPackedOutput, []) := by
    simpa using decodePackedSmithOutputPrefix_encode_append right []
  rw [rightDecoded] at decoded
  exact ⟨congrArg (fun output ↦ output.2) (Option.some.inj decoded),
    congrArg (fun output ↦ output.1) (Option.some.inj decoded)⟩

/-- Closed encoding-length bound for one `n × n` matrix of bounded entries. -/
@[expose] public def matrixEncodingLengthBound
    (dimension entryBits : Nat) : Nat :=
  2 * (2 * dimension.size + 2 +
    dimension * dimension * (2 * (entryBits + 2))) + 2

public theorem matrixEncodingLength_le_bound
    (packed : PackedMatrix) (entryBits : Nat)
    (bound :
      Hermite.matrixBitLength packed.matrix ≤ entryBits) :
    matrixEncodingLength packed ≤
      matrixEncodingLengthBound packed.n entryBits := by
  cases packed with
  | mk n matrix =>
      have atoms :
          ((matrixEntries matrix).map integerAtomLength).sum ≤
            (matrixEntries matrix).length * (2 * (entryBits + 2)) := by
        calc
          ((matrixEntries matrix).map integerAtomLength).sum ≤
              ((matrixEntries matrix).map
                fun _ ↦ 2 * (entryBits + 2)).sum := by
            apply List.sum_le_sum
            intro value member
            rw [integerAtomLength_eq]
            apply Nat.mul_le_mul_left
            apply Nat.add_le_add_right
            rw [matrixEntries, List.mem_ofFn] at member
            obtain ⟨index, rfl⟩ := member
            let position := finProdFinEquiv.symm index
            exact (Hermite.entry_bitLength_le_matrixBitLength
              matrix position.1 position.2).trans bound
          _ = (matrixEntries matrix).length * (2 * (entryBits + 2)) := by
            simp
      simp only [matrixEncodingLength, encodeMatrix, framePayload_length,
        matrixPayload, List.length_append, List.length_flatMap,
        encodeNat_length_eq_natSize, matrixEncodingLengthBound]
      have entryLength : (matrixEntries matrix).length = n * n := by
        simp [matrixEntries]
      have encodedAtoms :
          ((matrixEntries matrix).map
              fun value ↦ (encodeIntegerAtom value).length).sum ≤
            n * n * (2 * (entryBits + 2)) := by
        change ((matrixEntries matrix).map integerAtomLength).sum ≤
          n * n * (2 * (entryBits + 2))
        simpa [entryLength] using atoms
      omega

/-- Maximum entry width among the five data-only Smith output matrices. -/
@[expose] public def smithOutputMatrixBitLength {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) : Nat :=
  max (Hermite.matrixBitLength result.S)
    (max (Hermite.matrixBitLength result.U)
      (max (Hermite.matrixBitLength result.U_cert.inverse)
        (max (Hermite.matrixBitLength result.V)
          (Hermite.matrixBitLength result.V_cert.inverse))))

/-- Closed five-matrix encoding-length bound at a common entry width. -/
@[expose] public def smithOutputEncodingLengthBound
    (dimension entryBits : Nat) : Nat :=
  2 * (5 * matrixEncodingLengthBound dimension entryBits) + 2

public theorem smithOutputEncodingLength_le_bound {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} (result : SNFResultFin A) :
    smithOutputEncodingLength result ≤
      smithOutputEncodingLengthBound n
        (smithOutputMatrixBitLength result) := by
  let bits := smithOutputMatrixBitLength result
  have sBound := matrixEncodingLength_le_bound
    (⟨n, result.S⟩ : PackedMatrix) bits (le_max_left _ _)
  have uBound := matrixEncodingLength_le_bound
    (⟨n, result.U⟩ : PackedMatrix) bits
    ((le_max_left _ _).trans (le_max_right _ _))
  have uinvBound := matrixEncodingLength_le_bound
    (⟨n, result.U_cert.inverse⟩ : PackedMatrix) bits
    ((le_max_left _ _).trans <| (le_max_right _ _).trans (le_max_right _ _))
  have vBound := matrixEncodingLength_le_bound
    (⟨n, result.V⟩ : PackedMatrix) bits
    ((le_max_left _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _))
  have vinvBound := matrixEncodingLength_le_bound
    (⟨n, result.V_cert.inverse⟩ : PackedMatrix) bits
    ((le_max_right _ _).trans <| (le_max_right _ _).trans <|
      (le_max_right _ _).trans (le_max_right _ _))
  have sBound' :
      (encodeMatrix ⟨n, result.S⟩).length ≤
        matrixEncodingLengthBound n bits := by
    simpa [matrixEncodingLength] using sBound
  have uBound' :
      (encodeMatrix ⟨n, result.U⟩).length ≤
        matrixEncodingLengthBound n bits := by
    simpa [matrixEncodingLength] using uBound
  have uinvBound' :
      (encodeMatrix ⟨n, result.U_cert.inverse⟩).length ≤
        matrixEncodingLengthBound n bits := by
    simpa [matrixEncodingLength] using uinvBound
  have vBound' :
      (encodeMatrix ⟨n, result.V⟩).length ≤
        matrixEncodingLengthBound n bits := by
    simpa [matrixEncodingLength] using vBound
  have vinvBound' :
      (encodeMatrix ⟨n, result.V_cert.inverse⟩).length ≤
        matrixEncodingLengthBound n bits := by
    simpa [matrixEncodingLength] using vinvBound
  dsimp only [bits] at sBound' uBound' uinvBound' vBound' vinvBound'
  simp only [smithOutputEncodingLength, encodeSmithOutput,
    framePayload_length, smithOutputPayload, List.length_append,
    smithOutputEncodingLengthBound]
  omega

end NormalForms.Research.KannanBachem
