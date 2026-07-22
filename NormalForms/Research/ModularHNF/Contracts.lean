/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import NormalForms.Euclidean.Int
public import NormalForms.Matrix.Smith.Algorithm
import all NormalForms.Matrix.Smith.Algorithm

/-!
# Explicit contracts for modular integer HNF

FLINT's modular row-HNF routines assume full column rank and do not check it.
They additionally assume that the supplied positive modulus is a multiple of
either the determinant of the nonzero HNF rows or the largest elementary
divisor.  This module turns those assumptions into data.  It contains no
algorithm and imports no external adapter.
-/

public section

namespace NormalForms.Research.ModularHNF

open scoped Matrix
open NormalForms.Matrix.Smith

/-- The integer matrix obtained by selecting a caller-supplied set of rows. -/
@[expose] public def selectedSquareMinor {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (rows : Fin n ↪ Fin m) :
    _root_.Matrix (Fin n) (Fin n) Int :=
  A.submatrix rows id

/--
A constructive full-column-rank certificate: `rows` selects a nonsingular
`n`-by-`n` minor.  In particular, its data entails `n <= m`; no unchecked
rank assertion is hidden in the interface.
-/
public structure FullColumnRankWitness {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) where
  rows : Fin n ↪ Fin m
  det_ne_zero : (selectedSquareMinor A rows).det ≠ 0

namespace FullColumnRankWitness

/-- The selected rows make the dimension inequality computationally explicit. -/
public theorem columns_le_rows {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (witness : FullColumnRankWitness A) : n ≤ m :=
  by
    simpa using
      (Fintype.card_le_of_injective witness.rows witness.rows.injective)

/-- Full column rank over the rationals follows from the selected minor. -/
public theorem rational_rank_eq {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (witness : FullColumnRankWitness A) :
    (A.map (Int.castRingHom Rat)).rank = n := by
  let B := selectedSquareMinor A witness.rows
  have hdetMap :
      (B.map (Int.castRingHom Rat)).det ≠ 0 := by
    change ((Int.castRingHom Rat).mapMatrix B).det ≠ 0
    rw [← (Int.castRingHom Rat).map_det B]
    change (B.det : Rat) ≠ 0
    exact_mod_cast (show B.det ≠ 0 by
      simpa [B] using witness.det_ne_zero)
  have hminorRank : (B.map (Int.castRingHom Rat)).rank = n := by
    have hunit : IsUnit (B.map (Int.castRingHom Rat)) :=
      (_root_.Matrix.isUnit_iff_isUnit_det _).2
        (isUnit_iff_ne_zero.mpr hdetMap)
    simpa using
      (_root_.Matrix.rank_of_isUnit
        (B.map (Int.castRingHom Rat)) hunit)
  have hsubmatrix :
      (B.map (Int.castRingHom Rat)) =
        (A.map (Int.castRingHom Rat)).submatrix witness.rows id := by
    ext i j
    rfl
  rw [hsubmatrix] at hminorRank
  have lower : n ≤ (A.map (Int.castRingHom Rat)).rank := by
    calc
      n = ((A.map (Int.castRingHom Rat)).submatrix witness.rows id).rank :=
        hminorRank.symm
      _ ≤ (A.map (Int.castRingHom Rat)).rank :=
        _root_.Matrix.rank_submatrix_le _ _ _
  exact le_antisymm (by
    simpa using
      (_root_.Matrix.rank_le_card_width
        (A.map (Int.castRingHom Rat)))) lower

end FullColumnRankWitness

/--
The stronger, directly checkable determinant-modulus contract.  It records a
multiple of one explicitly nonsingular selected minor.  The correctness layer
is responsible for connecting this conservative condition to the nonzero-row
HNF determinant required by the modular kernel.
-/
public structure DeterminantModulusWitness {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A) where
  modulus : Int
  positive : 0 < modulus
  selectedMinor_dvd :
    (selectedSquareMinor A fullRank.rows).det.natAbs ∣ modulus.natAbs

/-- Canonical largest elementary divisor, with neutral value `1` in width zero. -/
@[expose] public def largestElementaryDivisor {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A) : Int :=
  match n with
  | 0 => 1
  | k + 1 =>
      (NormalForms.Matrix.Smith.smithNormalFormFin A).S
        (Fin.castLE fullRank.columns_le_rows ⟨k, by omega⟩)
        ⟨k, by omega⟩

/--
The elementary-divisor contract used by `fmpz_mat_hnf_modular_eldiv`.
`largest` is tied to the canonical Smith result rather than accepted as
uninterpreted metadata.  Dimension zero uses the conventional neutral value
`1`.
-/
public structure ElementaryDivisorModulusWitness {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A) where
  modulus : Int
  positive : 0 < modulus
  largest : Int
  largest_eq : largest = largestElementaryDivisor A fullRank
  largest_dvd : largest.natAbs ∣ modulus.natAbs

/-- Exactly the two documented modular-HNF input contracts. -/
public inductive ModulusWitness {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (fullRank : FullColumnRankWitness A) where
  | determinant (witness : DeterminantModulusWitness A fullRank)
  | elementaryDivisor (witness : ElementaryDivisorModulusWitness A fullRank)

namespace ModulusWitness

/-- The caller-supplied positive modulus, independent of witness flavor. -/
@[expose] public def modulus {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    {fullRank : FullColumnRankWitness A} :
    ModulusWitness A fullRank → Int
  | .determinant witness => witness.modulus
  | .elementaryDivisor witness => witness.modulus

public theorem positive {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    {fullRank : FullColumnRankWitness A}
    (witness : ModulusWitness A fullRank) : 0 < witness.modulus := by
  cases witness with
  | determinant witness => exact witness.positive
  | elementaryDivisor witness => exact witness.positive

public theorem nonzero {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    {fullRank : FullColumnRankWitness A}
    (witness : ModulusWitness A fullRank) : witness.modulus ≠ 0 :=
  ne_of_gt witness.positive

end ModulusWitness

end NormalForms.Research.ModularHNF
