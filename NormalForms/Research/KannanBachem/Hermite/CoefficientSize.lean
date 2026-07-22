/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Nat.Size

/-!
# Coefficient sizes for the Kannan--Bachem development

This module fixes the size vocabulary used by the coefficient-growth and bit-
complexity proofs.  Matrix height is the largest absolute entry, while bit
length is the binary length of that natural-number height.  The determinant
envelope is the formal counterpart of Proposition 1 in Kannan--Bachem.
-/

public section

namespace NormalForms.Research.KannanBachem.Hermite

open scoped Matrix

/-- Binary magnitude length of a standard integer; zero has length zero. -/
@[expose] public def integerBitLength (a : Int) : Nat :=
  Nat.size a.natAbs

/-- Largest absolute entry of a finite integer matrix. -/
@[expose] public def matrixHeight {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : Nat :=
  Finset.univ.sup fun i => Finset.univ.sup fun j => (A i j).natAbs

/-- Binary length of the largest absolute matrix entry. -/
@[expose] public def matrixBitLength {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) : Nat :=
  Nat.size (matrixHeight A)

/-- Every entry is bounded by the matrix height. -/
public theorem entry_natAbs_le_matrixHeight {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (i : Fin m) (j : Fin n) :
    (A i j).natAbs ≤ matrixHeight A := by
  exact (Finset.le_sup (f := fun j => (A i j).natAbs) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup fun j => (A i j).natAbs)
      (Finset.mem_univ i))

/-- Matrix height is the least common natural bound on all entries. -/
public theorem matrixHeight_le {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int} {bound : Nat}
    (hbound : forall i j, (A i j).natAbs ≤ bound) :
    matrixHeight A ≤ bound := by
  apply Finset.sup_le
  intro i _
  apply Finset.sup_le
  intro j _
  exact hbound i j

@[simp] public theorem matrixHeight_zero {m n : Nat} :
    matrixHeight (0 : _root_.Matrix (Fin m) (Fin n) Int) = 0 := by
  simp [matrixHeight]

@[simp] public theorem matrixBitLength_zero {m n : Nat} :
    matrixBitLength (0 : _root_.Matrix (Fin m) (Fin n) Int) = 0 := by
  simp [matrixBitLength]

/-- Entry bit lengths are bounded by the matrix bit length. -/
public theorem entry_bitLength_le_matrixBitLength {m n : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int) (i : Fin m) (j : Fin n) :
    integerBitLength (A i j) ≤ matrixBitLength A := by
  exact Nat.size_le_size (entry_natAbs_le_matrixHeight A i j)

/--
Hadamard-free determinant envelope used in the original polynomiality proof:
the determinant is a sum of `n!` signed products of `n` bounded entries.
-/
public theorem determinant_natAbs_le_height_factorial {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    A.det.natAbs ≤ n.factorial * matrixHeight A ^ n := by
  have hdet := Matrix.det_le (A := A) (abv := AbsoluteValue.abs)
    (x := (matrixHeight A : Int)) (fun i j => by
      change |A i j| ≤ (matrixHeight A : Int)
      rw [Int.abs_eq_natAbs]
      exact_mod_cast entry_natAbs_le_matrixHeight A i j)
  simp only [Fintype.card_fin] at hdet
  change |A.det| ≤ n.factorial • (matrixHeight A : Int) ^ n at hdet
  simp only [Int.abs_eq_natAbs, Int.nsmul_eq_mul] at hdet
  exact_mod_cast hdet

private theorem natSize_mul_le (left right : Nat) :
    Nat.size (left * right) ≤ Nat.size left + Nat.size right := by
  rw [Nat.size_le, pow_add]
  exact mul_lt_mul''
    (Nat.lt_size_self left)
    (Nat.lt_size_self right)
    (Nat.zero_le _)
    (Nat.zero_le _)

private theorem natSize_pow_le (base exponent : Nat) :
    Nat.size (base ^ exponent) ≤ exponent * Nat.size base + 1 := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
      rw [pow_succ]
      calc
        Nat.size (base ^ exponent * base) ≤
            Nat.size (base ^ exponent) + Nat.size base :=
          natSize_mul_le _ _
        _ ≤ (exponent * Nat.size base + 1) + Nat.size base :=
          Nat.add_le_add_right ih _
        _ = (exponent + 1) * Nat.size base + 1 := by ring

private theorem natSize_factorial_le (n : Nat) :
    Nat.size n.factorial ≤ n * Nat.size n + 1 :=
  (Nat.size_le_size n.factorial_le_pow).trans (natSize_pow_le n n)

/-- Closed binary-length envelope for a determinant of order `n`. -/
@[expose] public def determinantBitLengthBound
    (n inputBits : Nat) : Nat :=
  n * (Nat.size n + inputBits) + 2

/-- Binary length of the factorial-power magnitude envelope. -/
public theorem factorial_mul_pow_size_le (order height : Nat) :
    Nat.size (order.factorial * height ^ order) ≤
      determinantBitLengthBound order (Nat.size height) := by
  unfold determinantBitLengthBound
  calc
    Nat.size (order.factorial * height ^ order) ≤
        Nat.size order.factorial + Nat.size (height ^ order) :=
      natSize_mul_le _ _
    _ ≤ (order * Nat.size order + 1) +
          (order * Nat.size height + 1) :=
      Nat.add_le_add (natSize_factorial_le order)
        (natSize_pow_le height order)
    _ = order * (Nat.size order + Nat.size height) + 2 := by ring

/-- Proposition 1 expressed directly as a polynomial binary-length bound. -/
public theorem determinant_bitLength_le {n : Nat}
    (A : _root_.Matrix (Fin n) (Fin n) Int) :
    integerBitLength A.det ≤
      determinantBitLengthBound n (matrixBitLength A) := by
  unfold integerBitLength matrixBitLength determinantBitLengthBound
  refine (Nat.size_le_size (determinant_natAbs_le_height_factorial A)).trans ?_
  exact factorial_mul_pow_size_le n (matrixHeight A)

/-- Matrix multiplication has the standard dimension-times-height envelope. -/
public theorem matrix_mul_height_le {m n p : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (B : _root_.Matrix (Fin n) (Fin p) Int) :
    matrixHeight (A * B) ≤
      n * (matrixHeight A * matrixHeight B) := by
  apply matrixHeight_le
  intro i j
  rw [_root_.Matrix.mul_apply]
  calc
    (∑ k, A i k * B k j).natAbs ≤
        ∑ k, (A i k * B k j).natAbs :=
      Int.natAbs_sum_le Finset.univ _
    _ ≤ ∑ _k : Fin n, matrixHeight A * matrixHeight B := by
      gcongr with k
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul
        (entry_natAbs_le_matrixHeight A i k)
        (entry_natAbs_le_matrixHeight B k j)
    _ = n * (matrixHeight A * matrixHeight B) := by simp

/-- Matrix-product coefficient length is additive up to the shared dimension. -/
public theorem matrix_mul_bitLength_le {m n p : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (B : _root_.Matrix (Fin n) (Fin p) Int) :
    matrixBitLength (A * B) ≤
      Nat.size n + matrixBitLength A + matrixBitLength B := by
  unfold matrixBitLength
  refine (Nat.size_le_size (matrix_mul_height_le A B)).trans ?_
  calc
    Nat.size (n * (matrixHeight A * matrixHeight B)) ≤
        Nat.size n + Nat.size (matrixHeight A * matrixHeight B) :=
      natSize_mul_le _ _
    _ ≤ Nat.size n +
          (Nat.size (matrixHeight A) + Nat.size (matrixHeight B)) :=
      Nat.add_le_add_left (natSize_mul_le _ _) _
    _ = Nat.size n + Nat.size (matrixHeight A) +
          Nat.size (matrixHeight B) := by omega

/-- Taking a finite submatrix cannot increase the largest absolute entry. -/
public theorem submatrix_height_le {m n r c : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (rows : Fin r → Fin m) (cols : Fin c → Fin n) :
    matrixHeight (A.submatrix rows cols) ≤ matrixHeight A := by
  apply matrixHeight_le
  intro i j
  exact entry_natAbs_le_matrixHeight A (rows i) (cols j)

/-- Taking a finite submatrix cannot increase the input coefficient length. -/
public theorem submatrix_bitLength_le {m n r c : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (rows : Fin r → Fin m) (cols : Fin c → Fin n) :
    matrixBitLength (A.submatrix rows cols) ≤ matrixBitLength A := by
  exact Nat.size_le_size (submatrix_height_le A rows cols)

/-- Every square minor satisfies the same factorial-height envelope. -/
public theorem minor_natAbs_le_height_factorial {m n k : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (rows : Fin k → Fin m) (cols : Fin k → Fin n) :
    (A.submatrix rows cols).det.natAbs ≤
      k.factorial * matrixHeight A ^ k := by
  exact (determinant_natAbs_le_height_factorial (A.submatrix rows cols)).trans
    (Nat.mul_le_mul_left k.factorial
      (Nat.pow_le_pow_left (submatrix_height_le A rows cols) k))

/-- Every square minor has a polynomial binary-length envelope in the input. -/
public theorem minor_bitLength_le {m n k : Nat}
    (A : _root_.Matrix (Fin m) (Fin n) Int)
    (rows : Fin k → Fin m) (cols : Fin k → Fin n) :
    integerBitLength (A.submatrix rows cols).det ≤
      determinantBitLengthBound k (matrixBitLength A) := by
  exact (determinant_bitLength_le (A.submatrix rows cols)).trans <| by
    unfold determinantBitLengthBound
    gcongr
    exact submatrix_bitLength_le A rows cols

/-- Every adjugate entry is a cofactor and hence obeys the minor envelope. -/
public theorem adjugate_height_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    matrixHeight A.adjugate ≤ n.factorial * matrixHeight A ^ n := by
  apply matrixHeight_le
  intro i j
  rw [_root_.Matrix.adjugate_fin_succ_eq_det_submatrix, Int.natAbs_mul]
  simpa using minor_natAbs_le_height_factorial A j.succAbove i.succAbove

/-- Cofactor matrices inherit the determinant/minor polynomial bit bound. -/
public theorem adjugate_bitLength_le {n : Nat}
    (A : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int) :
    matrixBitLength A.adjugate ≤
      determinantBitLengthBound n (matrixBitLength A) := by
  unfold matrixBitLength
  exact (Nat.size_le_size (adjugate_height_le A)).trans
    (factorial_mul_pow_size_le n (matrixHeight A))

/-- Dividing an exact nonzero integer scalar cannot increase matrix height. -/
public theorem matrixHeight_le_of_smul_eq {m n : Nat}
    {scalar : Int}
    {A B : _root_.Matrix (Fin m) (Fin n) Int}
    (scalar_ne : scalar ≠ 0) (equation : scalar • A = B) :
    matrixHeight A ≤ matrixHeight B := by
  apply matrixHeight_le
  intro i j
  have scalar_abs_pos : 1 ≤ scalar.natAbs :=
    Int.natAbs_pos.mpr scalar_ne
  calc
    (A i j).natAbs = 1 * (A i j).natAbs := by simp
    _ ≤ scalar.natAbs * (A i j).natAbs :=
      Nat.mul_le_mul_right (A i j).natAbs scalar_abs_pos
    _ = (scalar * A i j).natAbs := Int.natAbs_mul scalar (A i j) |>.symm
    _ = (B i j).natAbs := by
      have entry := congrFun (congrFun equation i) j
      exact congrArg Int.natAbs entry
    _ ≤ matrixHeight B := entry_natAbs_le_matrixHeight B i j

/--
Cramer's-rule height bound for a left multiplier.  The equation is converted
to `det A • U = H * adjugate A`; exact division by a nonzero determinant can
only decrease absolute values.
-/
public theorem leftMultiplier_height_le_of_mul_eq {n : Nat}
    (A U H : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (equation : U * A = H) (det_ne : A.det ≠ 0) :
    matrixHeight U ≤
      (n + 1) *
        (matrixHeight H * (n.factorial * matrixHeight A ^ n)) := by
  have scaled : A.det • U = H * A.adjugate := by
    calc
      A.det • U = U * (A.det • (1 :
          _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)) := by
        rw [_root_.Matrix.mul_smul, _root_.Matrix.mul_one]
      _ = U * (A * A.adjugate) := by
        rw [_root_.Matrix.mul_adjugate]
      _ = (U * A) * A.adjugate := by
        rw [_root_.Matrix.mul_assoc]
      _ = H * A.adjugate := by rw [equation]
  exact (matrixHeight_le_of_smul_eq det_ne scaled).trans <|
    (matrix_mul_height_le H A.adjugate).trans <| by
      gcongr
      exact adjugate_height_le A

/-- Polynomial coefficient-length bound for a left multiplier. -/
public theorem leftMultiplier_bitLength_le_of_mul_eq {n : Nat}
    (A U H : _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)
    (equation : U * A = H) (det_ne : A.det ≠ 0) :
    matrixBitLength U ≤
      Nat.size (n + 1) + matrixBitLength H +
        determinantBitLengthBound n (matrixBitLength A) := by
  have scaled : A.det • U = H * A.adjugate := by
    calc
      A.det • U = U * (A.det • (1 :
          _root_.Matrix (Fin (n + 1)) (Fin (n + 1)) Int)) := by
        rw [_root_.Matrix.mul_smul, _root_.Matrix.mul_one]
      _ = U * (A * A.adjugate) := by
        rw [_root_.Matrix.mul_adjugate]
      _ = (U * A) * A.adjugate := by
        rw [_root_.Matrix.mul_assoc]
      _ = H * A.adjugate := by rw [equation]
  exact (Nat.size_le_size (matrixHeight_le_of_smul_eq det_ne scaled)).trans <|
    (matrix_mul_bitLength_le H A.adjugate).trans <| by
      gcongr
      exact adjugate_bitLength_le A

end NormalForms.Research.KannanBachem.Hermite
