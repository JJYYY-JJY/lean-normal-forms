/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Bridge.MathlibPID.Basic
public import NormalForms.Matrix.Smith.Determinantal

/-!
# PID Signature Bridge

This module compares the intrinsic signature of a strong executable Smith
result with a canonical diagonal basis for the same column span.

Mathlib's raw `Module.Basis.SmithNormalForm` records a diagonal basis, but its
structure does not record normalization or a divisibility chain.  Those fields
alone are therefore not a canonical invariant: for example, diagonal factors
`2, 3` and `1, 6` can describe the same submodule.  `CanonicalPIDSmithBasis`
adds exactly the missing canonicality obligation before any coefficient
comparison is stated.

The bridge has three reader-facing levels:

* equality of associate-factor multisets over a PID;
* equality of normalized representative multisets;
* equality of sorted `Int.natAbs` lists.

No theorem compares mathlib's noncomputable coefficient function with the
executable list pointwise.
-/

@[expose] public section

namespace NormalForms.Bridge.MathlibPID

open NormalForms.Matrix.Smith

/-- The number of vectors in a Smith submodule basis is at most the ambient rank. -/
public theorem pidSmithBasisCount_le_rows
    {m k : Nat} {R : Type _} [CommRing R] [IsDomain R]
    {N : Submodule R (Fin m → R)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) k) :
    k ≤ m := by
  simpa using Fintype.card_le_of_embedding snf.f

/-- Every coefficient of a Smith submodule basis is nonzero. -/
public theorem pidSmithBasisCoeff_ne_zero
    {m k : Nat} {R : Type _} [CommRing R] [IsDomain R]
    {N : Submodule R (Fin m → R)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) k)
    (i : Fin k) :
    snf.a i ≠ 0 := by
  intro hi
  apply Module.Basis.ne_zero snf.bN i
  simpa [hi] using snf.snf i

/--
The rectangular diagonal matrix read from a mathlib Smith basis.

Its columns use the standard initial embedding into the ambient row type.
An internal row permutation relates this presentation to `snf.f`.
-/
public noncomputable def pidSmithBasisDiagonalMatrix
    {m k : Nat} {R : Type _} [CommRing R] [IsDomain R]
    {N : Submodule R (Fin m → R)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) k) :
    _root_.Matrix (Fin m) (Fin k) R :=
  fun i j =>
    if i = Fin.castLE (pidSmithBasisCount_le_rows snf) j
    then snf.a j else 0

namespace Internal

private noncomputable def pidSmithBasisRowPermutation
    {m k : Nat} {R : Type _} [CommRing R] [IsDomain R]
    {N : Submodule R (Fin m → R)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) k) :
    Equiv.Perm (Fin m) :=
  Classical.choose <|
    Equiv.Perm.exists_extending_pair
      (fun i : Fin k => Fin.castLE (pidSmithBasisCount_le_rows snf) i)
      snf.f
      (Fin.castLE_injective _)
      snf.f.injective

@[simp] private theorem pidSmithBasisRowPermutation_apply_castLE
    {m k : Nat} {R : Type _} [CommRing R] [IsDomain R]
    {N : Submodule R (Fin m → R)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) k)
    (i : Fin k) :
    pidSmithBasisRowPermutation snf
        (Fin.castLE (pidSmithBasisCount_le_rows snf) i) =
      snf.f i :=
  Classical.choose_spec
    (Equiv.Perm.exists_extending_pair
      (fun i : Fin k => Fin.castLE (pidSmithBasisCount_le_rows snf) i)
      snf.f
      (Fin.castLE_injective _)
      snf.f.injective) i

private noncomputable def pidSmithBasisAmbientBasis
    {m k : Nat} {R : Type _} [CommRing R] [IsDomain R]
    {N : Submodule R (Fin m → R)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) k) :
    Module.Basis (Fin m) R (Fin m → R) :=
  snf.bM.reindex (pidSmithBasisRowPermutation snf).symm

@[simp] private theorem pidSmithBasisAmbientBasis_apply_castLE
    {m k : Nat} {R : Type _} [CommRing R] [IsDomain R]
    {N : Submodule R (Fin m → R)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) k)
    (i : Fin k) :
    pidSmithBasisAmbientBasis snf
        (Fin.castLE (pidSmithBasisCount_le_rows snf) i) =
      snf.bM (snf.f i) := by
  simp [pidSmithBasisAmbientBasis]

private theorem pidSmithBasisDiagonalMatrix_eq_toMatrix_subtype
    {m k : Nat} {R : Type _} [CommRing R] [IsDomain R]
    {N : Submodule R (Fin m → R)}
    (snf : Module.Basis.SmithNormalForm N (Fin m) k) :
    pidSmithBasisDiagonalMatrix snf =
      LinearMap.toMatrix snf.bN (pidSmithBasisAmbientBasis snf) N.subtype := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change
    (if i = Fin.castLE (pidSmithBasisCount_le_rows snf) j then snf.a j else 0) =
      (pidSmithBasisAmbientBasis snf).repr
        ((snf.bN j : N) : Fin m → R) i
  rw [snf.snf j]
  have hb :
      snf.bM (snf.f j) =
        pidSmithBasisAmbientBasis snf
          (Fin.castLE (pidSmithBasisCount_le_rows snf) j) :=
    (pidSmithBasisAmbientBasis_apply_castLE snf j).symm
  have hrepr :
      (pidSmithBasisAmbientBasis snf).repr (snf.bM (snf.f j)) i =
        if i = Fin.castLE (pidSmithBasisCount_le_rows snf) j then 1 else 0 := by
    have hreprFinsupp :
        (pidSmithBasisAmbientBasis snf).repr (snf.bM (snf.f j)) =
          Finsupp.single
            (Fin.castLE (pidSmithBasisCount_le_rows snf) j) 1 := by
      rw [hb]
      exact (pidSmithBasisAmbientBasis snf).repr_self _
    rw [hreprFinsupp]
    rw [Finsupp.single_apply]
    by_cases hji : Fin.castLE (pidSmithBasisCount_le_rows snf) j = i
    · rw [if_pos hji, if_pos hji.symm]
    · rw [if_neg hji, if_neg (Ne.symm hji)]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hrepr]
  by_cases hij : i = Fin.castLE (pidSmithBasisCount_le_rows snf) j
  · simp only [hij, if_true, mul_one]
  · simp only [hij, if_false, mul_zero]

private noncomputable def pidSmithBasisMatrix
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k) :
    _root_.Matrix (Fin m) (Fin n) R :=
  LinearMap.toMatrix (Pi.basisFun R (Fin n))
    (pidSmithBasisAmbientBasis snf) A.mulVecLin

private theorem pidSmithBasisMatrix_eq_mul
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k) :
    pidSmithBasisMatrix A snf =
      (pidSmithBasisAmbientBasis snf).toMatrix
          (Pi.basisFun R (Fin m)) * A := by
  symm
  simpa only [pidSmithBasisMatrix, _root_.Matrix.toLin_eq_toLin',
    _root_.Matrix.toLin'_apply'] using
    (basis_toMatrix_mul
      (pidSmithBasisAmbientBasis snf)
      (Pi.basisFun R (Fin m))
      (Pi.basisFun R (Fin n))
      A)

private theorem pidSmithBasisMatrix_recover
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k) :
    A =
      (Pi.basisFun R (Fin m)).toMatrix
          (pidSmithBasisAmbientBasis snf) *
        pidSmithBasisMatrix A snf := by
  rw [pidSmithBasisMatrix_eq_mul, ← _root_.Matrix.mul_assoc,
    Module.Basis.toMatrix_mul_toMatrix_flip]
  simp

private noncomputable def pidSmithRangeSplitting
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (_snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k) :
    { rightInverse : (pidSmithColumnSpan A) →ₗ[R] (Fin n → R) //
      A.mulVecLin.rangeRestrict.comp rightInverse = LinearMap.id } := by
  letI : Module.Free R (pidSmithColumnSpan A) :=
    Module.Free.of_basis _snf.bN
  have h :
      ∃ rightInverse : (pidSmithColumnSpan A) →ₗ[R] (Fin n → R),
        A.mulVecLin.rangeRestrict.comp rightInverse = LinearMap.id :=
    A.mulVecLin.rangeRestrict.exists_rightInverse_of_surjective
      A.mulVecLin.range_rangeRestrict
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

private noncomputable def pidSmithGeneratorMatrix
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k) :
    _root_.Matrix (Fin k) (Fin n) R :=
  LinearMap.toMatrix (Pi.basisFun R (Fin n)) snf.bN
    A.mulVecLin.rangeRestrict

private noncomputable def pidSmithSectionMatrix
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k) :
    _root_.Matrix (Fin n) (Fin k) R :=
  LinearMap.toMatrix snf.bN (Pi.basisFun R (Fin n))
    (pidSmithRangeSplitting A snf).1

private theorem pidSmithBasisMatrix_eq_diagonal_mul_generator
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k) :
    pidSmithBasisMatrix A snf =
      pidSmithBasisDiagonalMatrix snf *
        pidSmithGeneratorMatrix A snf := by
  rw [pidSmithBasisDiagonalMatrix_eq_toMatrix_subtype]
  unfold pidSmithBasisMatrix pidSmithGeneratorMatrix
  rw [← LinearMap.toMatrix_comp]
  apply congrArg
  apply LinearMap.ext
  intro x
  rfl

private theorem pidSmithBasisDiagonalMatrix_eq_basis_mul_section
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k) :
    pidSmithBasisDiagonalMatrix snf =
      pidSmithBasisMatrix A snf * pidSmithSectionMatrix A snf := by
  rw [pidSmithBasisDiagonalMatrix_eq_toMatrix_subtype]
  rw [pidSmithBasisMatrix, pidSmithSectionMatrix,
    ← LinearMap.toMatrix_comp]
  apply congrArg
  apply LinearMap.ext
  intro x
  have hs := DFunLike.congr_fun (pidSmithRangeSplitting A snf).2 x
  exact (congrArg Subtype.val hs).symm

end Internal

/--
The original presentation matrix and a mathlib Smith basis diagonal generate
the same determinantal ideals.  The proof factors through the column-span
surjection and a projective right inverse; no square domain basis is assumed.
-/
public theorem determinantalIdealFin_eq_pidSmithBasisDiagonal
    {m n k : Nat} {R : Type _}
    [EuclideanDomain R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (snf : Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) k)
    (minorSize : Nat) :
    determinantalIdealFin A minorSize =
      determinantalIdealFin
        (pidSmithBasisDiagonalMatrix snf) minorSize := by
  apply le_antisymm
  · calc
      determinantalIdealFin A minorSize =
          determinantalIdealFin
            ((Pi.basisFun R (Fin m)).toMatrix
                (Internal.pidSmithBasisAmbientBasis snf) *
              Internal.pidSmithBasisMatrix A snf) minorSize := by
        rw [← Internal.pidSmithBasisMatrix_recover A snf]
      _ ≤ determinantalIdealFin
            (Internal.pidSmithBasisMatrix A snf) minorSize :=
        determinantalIdealFin_mul_left_le
          ((Pi.basisFun R (Fin m)).toMatrix
            (Internal.pidSmithBasisAmbientBasis snf))
          (Internal.pidSmithBasisMatrix A snf)
      _ ≤ determinantalIdealFin
            (pidSmithBasisDiagonalMatrix snf) minorSize := by
        rw [Internal.pidSmithBasisMatrix_eq_diagonal_mul_generator A snf]
        exact determinantalIdealFin_mul_right_le
          (pidSmithBasisDiagonalMatrix snf)
          (Internal.pidSmithGeneratorMatrix A snf)
  · calc
      determinantalIdealFin
          (pidSmithBasisDiagonalMatrix snf) minorSize ≤
          determinantalIdealFin
            (Internal.pidSmithBasisMatrix A snf) minorSize := by
        rw [Internal.pidSmithBasisDiagonalMatrix_eq_basis_mul_section A snf]
        exact determinantalIdealFin_mul_right_le
          (Internal.pidSmithBasisMatrix A snf)
          (Internal.pidSmithSectionMatrix A snf)
      _ ≤ determinantalIdealFin A minorSize := by
        rw [Internal.pidSmithBasisMatrix_eq_mul A snf]
        exact determinantalIdealFin_mul_left_le
          ((Internal.pidSmithBasisAmbientBasis snf).toMatrix
            (Pi.basisFun R (Fin m))) A

/--
A mathlib diagonal basis together with the canonicality facts absent from
`Module.Basis.SmithNormalForm` itself.
-/
public structure CanonicalPIDSmithBasis
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R) where
  count : Nat
  witness :
    Module.Basis.SmithNormalForm
      (pidSmithColumnSpan A) (Fin m) count
  canonical :
    IsSmithNormalFormFin (pidSmithBasisDiagonalMatrix witness)

/-- Canonical representatives of an intrinsic associate-factor multiset. -/
public noncomputable def pidNormalizedFactors
    {R : Type _} [MonoidWithZero R] [NormalizationMonoid R]
    (signature : SmithSignature R) :
    Multiset R :=
  signature.factors.map Associates.out

/-- Sorted absolute-value readout of an intrinsic integer Smith signature. -/
public noncomputable def pidIntNatAbsList
    (signature : SmithSignature Int) :
    List Nat :=
  (signature.factors.map fun factor => factor.out.natAbs).sort (· ≤ ·)

namespace CanonicalPIDSmithBasis

/--
Package mathlib's chosen Smith basis once the missing canonicality obligation
has been proved for its rectangular diagonal matrix.
-/
public noncomputable def ofMathlib
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    (A : _root_.Matrix (Fin m) (Fin n) R)
    (canonical :
      IsSmithNormalFormFin
        (pidSmithBasisDiagonalMatrix (pidSmithNormalFormData A).2)) :
    CanonicalPIDSmithBasis A where
  count := (pidSmithNormalFormData A).1
  witness := (pidSmithNormalFormData A).2
  canonical := canonical

/-- All nonzero mathlib coefficients, modulo units and without a zero tail. -/
public noncomputable def associateFactors
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    Multiset (Associates R) :=
  Multiset.ofList <| List.ofFn fun i =>
    Associates.mk (basis.witness.a i)

/-- The mathlib-basis signature, retaining the original matrix dimensions. -/
public noncomputable def signature
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    SmithSignature R where
  rows := m
  cols := n
  rank := basis.count
  factors := basis.associateFactors
  factor_card := by
    simp [associateFactors]
  nonzero := by
    intro factor hfactor
    rw [associateFactors, Multiset.mem_coe, List.mem_ofFn] at hfactor
    rcases hfactor with ⟨i, rfl⟩
    rw [Associates.mk_ne_zero]
    exact pidSmithBasisCoeff_ne_zero basis.witness i

@[simp] public theorem signature_rows
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    basis.signature.rows = m :=
  rfl

@[simp] public theorem signature_cols
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    basis.signature.cols = n :=
  rfl

@[simp] public theorem signature_rank
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    basis.signature.rank = basis.count :=
  rfl

/-- Normalized representatives of all mathlib basis coefficients. -/
public noncomputable def normalizedFactors
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    Multiset R :=
  Multiset.ofList <| List.ofFn fun i =>
    normalize (basis.witness.a i)

public theorem normalizedFactors_eq_signature
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    basis.normalizedFactors = pidNormalizedFactors basis.signature := by
  unfold normalizedFactors pidNormalizedFactors signature associateFactors
  rw [Multiset.map_coe]
  apply congrArg Multiset.ofList
  rw [List.map_ofFn]
  apply (List.ofFn_inj).2
  funext i
  exact (Associates.out_mk _).symm

/-- Sorted absolute values of all nonzero mathlib integer coefficients. -/
public noncomputable def intCoeffNatAbsList
    {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (basis : CanonicalPIDSmithBasis A) :
    List Nat :=
  (Multiset.ofList <| List.ofFn fun i =>
    (basis.witness.a i).natAbs).sort (· ≤ ·)

public theorem intCoeffNatAbsList_eq_signature
    {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (basis : CanonicalPIDSmithBasis A) :
    basis.intCoeffNatAbsList = pidIntNatAbsList basis.signature := by
  apply congrArg (fun factors : Multiset Nat => factors.sort (· ≤ ·))
  change
    Multiset.ofList
        (List.ofFn fun i => (basis.witness.a i).natAbs) =
      (Multiset.ofList
        (List.ofFn fun i => Associates.mk (basis.witness.a i))).map
          fun factor => factor.out.natAbs
  rw [Multiset.map_coe]
  apply congrArg Multiset.ofList
  rw [List.map_ofFn]
  apply (List.ofFn_inj).2
  funext i
  change
    (basis.witness.a i).natAbs =
      (Associates.mk (basis.witness.a i)).out.natAbs
  rw [Associates.out_mk]
  rw [← Int.abs_eq_normalize, Int.natAbs_abs]

theorem diagonalData_rank
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    (SmithData.ofSmithMatrix
      (pidSmithBasisDiagonalMatrix basis.witness)
      basis.canonical).rank = basis.count := by
  let data := SmithData.ofSmithMatrix
    (pidSmithBasisDiagonalMatrix basis.witness) basis.canonical
  have hkm : basis.count ≤ m :=
    pidSmithBasisCount_le_rows basis.witness
  apply Nat.le_antisymm
  · exact data.rank_le.trans (Nat.min_le_right m basis.count)
  · by_contra hle
    have hlt : data.rank < basis.count := Nat.lt_of_not_ge hle
    have hmin : Nat.min m basis.count = basis.count :=
      Nat.min_eq_right hkm
    let i : Fin (Nat.min m basis.count) :=
      ⟨data.rank, hmin.symm ▸ hlt⟩
    have hzero : data.diagonal i = 0 :=
      data.zero_tail i (Nat.le_refl data.rank)
    have hdiag :
        data.diagonal i =
          basis.witness.a (Fin.cast hmin i) := by
      change
        pidSmithBasisDiagonalMatrix basis.witness
            (Fin.castLE (Nat.min_le_left m basis.count) i)
            (Fin.castLE (Nat.min_le_right m basis.count) i) =
          basis.witness.a (Fin.cast hmin i)
      unfold pidSmithBasisDiagonalMatrix
      rw [if_pos]
      · congr 1
      · apply Fin.ext
        rfl
    exact pidSmithBasisCoeff_ne_zero basis.witness (Fin.cast hmin i)
      (hdiag.symm.trans hzero)

theorem diagonalData_factors
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (basis : CanonicalPIDSmithBasis A) :
    (SmithData.ofSmithMatrix
        (pidSmithBasisDiagonalMatrix basis.witness)
        basis.canonical).signature.factors =
      basis.associateFactors := by
  let data := SmithData.ofSmithMatrix
    (pidSmithBasisDiagonalMatrix basis.witness) basis.canonical
  change
    Multiset.ofList (List.ofFn data.factorAt) =
      Multiset.ofList
        (List.ofFn fun i => Associates.mk (basis.witness.a i))
  apply congrArg Multiset.ofList
  apply List.ext_get
  · simp only [List.length_ofFn]
    exact diagonalData_rank basis
  · intro q hqData hqBasis
    simp only [List.length_ofFn] at hqData hqBasis
    rw [List.get_ofFn, List.get_ofFn]
    apply congrArg Associates.mk
    unfold SmithData.factorAt
    change
      pidSmithBasisDiagonalMatrix basis.witness
          (Fin.castLE (Nat.min_le_left m basis.count)
            (Fin.castLE data.rank_le ⟨q, hqData⟩))
          (Fin.castLE (Nat.min_le_right m basis.count)
            (Fin.castLE data.rank_le ⟨q, hqData⟩)) =
        basis.witness.a ⟨q, hqBasis⟩
    unfold pidSmithBasisDiagonalMatrix
    rw [if_pos]
    · congr 1
    · apply Fin.ext
      rfl

/--
General PID bridge: canonical mathlib factors and executable factors agree as
a multiset of associate classes, with rank and dimensions included.
-/
public theorem smithSignature_eq
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (result : SNFResultFin A)
    (basis : CanonicalPIDSmithBasis A) :
    result.smithSignature = basis.signature := by
  let certificate :
      NormalForms.Matrix.Certificates.TwoSidedCertificate A :=
    { U := result.U
      U_cert := result.U_cert
      result := result.S
      V := result.V
      V_cert := result.V_cert
      equation := result.equation }
  have hdet :
      ∀ minorSize,
        determinantalIdealFin result.S minorSize =
          determinantalIdealFin
            (pidSmithBasisDiagonalMatrix basis.witness) minorSize := by
    intro minorSize
    exact
      (determinantalIdealFin_eq_of_certificate certificate minorSize).symm.trans
        (determinantalIdealFin_eq_pidSmithBasisDiagonal
          A basis.witness minorSize)
  apply SmithSignature.ext
  · rfl
  · rfl
  · change
      (SmithData.ofSmithMatrix result.S result.isSmith).rank =
        basis.count
    exact
      (smithRank_eq_of_determinantalIdeals
        result.isSmith basis.canonical hdet).trans
          (diagonalData_rank basis)
  · change
      (SmithData.ofSmithMatrix result.S result.isSmith).signature.factors =
        basis.associateFactors
    exact
      (smithFactors_eq_of_determinantalIdeals
        result.isSmith basis.canonical hdet).trans
          (diagonalData_factors basis)

/-- Canonical Euclidean-domain bridge: normalized multisets agree. -/
public theorem normalizedFactors_eq
    {m n : Nat} {R : Type _}
    [EuclideanDomain R] [NormalizationMonoid R] [DecidableEq R]
    {A : _root_.Matrix (Fin m) (Fin n) R}
    (result : SNFResultFin A)
    (basis : CanonicalPIDSmithBasis A) :
    pidNormalizedFactors result.smithSignature =
      basis.normalizedFactors := by
  rw [smithSignature_eq result basis]
  exact (normalizedFactors_eq_signature basis).symm

/-- Integer bridge: sorted absolute-value coefficient lists agree. -/
public theorem intNatAbsList_eq
    {m n : Nat}
    {A : _root_.Matrix (Fin m) (Fin n) Int}
    (result : SNFResultFin A)
    (basis : CanonicalPIDSmithBasis A) :
    pidIntNatAbsList result.smithSignature =
      basis.intCoeffNatAbsList := by
  rw [smithSignature_eq result basis]
  exact (intCoeffNatAbsList_eq_signature basis).symm

end CanonicalPIDSmithBasis

end NormalForms.Bridge.MathlibPID
