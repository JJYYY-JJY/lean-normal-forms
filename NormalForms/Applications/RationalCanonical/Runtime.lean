/-
Copyright (c) 2026 Junye Ji. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junye Ji
-/
module

public import NormalForms.Applications.RationalCanonical.Presentation
public import NormalForms.Matrix.PolynomialRat
public import Mathlib.Algebra.Ring.Equiv
import all NormalForms.Euclidean.Rat
import all NormalForms.Euclidean.PolynomialRat

/-!
# Rational-Polynomial Runtime Bridge

The strict executable core uses a choice-free rational and polynomial
dictionary.  Consequently its runtime polynomial type is not definitionally
the standard `Rat[X]` type.  This module gives the coefficient-preserving
equivalence between them and proves that it preserves addition and
multiplication.

The bridge belongs to the independently versioned rational-canonical
application.  Its implementation-only rational-operation lemmas are imported
with `import all`, so the frozen version 1 core facade gains no declarations.
-/

namespace NormalForms.RationalCanonical

open Polynomial
open PolynomialRatRuntime

private def runtimeCoefficientFinsupp (p : RuntimePolynomial) :
    @Finsupp Nat Rat PolynomialRatRuntime.cleanSemiringRat.toZero :=
  @AddMonoidAlgebra.coeff Rat Nat
    PolynomialRatRuntime.cleanSemiringRat
    (@Polynomial.toFinsupp Rat
      PolynomialRatRuntime.cleanSemiringRat p)

private def runtimeCoefficient
    (p : RuntimePolynomial) (degree : Nat) : Rat :=
  runtimeCoefficientFinsupp p degree

private theorem runtimeCoefficient_add
    (p q : RuntimePolynomial) (degree : Nat) :
    runtimeCoefficient (PolynomialRatRuntime.add p q) degree =
      @Add.add Rat PolynomialRatRuntime.cleanSemiringRat.toAdd
        (runtimeCoefficient p degree)
        (runtimeCoefficient q degree) := by
  change
    @Polynomial.coeff Rat PolynomialRatRuntime.cleanSemiringRat
        (PolynomialRatRuntime.add p q) degree = _
  rw [PolynomialRatRuntime.add_eq,
    @Polynomial.coeff_add Rat
      PolynomialRatRuntime.cleanSemiringRat]
  rfl

private theorem runtimeCoefficient_mul
    (p q : RuntimePolynomial) (degree : Nat) :
    runtimeCoefficient (PolynomialRatRuntime.mul p q) degree =
      @Finset.sum (Nat × Nat) Rat
        PolynomialRatRuntime.cleanSemiringRat.toAddCommMonoid
        (Finset.HasAntidiagonal.antidiagonal degree)
        (fun indices =>
          @Mul.mul Rat PolynomialRatRuntime.cleanSemiringRat.toMul
            (runtimeCoefficient p indices.1)
            (runtimeCoefficient q indices.2)) := by
  change
    @Polynomial.coeff Rat PolynomialRatRuntime.cleanSemiringRat
        (PolynomialRatRuntime.mul p q) degree = _
  rw [PolynomialRatRuntime.mul_eq,
    @Polynomial.coeff_mul Rat
      PolynomialRatRuntime.cleanSemiringRat]
  rfl

private def runtimeFinsuppToStandard
    (p : RuntimePolynomial) : Nat →₀ Rat where
  support := (runtimeCoefficientFinsupp p).support
  toFun := runtimeCoefficient p
  mem_support_toFun := by
    intro degree
    change
      degree ∈ (runtimeCoefficientFinsupp p).support ↔
        runtimeCoefficient p degree ≠ (0 : Rat)
    rw [← ConstructiveRat.field_zero_eq_standard]
    exact Finsupp.mem_support_iff

private def runtimeToPolynomial
    (p : RuntimePolynomial) : Rat[X] :=
  .ofFinsupp (.ofCoeff (runtimeFinsuppToStandard p))

@[simp]
private theorem runtimeToPolynomial_coeff
    (p : RuntimePolynomial) (degree : Nat) :
    (runtimeToPolynomial p).coeff degree =
      runtimeCoefficient p degree :=
  rfl

private def standardFinsuppToRuntime
    (p : Rat[X]) :
    @Finsupp Nat Rat PolynomialRatRuntime.cleanSemiringRat.toZero where
  support := p.toFinsupp.coeff.support
  toFun := fun degree => p.coeff degree
  mem_support_toFun := by
    intro degree
    change
      degree ∈ p.support ↔
        p.coeff degree ≠
          @Zero.zero Rat
            PolynomialRatRuntime.cleanSemiringRat.toZero
    rw [ConstructiveRat.field_zero_eq_standard]
    exact Polynomial.mem_support_iff

private def polynomialToRuntime
    (p : Rat[X]) : RuntimePolynomial :=
  @Polynomial.ofFinsupp Rat
    PolynomialRatRuntime.cleanSemiringRat
    (@AddMonoidAlgebra.ofCoeff Rat Nat
      PolynomialRatRuntime.cleanSemiringRat
      (standardFinsuppToRuntime p))

@[simp]
private theorem polynomialToRuntime_coeff
    (p : Rat[X]) (degree : Nat) :
    runtimeCoefficient (polynomialToRuntime p) degree =
      p.coeff degree :=
  rfl

/--
The coefficient-preserving equivalence from the strict executable polynomial
type to standard mathlib rational polynomials.
-/
public def runtimePolynomialEquiv :
    RuntimePolynomial ≃ Rat[X] where
  toFun := runtimeToPolynomial
  invFun := polynomialToRuntime
  left_inv := by
    intro p
    apply @Polynomial.coeff_injective Rat
      PolynomialRatRuntime.cleanSemiringRat
    funext degree
    exact polynomialToRuntime_coeff
      (runtimeToPolynomial p) degree
  right_inv := by
    intro p
    apply Polynomial.coeff_injective
    funext degree
    exact runtimeToPolynomial_coeff
      (polynomialToRuntime p) degree

@[simp]
public theorem runtimePolynomialEquiv_coeff
    (p : RuntimePolynomial) (degree : Nat) :
    (runtimePolynomialEquiv p).coeff degree =
      @Polynomial.coeff Rat
        PolynomialRatRuntime.cleanSemiringRat p degree := by
  change (runtimeToPolynomial p).coeff degree = _
  rw [runtimeToPolynomial_coeff]
  rfl

@[simp]
public theorem runtimePolynomialEquiv_support
    (p : RuntimePolynomial) :
    (runtimePolynomialEquiv p).support =
      @Polynomial.support Rat
        PolynomialRatRuntime.cleanSemiringRat p := by
  change
    (runtimeFinsuppToStandard p).support =
      (runtimeCoefficientFinsupp p).support
  rfl

@[simp]
public theorem runtimePolynomialEquiv_natDegree
    (p : RuntimePolynomial) :
    (runtimePolynomialEquiv p).natDegree =
      @Polynomial.natDegree Rat
        PolynomialRatRuntime.cleanSemiringRat p := by
  unfold Polynomial.natDegree Polynomial.degree
  rw [runtimePolynomialEquiv_support]

@[simp]
public theorem runtimePolynomialEquiv_leadingCoeff
    (p : RuntimePolynomial) :
    (runtimePolynomialEquiv p).leadingCoeff =
      @Polynomial.leadingCoeff Rat
        PolynomialRatRuntime.cleanSemiringRat p := by
  unfold Polynomial.leadingCoeff
  rw [runtimePolynomialEquiv_coeff,
    runtimePolynomialEquiv_natDegree]

@[simp]
public theorem runtimePolynomialEquiv_zero :
    runtimePolynomialEquiv PolynomialRatRuntime.zero = 0 := by
  apply Polynomial.coeff_injective
  funext degree
  rw [runtimePolynomialEquiv_coeff]
  simp only [PolynomialRatRuntime.zero_eq, Polynomial.coeff_zero]
  exact ConstructiveRat.field_zero_eq_standard

@[simp]
public theorem runtimePolynomialEquiv_runtimeZero :
    runtimePolynomialEquiv
        (@Zero.zero RuntimePolynomial
          runtimeAlgebra.euclidean.toZero) =
      0 := by
  rw [PolynomialRatRuntime.runtimeAlgebra_zero_eq,
    runtimePolynomialEquiv_zero]

@[simp]
public theorem runtimePolynomialEquiv_one :
    runtimePolynomialEquiv PolynomialRatRuntime.one = 1 := by
  apply Polynomial.coeff_injective
  funext degree
  rw [runtimePolynomialEquiv_coeff]
  simp only [PolynomialRatRuntime.one_eq, Polynomial.coeff_one]
  split
  · exact ConstructiveRat.field_one_eq_standard
  · exact ConstructiveRat.field_zero_eq_standard

@[simp]
public theorem runtimePolynomialEquiv_C (a : Rat) :
    runtimePolynomialEquiv (PolynomialRatRuntime.C a) =
      Polynomial.C a := by
  apply Polynomial.coeff_injective
  funext degree
  rw [runtimePolynomialEquiv_coeff]
  simp only [PolynomialRatRuntime.C_eq, Polynomial.coeff_C]
  split
  · rfl
  · exact ConstructiveRat.field_zero_eq_standard

private theorem cleanFinsetSum_eq_standard
    {α : Type u} (support : Finset α) (f : α → Rat) :
    @Finset.sum α Rat
        PolynomialRatRuntime.cleanSemiringRat.toAddCommMonoid
        support f =
      ∑ x ∈ support, f x := by
  classical
  induction support using Finset.induction_on with
  | empty =>
      change
        @Zero.zero Rat
            PolynomialRatRuntime.cleanSemiringRat.toZero =
          (0 : Rat)
      exact ConstructiveRat.field_zero_eq_standard
  | @insert a support absent ih =>
      rw [@Finset.sum_insert α Rat support a
        PolynomialRatRuntime.cleanSemiringRat.toAddCommMonoid
        f inferInstance absent]
      rw [Finset.sum_insert absent]
      rw [ih]
      exact ConstructiveRat.field_add_eq_standard _ _

/-- The runtime equivalence preserves polynomial addition. -/
public theorem runtimePolynomialEquiv_add
    (p q : RuntimePolynomial) :
    runtimePolynomialEquiv (PolynomialRatRuntime.add p q) =
      runtimePolynomialEquiv p + runtimePolynomialEquiv q := by
  apply Polynomial.coeff_injective
  funext degree
  change
    (runtimeToPolynomial
        (PolynomialRatRuntime.add p q)).coeff degree =
      (runtimeToPolynomial p +
        runtimeToPolynomial q).coeff degree
  rw [runtimeToPolynomial_coeff, Polynomial.coeff_add,
    runtimeToPolynomial_coeff, runtimeToPolynomial_coeff,
    runtimeCoefficient_add]
  exact ConstructiveRat.field_add_eq_standard _ _

/-- The runtime equivalence preserves polynomial multiplication. -/
public theorem runtimePolynomialEquiv_mul
    (p q : RuntimePolynomial) :
    runtimePolynomialEquiv (PolynomialRatRuntime.mul p q) =
      runtimePolynomialEquiv p * runtimePolynomialEquiv q := by
  apply Polynomial.coeff_injective
  funext degree
  change
    (runtimeToPolynomial
        (PolynomialRatRuntime.mul p q)).coeff degree =
      (runtimeToPolynomial p *
        runtimeToPolynomial q).coeff degree
  rw [runtimeToPolynomial_coeff, Polynomial.coeff_mul,
    runtimeCoefficient_mul]
  calc
    @Finset.sum (Nat × Nat) Rat
          PolynomialRatRuntime.cleanSemiringRat.toAddCommMonoid
          (Finset.HasAntidiagonal.antidiagonal degree)
          (fun indices =>
            @Mul.mul Rat
              PolynomialRatRuntime.cleanSemiringRat.toMul
              (runtimeCoefficient p indices.1)
              (runtimeCoefficient q indices.2)) =
        ∑ indices ∈
            Finset.HasAntidiagonal.antidiagonal degree,
          @Mul.mul Rat
            PolynomialRatRuntime.cleanSemiringRat.toMul
            (runtimeCoefficient p indices.1)
            (runtimeCoefficient q indices.2) :=
      cleanFinsetSum_eq_standard _ _
    _ =
        ∑ indices ∈
            Finset.HasAntidiagonal.antidiagonal degree,
          runtimeCoefficient p indices.1 *
            runtimeCoefficient q indices.2 := by
      apply Finset.sum_congr rfl
      intro indices _
      exact ConstructiveRat.field_mul_eq_standard _ _
    _ = _ := by
      simp only [runtimeToPolynomial_coeff]

/--
The runtime bridge as a ring equivalence for the exact coherent ring
dictionary used by the executable Smith kernel.
-/
public def runtimePolynomialRingEquiv :
    @RingEquiv RuntimePolynomial Rat[X]
      runtimeAlgebra.euclidean.toCommRing.toMul inferInstance
      runtimeAlgebra.euclidean.toCommRing.toAdd inferInstance :=
  @RingEquiv.mk RuntimePolynomial Rat[X]
    runtimeAlgebra.euclidean.toCommRing.toMul inferInstance
    runtimeAlgebra.euclidean.toCommRing.toAdd inferInstance
    runtimePolynomialEquiv
    (fun p q => by
      change runtimePolynomialEquiv
          (@Mul.mul RuntimePolynomial
            runtimeAlgebra.euclidean.toCommRing.toMul p q) =
        runtimePolynomialEquiv p * runtimePolynomialEquiv q
      rw [PolynomialRatRuntime.runtimeAlgebra_mul_eq]
      exact runtimePolynomialEquiv_mul p q)
    (fun p q => by
      change runtimePolynomialEquiv
          (@Add.add RuntimePolynomial
            runtimeAlgebra.euclidean.toCommRing.toAdd p q) =
        runtimePolynomialEquiv p + runtimePolynomialEquiv q
      rw [PolynomialRatRuntime.runtimeAlgebra_add_eq]
      exact runtimePolynomialEquiv_add p q)

/--
The same coefficient bridge, with source operations selected through the
`CommSemiring` projection used by `MatrixInverseCertificate`.

Keeping this coherence adapter explicit prevents Lean from mixing the
runtime polynomial dictionary with the standard polynomial dictionary while
transporting matrix products.
-/
public def runtimePolynomialCertificateRingEquiv :
    @RingEquiv RuntimePolynomial Rat[X]
      (@instDistribOfSemiring RuntimePolynomial
        runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul
      inferInstance
      (@Semiring.toAddCommMonoid RuntimePolynomial
        runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toAdd
      inferInstance :=
  @RingEquiv.mk RuntimePolynomial Rat[X]
    (@instDistribOfSemiring RuntimePolynomial
      runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul
    inferInstance
    (@Semiring.toAddCommMonoid RuntimePolynomial
      runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toAdd
    inferInstance
    runtimePolynomialEquiv
    (fun p q => by
      change runtimePolynomialEquiv
          (@Mul.mul RuntimePolynomial
            (@instDistribOfSemiring RuntimePolynomial
              runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul p q) =
        runtimePolynomialEquiv p * runtimePolynomialEquiv q
      rw [PolynomialRatRuntime.runtimeAlgebra_commSemiring_mul_eq]
      exact runtimePolynomialEquiv_mul p q)
    (fun p q => by
      change runtimePolynomialEquiv
          (@Add.add RuntimePolynomial
            (@Semiring.toAddCommMonoid RuntimePolynomial
              runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toAdd p q) =
        runtimePolynomialEquiv p + runtimePolynomialEquiv q
      rw [PolynomialRatRuntime.runtimeAlgebra_commSemiring_add_eq]
      exact runtimePolynomialEquiv_add p q)

@[simp]
public theorem runtimePolynomialCertificateRingEquiv_apply
    (p : RuntimePolynomial) :
    runtimePolynomialCertificateRingEquiv p =
      runtimePolynomialEquiv p := by
  rfl

@[simp]
public theorem runtimePolynomialEquiv_certificateZero :
    runtimePolynomialEquiv
        (@Zero.zero RuntimePolynomial
          (@Semiring.toAddCommMonoid RuntimePolynomial
            runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toZero) =
      0 := by
  rw [PolynomialRatRuntime.runtimeAlgebra_commSemiring_zero_eq,
    runtimePolynomialEquiv_zero]

@[simp]
public theorem runtimePolynomialEquiv_certificateMatrixZero :
    runtimePolynomialEquiv
        (@Zero.zero RuntimePolynomial
          (@MulZeroClass.toZero RuntimePolynomial
            (@instMulZeroClassOfSemiring RuntimePolynomial
              runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring))) =
      0 := by
  rw [PolynomialRatRuntime.runtimeAlgebra_certificate_zero_eq,
    runtimePolynomialEquiv_zero]

@[simp]
public theorem runtimePolynomialEquiv_certificateMatrixOneScalar :
    runtimePolynomialEquiv
        (@One.one RuntimePolynomial
          (@AddMonoidWithOne.toOne RuntimePolynomial
            (@AddGroupWithOne.toAddMonoidWithOne RuntimePolynomial
              (@Ring.toAddGroupWithOne RuntimePolynomial
                runtimeAlgebra.euclidean.toCommRing.toRing)))) =
      1 := by
  rw [PolynomialRatRuntime.runtimeAlgebra_certificate_one_eq,
    runtimePolynomialEquiv_one]

/-- Mapping the source identity matrix used by inverse certificates gives the
standard polynomial identity matrix. -/
public theorem runtimePolynomialEquiv_certificateMatrixOne
    {n : Nat} :
    (@One.one
        (_root_.Matrix (Fin n) (Fin n) RuntimePolynomial)
        (@Matrix.one (Fin n) RuntimePolynomial
          inferInstance
          (@MulZeroClass.toZero RuntimePolynomial
            (@instMulZeroClassOfSemiring RuntimePolynomial
              runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring))
          (@AddMonoidWithOne.toOne RuntimePolynomial
            (@AddGroupWithOne.toAddMonoidWithOne RuntimePolynomial
              (@Ring.toAddGroupWithOne RuntimePolynomial
                runtimeAlgebra.euclidean.toCommRing.toRing))))).map
        runtimePolynomialEquiv =
      (1 : _root_.Matrix (Fin n) (Fin n) Rat[X]) := by
  apply _root_.Matrix.ext
  intro i j
  change
    runtimePolynomialEquiv
        (if i = j then
          @One.one RuntimePolynomial
            (@AddMonoidWithOne.toOne RuntimePolynomial
              (@AddGroupWithOne.toAddMonoidWithOne RuntimePolynomial
                (@Ring.toAddGroupWithOne RuntimePolynomial
                  runtimeAlgebra.euclidean.toCommRing.toRing)))
        else
          @Zero.zero RuntimePolynomial
            (@MulZeroClass.toZero RuntimePolynomial
              (@instMulZeroClassOfSemiring RuntimePolynomial
                runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring))) =
      if i = j then 1 else 0
  by_cases h : i = j
  · simp only [h, ↓reduceIte]
    exact runtimePolynomialEquiv_certificateMatrixOneScalar
  · simp only [h, ↓reduceIte]
    exact runtimePolynomialEquiv_certificateMatrixZero

/-- The coefficient bridge preserves the multiplication instance used by the
divisibility field of the runtime Euclidean domain. -/
public theorem runtimePolynomialEquiv_divisibilityMul
    (p q : RuntimePolynomial) :
    runtimePolynomialEquiv
        (@Mul.mul RuntimePolynomial
          (let sourceRing :=
            runtimeAlgebra.euclidean.toCommRing.toNonUnitalCommRing
          let source := sourceRing.toNonUnitalCommSemiring
          source.toSemigroupWithZero.toMul)
          p q) =
      runtimePolynomialEquiv p * runtimePolynomialEquiv q := by
  rw [PolynomialRatRuntime.runtimeAlgebra_divisibility_mul_eq,
    runtimePolynomialEquiv_mul]

/--
Mapping a square matrix product formed with the exact `CommSemiring`
projection used by `MatrixInverseCertificate` agrees with standard polynomial
matrix multiplication.
-/
public theorem runtimePolynomialEquiv_certificateMatrixMul
    {n : Nat}
    (A B : _root_.Matrix (Fin n) (Fin n) RuntimePolynomial) :
    (@HMul.hMul
        (_root_.Matrix (Fin n) (Fin n) RuntimePolynomial)
        (_root_.Matrix (Fin n) (Fin n) RuntimePolynomial)
        (_root_.Matrix (Fin n) (Fin n) RuntimePolynomial)
        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
          (Fin n) (Fin n) (Fin n) RuntimePolynomial
          (constructiveFinFintype n)
          (@instDistribOfSemiring RuntimePolynomial
            runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul
          (@Semiring.toAddCommMonoid RuntimePolynomial
            runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring))
        A B).map runtimePolynomialEquiv =
      A.map runtimePolynomialEquiv *
        B.map runtimePolynomialEquiv := by
  let sourceAddCommMonoid : AddCommMonoid RuntimePolynomial :=
    @Semiring.toAddCommMonoid RuntimePolynomial
      runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring
  letI : AddCommMonoid RuntimePolynomial := sourceAddCommMonoid
  letI : Add RuntimePolynomial := sourceAddCommMonoid.toAdd
  letI : Zero RuntimePolynomial := sourceAddCommMonoid.toZero
  letI : Mul RuntimePolynomial :=
    (@instDistribOfSemiring RuntimePolynomial
      runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul
  apply _root_.Matrix.ext
  intro i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  simp only [← runtimePolynomialCertificateRingEquiv_apply]
  let termSource (k : Fin n) := A i k * B k j
  let termTarget (k : Fin n) :=
    runtimePolynomialCertificateRingEquiv (A i k) *
      runtimePolynomialCertificateRingEquiv (B k j)
  have hterm (k : Fin n) :
      runtimePolynomialCertificateRingEquiv (termSource k) =
        termTarget k := by
    exact
      @RingEquiv.map_mul' RuntimePolynomial Rat[X]
        (@instDistribOfSemiring RuntimePolynomial
          runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul
        inferInstance
        (@Semiring.toAddCommMonoid RuntimePolynomial
          runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toAdd
        inferInstance
        runtimePolynomialCertificateRingEquiv _ _
  have hsum (s : Finset (Fin n)) :
      runtimePolynomialCertificateRingEquiv
          (∑ k ∈ s, termSource k) =
        ∑ k ∈ s, termTarget k := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        rw [runtimePolynomialCertificateRingEquiv_apply]
        change
          runtimePolynomialEquiv
              (@Zero.zero RuntimePolynomial
                (@Semiring.toAddCommMonoid RuntimePolynomial
                  runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toZero) =
            0
        exact runtimePolynomialEquiv_certificateZero
    | @insert k s absent ih =>
        rw [Finset.sum_insert absent, Finset.sum_insert absent]
        calc
          runtimePolynomialCertificateRingEquiv
                (termSource k + ∑ x ∈ s, termSource x) =
              runtimePolynomialCertificateRingEquiv (termSource k) +
                runtimePolynomialCertificateRingEquiv
                  (∑ x ∈ s, termSource x) :=
            @RingEquiv.map_add' RuntimePolynomial Rat[X]
              (@instDistribOfSemiring RuntimePolynomial
                runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toMul
              inferInstance
              (@Semiring.toAddCommMonoid RuntimePolynomial
                runtimeAlgebra.euclidean.toCommRing.toCommSemiring.toSemiring).toAdd
              inferInstance
              runtimePolynomialCertificateRingEquiv _ _
          _ = termTarget k + ∑ x ∈ s, termTarget x := by
            rw [hterm, ih]
  simpa only [termSource, termTarget] using hsum Finset.univ

@[simp]
public theorem runtimePolynomialRingEquiv_apply
    (p : RuntimePolynomial) :
    runtimePolynomialRingEquiv p =
      runtimePolynomialEquiv p := by
  rfl

@[simp]
public theorem runtimePolynomialRingEquiv_mapMatrix
    {n : Nat}
    (M : _root_.Matrix (Fin n) (Fin n) RuntimePolynomial) :
    @RingEquiv.mapMatrix (Fin n) RuntimePolynomial Rat[X]
        inferInstance inferInstance
        runtimeAlgebra.euclidean.toNonAssocSemiring
        inferInstance runtimePolynomialRingEquiv M =
      M.map runtimePolynomialEquiv := by
  apply _root_.Matrix.ext
  intro i j
  change
    runtimePolynomialRingEquiv (M i j) =
      runtimePolynomialEquiv (M i j)
  exact runtimePolynomialRingEquiv_apply (M i j)

/-- The coefficient bridge commutes with determinants. -/
public theorem runtimePolynomialEquiv_det
    {n : Nat}
    (M : _root_.Matrix (Fin n) (Fin n) RuntimePolynomial) :
    runtimePolynomialEquiv
        (@_root_.Matrix.det (Fin n) inferInstance inferInstance
          RuntimePolynomial runtimeAlgebra.euclidean.toCommRing M) =
      (M.map runtimePolynomialEquiv).det := by
  calc
    runtimePolynomialEquiv
        (@_root_.Matrix.det (Fin n) inferInstance inferInstance
          RuntimePolynomial runtimeAlgebra.euclidean.toCommRing M) =
        runtimePolynomialRingEquiv
          (@_root_.Matrix.det (Fin n)
            inferInstance inferInstance RuntimePolynomial
            runtimeAlgebra.euclidean.toCommRing M) :=
      (runtimePolynomialRingEquiv_apply _).symm
    _ =
        (@RingEquiv.mapMatrix (Fin n)
          RuntimePolynomial Rat[X]
          inferInstance inferInstance
          runtimeAlgebra.euclidean.toNonAssocSemiring inferInstance
          runtimePolynomialRingEquiv M).det := by
            exact
              @RingEquiv.map_det (Fin n)
                inferInstance inferInstance
                RuntimePolynomial
                runtimeAlgebra.euclidean.toCommRing
                Rat[X] inferInstance
                runtimePolynomialRingEquiv M
    _ = (M.map runtimePolynomialEquiv).det :=
      congrArg _root_.Matrix.det
        (runtimePolynomialRingEquiv_mapMatrix M)

/--
The multiplicative part of the runtime bridge with the source `MulOne`
dictionary made explicit.  This form transports unit and association proofs
without relying on ambient instance selection.
-/
public def runtimePolynomialMonoidHom :
    @MonoidHom RuntimePolynomial Rat[X]
      runtimeAlgebra.euclidean.toMulOne inferInstance :=
  @MonoidHom.mk RuntimePolynomial Rat[X]
    runtimeAlgebra.euclidean.toMulOne inferInstance
    (@OneHom.mk RuntimePolynomial Rat[X]
      runtimeAlgebra.euclidean.toOne inferInstance
      runtimePolynomialEquiv
      (by
        change runtimePolynomialEquiv
            (@One.one RuntimePolynomial
              runtimeAlgebra.euclidean.toOne) = 1
        rw [PolynomialRatRuntime.runtimeAlgebra_one_eq,
          runtimePolynomialEquiv_one]))
    (by
      intro p q
      change runtimePolynomialEquiv
          (@Mul.mul RuntimePolynomial
            runtimeAlgebra.euclidean.toMul p q) =
        runtimePolynomialEquiv p * runtimePolynomialEquiv q
      rw [PolynomialRatRuntime.runtimeAlgebra_mul_eq]
      exact runtimePolynomialEquiv_mul p q)

@[simp]
public theorem runtimePolynomialMonoidHom_apply
    (p : RuntimePolynomial) :
    runtimePolynomialMonoidHom p =
    runtimePolynomialEquiv p := by
  rfl

/-- The coefficient bridge preserves association by mapping its unit witness. -/
public theorem runtimePolynomialEquiv_associated
    {p q : RuntimePolynomial}
    (h :
      @Associated RuntimePolynomial
        runtimeAlgebra.euclidean.toMonoid p q) :
    Associated (runtimePolynomialEquiv p)
      (runtimePolynomialEquiv q) := by
  simpa only [runtimePolynomialMonoidHom_apply] using
    @Associated.map RuntimePolynomial Rat[X]
      runtimeAlgebra.euclidean.toMonoid inferInstance
      (@MonoidHom RuntimePolynomial Rat[X]
        runtimeAlgebra.euclidean.toMulOne inferInstance)
      inferInstance inferInstance
      runtimePolynomialMonoidHom _ _ h

private theorem runtimePolynomialEquiv_executableNormalize
    (p : RuntimePolynomial) :
    runtimePolynomialEquiv (PolynomialRatRuntime.normalize p) =
      normalize (runtimePolynomialEquiv p) := by
  unfold PolynomialRatRuntime.normalize
  split
  case isTrue hzero =>
    have hp : p = PolynomialRatRuntime.zero :=
      (PolynomialRatRuntime.isZeroB_eq_true_iff p).mp hzero
    subst p
    rw [runtimePolynomialEquiv_zero, normalize_zero]
  case isFalse hzero =>
    have hp : p ≠ PolynomialRatRuntime.zero :=
      fun h =>
        hzero
          ((PolynomialRatRuntime.isZeroB_eq_true_iff p).mpr h)
    have hpTarget : runtimePolynomialEquiv p ≠ 0 := by
      intro h
      have h' :
          runtimePolynomialEquiv p =
            runtimePolynomialEquiv
              PolynomialRatRuntime.zero :=
        h.trans runtimePolynomialEquiv_zero.symm
      exact hp (runtimePolynomialEquiv.injective h')
    rw [runtimePolynomialEquiv_mul, runtimePolynomialEquiv_C,
      _root_.normalize_apply,
      Polynomial.coe_normUnit_of_ne_zero hpTarget,
      runtimePolynomialEquiv_leadingCoeff,
      PolynomialRatRuntime.leadingCoeff_eq,
      ConstructiveRat.field_inv_eq_standard]

/--
The coefficient bridge carries the runtime normalization convention to the
standard monic-polynomial convention.
-/
public theorem runtimePolynomialEquiv_normalize
    (p : RuntimePolynomial) :
    runtimePolynomialEquiv
        (@_root_.normalize RuntimePolynomial
          runtimeAlgebra.euclidean.toMonoidWithZero
          runtimeAlgebra.normalization p) =
      normalize (runtimePolynomialEquiv p) := by
  rw [← runtimeAlgebra.operations.normalize_spec p]
  exact runtimePolynomialEquiv_executableNormalize p

/--
The computable presentation matrix in the choice-free polynomial runtime.
It is obtained through the inverse coefficient bridge, so it cannot drift
from the standard `XI - A` definition.
-/
public def endomorphismPresentationMatrixRuntime
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    _root_.Matrix (Fin n) (Fin n) RuntimePolynomial :=
  fun i j =>
    runtimePolynomialEquiv.symm
      (endomorphismPresentationMatrix A i j)

/--
Mapping every runtime entry back to standard polynomials recovers exactly
mathlib's characteristic matrix.
-/
public theorem endomorphismPresentationMatrixRuntime_eq_charmatrix
    {n : Nat} (A : _root_.Matrix (Fin n) (Fin n) Rat) :
    (endomorphismPresentationMatrixRuntime A).map
        runtimePolynomialEquiv =
      A.charmatrix := by
  rw [← endomorphismPresentationMatrix_eq_charmatrix]
  ext i j : 1
  exact runtimePolynomialEquiv.apply_symm_apply
    (endomorphismPresentationMatrix A i j)

end NormalForms.RationalCanonical
