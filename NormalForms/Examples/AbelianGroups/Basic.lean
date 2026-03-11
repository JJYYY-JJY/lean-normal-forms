import NormalForms.Matrix.Hermite
import NormalForms.Matrix.Smith
import NormalForms.Bridge.MathlibPID

/-!
# Abelian Group Examples

Sample matrices for the future finitely generated abelian-group showcase.
The current module includes executable smoke checks for elementary matrices,
mixed log certificates, the Phase 1 Bezout reduction gadget, and Phase 2 HNF
smoke coverage.

For Smith normal form, the examples are intentionally split across two layers:

- internal `Fin`-indexed smoke theorems check concrete diagonal specifications,
  invariant factors, same-size `prepareLead...` / `stabilizePivot` /
  `improvePivot` building blocks, and witness/result checks over `Int` and
  `Q[X]`
- public smoke theorems focus on certificate/result packaging through
  `SNFResult.ofCertificate`

This split keeps the examples close to the public API while avoiding the costly
`Fintype.equivFin` simplification paths that can otherwise dominate elaboration
for concrete matrices.
-/

namespace NormalForms.Examples.AbelianGroups

open Polynomial
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite
open NormalForms.Matrix.Smith

def zeroMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  0

def fullRankMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 0 => 3
    | 1, 1 => 5
    | _, _ => 0

def rankDeficientMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 2
    | 0, 1 => 4
    | 1, 0 => 1
    | 1, 1 => 2
    | _, _ => 0

def unitBoundaryMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => -1
    | 0, 1 => 0
    | 1, 0 => 0
    | 1, 1 => 2
    | _, _ => 0

def presentationMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 2
    | 0, 1 => 4
    | 0, 2 => 6
    | 1, 0 => 0
    | 1, 1 => 8
    | 1, 2 => 10
    | _, _ => 0

def swappedFullRankMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 3
    | 0, 1 => 5
    | 1, 0 => 1
    | 1, 1 => 2
    | _, _ => 0

def rowAddedFullRankMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 0 => 5
    | 1, 1 => 9
    | _, _ => 0

def rowScaledFullRankMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 0 => -3
    | 1, 1 => -5
    | _, _ => 0

def swappedPresentationColumnsZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 6
    | 0, 1 => 4
    | 0, 2 => 2
    | 1, 0 => 10
    | 1, 1 => 8
    | 1, 2 => 0
    | _, _ => 0

def addedPresentationColumnsZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 2
    | 0, 1 => 2
    | 0, 2 => 6
    | 1, 0 => 0
    | 1, 1 => 8
    | 1, 2 => 10
    | _, _ => 0

def scaledPresentationColumnsZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 2
    | 0, 1 => 4
    | 0, 2 => -6
    | 1, 0 => 0
    | 1, 1 => 8
    | 1, 2 => -10
    | _, _ => 0

abbrev mixedLog : OperationLog Int (Fin 2) (Fin 3) :=
  [MatrixStep.row (.add (0 : Fin 2) (1 : Fin 2) 2),
    MatrixStep.col (.swap (0 : Fin 3) (2 : Fin 3))]

abbrev rowOnlyLog : OperationLog Int (Fin 2) (Fin 2) :=
  [MatrixStep.row (.add (0 : Fin 2) (1 : Fin 2) 2)]

def mixedReplayMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 6
    | 0, 1 => 4
    | 0, 2 => 2
    | 1, 0 => 22
    | 1, 1 => 16
    | 1, 2 => 4
    | _, _ => 0

noncomputable def polynomialMatrixQX : _root_.Matrix (Fin 2) (Fin 2) (Polynomial Rat) :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => Polynomial.X + 1
    | 0, 1 => Polynomial.X
    | 1, 0 => 0
    | 1, 1 => Polynomial.X ^ 2 + 1
    | _, _ => 0

def fullRankHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 1]

def rankDeficientHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 2;
     0, 0]

def unitBoundaryHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 2]

def presentationHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![2, 4, 6;
     0, 8, 10]

def fullRankSNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 1]

def rankDeficientSNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 0]

def unitBoundarySNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 2]

def presentationSNFMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![2, 0, 0;
     0, 2, 0]

noncomputable def simpleSmithMatrixQX : _root_.Matrix (Fin 2) (Fin 2) (Polynomial Rat) :=
  !![(1 : Polynomial Rat), 0;
     0, 1]

def prepareLeadColumnMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![6, 0;
     15, 0]

def prepareLeadRowMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![6, 15;
     0, 0]

def improvePivotMatrixZ : _root_.Matrix (Fin 3) (Fin 3) Int :=
  !![6, 0, 0;
     0, 0, 15;
     0, 0, 0]

def improvePivotLeadClearedStateZ :
    NormalForms.Matrix.Smith.Internal.LeadClearedState improvePivotMatrixZ :=
  { t := TwoSidedTransform.refl improvePivotMatrixZ
    pivot_ne_zero := by decide
    pivot_normalized := by
      simpa [improvePivotMatrixZ, TwoSidedTransform.refl, Int.normalize_of_nonneg]
    rowCleared := by
      intro j
      fin_cases j <;> decide
    colCleared := by
      intro i
      fin_cases i <;> decide }

def prepareLeadColumnPivotStateZ :
    NormalForms.Matrix.Smith.Internal.PivotState prepareLeadColumnMatrixZ :=
  { t := TwoSidedTransform.refl prepareLeadColumnMatrixZ
    pivot_ne_zero := by decide
    pivot_normalized := by
      simpa [prepareLeadColumnMatrixZ, TwoSidedTransform.refl, Int.normalize_of_nonneg] }

def prepareLeadRowPivotStateZ :
    NormalForms.Matrix.Smith.Internal.PivotState prepareLeadRowMatrixZ :=
  { t := TwoSidedTransform.refl prepareLeadRowMatrixZ
    pivot_ne_zero := by decide
    pivot_normalized := by
      simpa [prepareLeadRowMatrixZ, TwoSidedTransform.refl, Int.normalize_of_nonneg] }

def fullRankSNFPivotStateZ :
    NormalForms.Matrix.Smith.Internal.PivotState fullRankSNFMatrixZ :=
  { t := TwoSidedTransform.refl fullRankSNFMatrixZ
    pivot_ne_zero := by decide
    pivot_normalized := by
      simpa [fullRankSNFMatrixZ, TwoSidedTransform.refl, Int.normalize_of_nonneg] }

def fullRankSNFLeftZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![-5, 2;
     3, -1]

def rankDeficientSNFLeftZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![0, 1;
     1, -2]

def rankDeficientSNFRightZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, -2;
     0, 1]

def presentationSNFRightZ : _root_.Matrix (Fin 3) (Fin 3) Int :=
  !![1, -1, 2;
     0, -1, 5;
     0, 1, -4]

noncomputable def fullRankHNFPublic : HNFResult fullRankMatrixZ :=
  Classical.choose (NormalForms.Matrix.Hermite.hermiteNormalForm_exists fullRankMatrixZ)

abbrev fullRankHNFInternal :
    NormalForms.Matrix.Hermite.Internal.FinHNFResult fullRankMatrixZ :=
  NormalForms.Matrix.Hermite.Internal.hermiteNormalFormFin fullRankMatrixZ
theorem zeroMatrixHNFSmoke :
    (NormalForms.Matrix.Hermite.Internal.hermiteNormalFormFin zeroMatrixZ).H = zeroMatrixZ := by
  decide

theorem fullRankHNFSmoke :
    (NormalForms.Matrix.Hermite.Internal.hermiteNormalFormFin fullRankMatrixZ).H =
      fullRankHNFMatrixZ := by
  native_decide

theorem rankDeficientHNFSmoke :
    (NormalForms.Matrix.Hermite.Internal.hermiteNormalFormFin rankDeficientMatrixZ).H =
      rankDeficientHNFMatrixZ := by
  native_decide

theorem unitBoundaryHNFSmoke :
    (NormalForms.Matrix.Hermite.Internal.hermiteNormalFormFin unitBoundaryMatrixZ).H =
      unitBoundaryHNFMatrixZ := by
  native_decide

theorem presentationHNFSmoke :
    (NormalForms.Matrix.Hermite.Internal.hermiteNormalFormFin presentationMatrixZ).H =
      presentationHNFMatrixZ := by
  native_decide

theorem zeroMatrixHNFExists :
    ∃ result, hermiteNormalForm zeroMatrixZ = some result :=
  NormalForms.Matrix.Hermite.hermiteNormalForm_exists zeroMatrixZ

theorem fullRankHNFExists :
    ∃ result, hermiteNormalForm fullRankMatrixZ = some result :=
  NormalForms.Matrix.Hermite.hermiteNormalForm_exists fullRankMatrixZ

theorem rankDeficientHNFExists :
    ∃ result, hermiteNormalForm rankDeficientMatrixZ = some result :=
  NormalForms.Matrix.Hermite.hermiteNormalForm_exists rankDeficientMatrixZ

theorem unitBoundaryHNFExists :
    ∃ result, hermiteNormalForm unitBoundaryMatrixZ = some result :=
  NormalForms.Matrix.Hermite.hermiteNormalForm_exists unitBoundaryMatrixZ

theorem polynomialMatrixQXHNFExists :
    ∃ result, hermiteNormalForm polynomialMatrixQX = some result :=
  NormalForms.Matrix.Hermite.hermiteNormalForm_exists polynomialMatrixQX

theorem fullRankHNFPublicSmoke :
    hermiteNormalForm fullRankMatrixZ = some fullRankHNFPublic :=
  Classical.choose_spec (NormalForms.Matrix.Hermite.hermiteNormalForm_exists fullRankMatrixZ)

theorem fullRankHNFPublicLeftMulSmoke :
    fullRankHNFPublic.U * fullRankMatrixZ = fullRankHNFPublic.H :=
  fullRankHNFPublic.left_mul

theorem fullRankHNFPublicIsHermiteSmoke :
    IsHermiteNormalForm fullRankHNFPublic.H := by
  exact NormalForms.Matrix.Hermite.hermiteNormalForm_isHermite
    (A := fullRankMatrixZ)
    (result := fullRankHNFPublic)
    (Classical.choose_spec (NormalForms.Matrix.Hermite.hermiteNormalForm_exists fullRankMatrixZ))

theorem fullRankHNFPublicUniqueSmoke :
    fullRankHNFPublic.H = fullRankHNFPublic.H := by
  exact NormalForms.Matrix.Hermite.isHermiteNormalForm_unique_of_left_equiv
    fullRankHNFPublicIsHermiteSmoke
    fullRankHNFPublicIsHermiteSmoke
    (U := 1)
    unimodular_one
    (by simp)

theorem fullRankHNFPublicUnimodularSmoke :
    Unimodular fullRankHNFPublic.U :=
  NormalForms.Matrix.Hermite.hermiteNormalForm_unimodular
    (A := fullRankMatrixZ)
    (result := fullRankHNFPublic)
    (Classical.choose_spec (NormalForms.Matrix.Hermite.hermiteNormalForm_exists fullRankMatrixZ))

theorem fullRankHNFPublicCertificateSmoke :
    (fullRankHNFPublic.toCertificate).U * fullRankMatrixZ =
      (fullRankHNFPublic.toCertificate).result := by
  exact (fullRankHNFPublic.toCertificate).equation

theorem fullRankHNFPublicCertificateMatchesResult :
    (fullRankHNFPublic.toCertificate).result = fullRankHNFPublic.H := by
  rfl

theorem fullRankSNFSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag fullRankSNFMatrixZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [fullRankSNFMatrixZ] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, fullRankSNFMatrixZ]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, fullRankSNFMatrixZ]

theorem rankDeficientSNFSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag rankDeficientSNFMatrixZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [rankDeficientSNFMatrixZ] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, rankDeficientSNFMatrixZ]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, rankDeficientSNFMatrixZ]

theorem unitBoundarySNFSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag unitBoundarySNFMatrixZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [unitBoundarySNFMatrixZ] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [NormalForms.Matrix.Smith.Internal.diagEntry, unitBoundarySNFMatrixZ,
        Int.normalize_of_nonneg]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, unitBoundarySNFMatrixZ]

theorem presentationSNFSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag presentationSNFMatrixZ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [presentationSNFMatrixZ] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [NormalForms.Matrix.Smith.Internal.diagEntry, presentationSNFMatrixZ,
        Int.normalize_of_nonneg]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [NormalForms.Matrix.Smith.Internal.diagEntry, presentationSNFMatrixZ]

theorem simpleSmithMatrixQXSpecSmoke :
    NormalForms.Matrix.Smith.Internal.IsSmithNormalFormDiag simpleSmithMatrixQX := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [simpleSmithMatrixQX] at hij ⊢
  · intro k hk
    norm_num at hk
    interval_cases k <;>
      simp [NormalForms.Matrix.Smith.Internal.diagEntry, simpleSmithMatrixQX]
  · intro k hk
    norm_num at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa [NormalForms.Matrix.Smith.Internal.diagEntry, simpleSmithMatrixQX] using
      (dvd_refl (1 : Polynomial Rat))

theorem zeroMatrixSNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors zeroMatrixZ = [] := by
  native_decide

theorem fullRankSNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors fullRankSNFMatrixZ = [1, 1] := by
  native_decide

theorem rankDeficientSNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors rankDeficientSNFMatrixZ = [1] := by
  native_decide

theorem unitBoundarySNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors unitBoundarySNFMatrixZ = [1, 2] := by
  native_decide

theorem presentationSNFInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors presentationSNFMatrixZ = [2, 2] := by
  native_decide

theorem simpleSmithMatrixQXInvariantFactorsSmoke :
    NormalForms.Matrix.Smith.Internal.invariantFactors simpleSmithMatrixQX = [1, 1] := by
  simp [NormalForms.Matrix.Smith.Internal.invariantFactors, simpleSmithMatrixQX, lowerRight]

theorem prepareLeadColumnStepDataTopLeftSmoke :
    (NormalForms.Matrix.Smith.Internal.prepareLeadColumnStepData
      (A := prepareLeadColumnMatrixZ)
      (TwoSidedTransform.refl prepareLeadColumnMatrixZ) (0 : Fin 1)).B 0 0 =
      normalize (EuclideanDomain.gcd (6 : Int) 15) := by
  have hwit :
      (TwoSidedTransform.refl prepareLeadColumnMatrixZ).B (0 : Fin 1).succ 0 ≠ 0 := by
    norm_num [prepareLeadColumnMatrixZ, TwoSidedTransform.refl]
  simpa [prepareLeadColumnMatrixZ] using
    NormalForms.Matrix.Smith.Internal.prepareLeadColumnStepData_topLeft_eq_normalize_gcd
      (t := TwoSidedTransform.refl prepareLeadColumnMatrixZ) (i := (0 : Fin 1)) hwit

theorem prepareLeadRowStepDataTopLeftSmoke :
    (NormalForms.Matrix.Smith.Internal.prepareLeadRowStepData
      (A := prepareLeadRowMatrixZ)
      (TwoSidedTransform.refl prepareLeadRowMatrixZ) (0 : Fin 1)).B 0 0 =
      normalize (EuclideanDomain.gcd (6 : Int) 15) := by
  have hwit :
      (TwoSidedTransform.refl prepareLeadRowMatrixZ).B 0 (0 : Fin 1).succ ≠ 0 := by
    norm_num [prepareLeadRowMatrixZ, TwoSidedTransform.refl]
  simpa [prepareLeadRowMatrixZ] using
    NormalForms.Matrix.Smith.Internal.prepareLeadRowStepData_topLeft_eq_normalize_gcd
      (t := TwoSidedTransform.refl prepareLeadRowMatrixZ) (j := (0 : Fin 1)) hwit

theorem improvePivotStepDataSmoke :
    let t :=
      NormalForms.Matrix.Smith.Internal.improvePivotStepData
        improvePivotLeadClearedStateZ (0 : Fin 2) (1 : Fin 2)
    t.B 0 0 = 3 ∧ t.B 0 0 ≠ 0 ∧
      Int.natAbs (t.B 0 0) < Int.natAbs (improvePivotMatrixZ 0 0) := by
  dsimp
  have hbad :
      ¬ improvePivotLeadClearedStateZ.t.B 0 0 ∣
        improvePivotLeadClearedStateZ.t.B (0 : Fin 2).succ (1 : Fin 2).succ := by
    change ¬ (6 : Int) ∣ 15
    norm_num
  have htop :
      (NormalForms.Matrix.Smith.Internal.improvePivotStepData
        improvePivotLeadClearedStateZ (0 : Fin 2) (1 : Fin 2)).B 0 0 = 3 := by
    have htop' :=
      NormalForms.Matrix.Smith.Internal.improvePivot_topLeft_eq_normalize_gcd
        improvePivotLeadClearedStateZ (0 : Fin 2) (1 : Fin 2) hbad
    have htop'' :
        (NormalForms.Matrix.Smith.Internal.improvePivotStepData
          improvePivotLeadClearedStateZ (0 : Fin 2) (1 : Fin 2)).B 0 0 =
          normalize (EuclideanDomain.gcd (6 : Int) 15) := by
      simpa [improvePivotLeadClearedStateZ, improvePivotMatrixZ, TwoSidedTransform.refl,
        Int.normalize_of_nonneg] using htop'
    have hgcd : normalize (EuclideanDomain.gcd (6 : Int) 15) = 3 := by
      have hgcdNat : Int.gcd (6 : Int) 15 = 3 := by
        norm_num
      have hgcdInt' : gcd (6 : Int) 15 = 3 := by
        simpa [Int.coe_gcd] using congrArg (fun x : Nat => (x : Int)) hgcdNat
      have hgcdNorm : gcd (6 : Int) 15 = normalize (EuclideanDomain.gcd (6 : Int) 15) := by
        have hEuclid : gcd (6 : Int) 15 ∣ EuclideanDomain.gcd (6 : Int) 15 := by
          exact EuclideanDomain.dvd_gcd
            (show gcd (6 : Int) 15 ∣ (6 : Int) by exact gcd_dvd_left _ _)
            (show gcd (6 : Int) 15 ∣ (15 : Int) by exact gcd_dvd_right _ _)
        have hGcd : EuclideanDomain.gcd (6 : Int) 15 ∣ gcd (6 : Int) 15 := by
          exact GCDMonoid.dvd_gcd
            (EuclideanDomain.gcd_dvd_left (6 : Int) 15)
            (EuclideanDomain.gcd_dvd_right (6 : Int) 15)
        apply gcd_eq_normalize
        · exact hEuclid
        · exact hGcd
      exact hgcdNorm.symm.trans hgcdInt'
    exact htop''.trans hgcd
  refine ⟨htop, ?_, ?_⟩
  · simpa [htop] using
      NormalForms.Matrix.Smith.Internal.improvePivot_pivot_ne_zero
        improvePivotLeadClearedStateZ (0 : Fin 2) (1 : Fin 2) hbad
  · simpa [htop, improvePivotMatrixZ]

theorem stabilizePivotColumnWitnessSmoke :
    NormalForms.Matrix.Smith.Internal.firstUndivisibleFirstCol? prepareLeadColumnMatrixZ =
      some (0 : Fin 1) := by
  native_decide

theorem stabilizePivotRowWitnessSmoke :
    NormalForms.Matrix.Smith.Internal.firstUndivisibleFirstRow? prepareLeadRowMatrixZ =
      some (0 : Fin 1) := by
  native_decide

theorem stabilizePivotImproveWitnessSmoke :
    NormalForms.Matrix.Smith.Internal.firstUndivisibleLowerRight? improvePivotMatrixZ (6 : Int) =
      some ((0 : Fin 2), (1 : Fin 2)) := by
  native_decide

theorem stabilizePivotAlreadyDivisibleWitnessSmoke :
    NormalForms.Matrix.Smith.Internal.firstUndivisibleFirstCol? fullRankSNFMatrixZ = none ∧
      NormalForms.Matrix.Smith.Internal.firstUndivisibleFirstRow? fullRankSNFMatrixZ = none ∧
      NormalForms.Matrix.Smith.Internal.firstUndivisibleLowerRight? fullRankSNFMatrixZ (1 : Int) = none := by
  native_decide

theorem stabilizePivotColumnResultSmoke :
    (NormalForms.Matrix.Smith.Internal.stabilizePivot prepareLeadColumnPivotStateZ).t.B
      (0 : Fin 1).succ 0 = 0 := by
  exact (NormalForms.Matrix.Smith.Internal.stabilizePivot prepareLeadColumnPivotStateZ).colCleared _

theorem stabilizePivotRowResultSmoke :
    (NormalForms.Matrix.Smith.Internal.stabilizePivot prepareLeadRowPivotStateZ).t.B
      0 (0 : Fin 1).succ = 0 := by
  exact (NormalForms.Matrix.Smith.Internal.stabilizePivot prepareLeadRowPivotStateZ).rowCleared _

theorem stabilizePivotImproveResultSmoke :
    (NormalForms.Matrix.Smith.Internal.stabilizePivot improvePivotLeadClearedStateZ.toPivotState).t.B
      0 0 ∣
      (NormalForms.Matrix.Smith.Internal.stabilizePivot improvePivotLeadClearedStateZ.toPivotState).t.B
        (0 : Fin 2).succ (0 : Fin 2).succ := by
  let result := NormalForms.Matrix.Smith.Internal.stabilizePivot improvePivotLeadClearedStateZ.toPivotState
  exact result.lowerRightDivisible _ _

theorem stabilizePivotAlreadyDivisibleResultSmoke :
    (NormalForms.Matrix.Smith.Internal.stabilizePivot fullRankSNFPivotStateZ).t.B 0 0 ∣
      (NormalForms.Matrix.Smith.Internal.stabilizePivot fullRankSNFPivotStateZ).t.B
        (0 : Fin 1).succ (0 : Fin 1).succ := by
  let result := NormalForms.Matrix.Smith.Internal.stabilizePivot fullRankSNFPivotStateZ
  exact result.lowerRightDivisible _ _

def fullRankSNFCertificateZ : TwoSidedCertificate fullRankMatrixZ :=
  { U := fullRankSNFLeftZ
    result := fullRankSNFMatrixZ
    V := 1
    equation := by native_decide }

def rankDeficientSNFCertificateZ : TwoSidedCertificate rankDeficientMatrixZ :=
  { U := rankDeficientSNFLeftZ
    result := rankDeficientSNFMatrixZ
    V := rankDeficientSNFRightZ
    equation := by native_decide }

def unitBoundarySNFCertificateZ : TwoSidedCertificate unitBoundaryMatrixZ :=
  { U := rowOperationMatrix (.smul (0 : Fin 2) (-1))
    result := unitBoundarySNFMatrixZ
    V := 1
    equation := by native_decide }

def presentationSNFCertificateZ : TwoSidedCertificate presentationMatrixZ :=
  { U := 1
    result := presentationSNFMatrixZ
    V := presentationSNFRightZ
    equation := by native_decide }

theorem fullRankSNFCertificateSmoke :
    fullRankSNFCertificateZ.U * fullRankMatrixZ * fullRankSNFCertificateZ.V =
      fullRankSNFCertificateZ.result := by
  exact fullRankSNFCertificateZ.equation

theorem rankDeficientSNFCertificateSmoke :
    rankDeficientSNFCertificateZ.U * rankDeficientMatrixZ * rankDeficientSNFCertificateZ.V =
      rankDeficientSNFCertificateZ.result := by
  exact rankDeficientSNFCertificateZ.equation

theorem unitBoundarySNFCertificateSmoke :
    unitBoundarySNFCertificateZ.U * unitBoundaryMatrixZ * unitBoundarySNFCertificateZ.V =
      unitBoundarySNFCertificateZ.result := by
  exact unitBoundarySNFCertificateZ.equation

theorem presentationSNFCertificateSmoke :
    presentationSNFCertificateZ.U * presentationMatrixZ * presentationSNFCertificateZ.V =
      presentationSNFCertificateZ.result := by
  exact presentationSNFCertificateZ.equation

theorem fullRankSNFOfCertificateUSmoke
    (hSmith : IsSmithNormalForm fullRankSNFCertificateZ.result) :
    (SNFResult.ofCertificate fullRankSNFCertificateZ hSmith).U =
      fullRankSNFCertificateZ.U := rfl

theorem fullRankSNFOfCertificateSSmoke
    (hSmith : IsSmithNormalForm fullRankSNFCertificateZ.result) :
    (SNFResult.ofCertificate fullRankSNFCertificateZ hSmith).S =
      fullRankSNFCertificateZ.result := rfl

theorem fullRankSNFOfCertificateVSmoke
    (hSmith : IsSmithNormalForm fullRankSNFCertificateZ.result) :
    (SNFResult.ofCertificate fullRankSNFCertificateZ hSmith).V =
      fullRankSNFCertificateZ.V := rfl

theorem fullRankSNFOfCertificateEquationSmoke
    (hSmith : IsSmithNormalForm fullRankSNFCertificateZ.result) :
    (SNFResult.ofCertificate fullRankSNFCertificateZ hSmith).two_sided_mul =
      fullRankSNFCertificateZ.equation := rfl

theorem fullRankSNFOfCertificateRoundTripSmoke
    (hSmith : IsSmithNormalForm fullRankSNFCertificateZ.result) :
    (SNFResult.ofCertificate fullRankSNFCertificateZ hSmith).toCertificate =
      fullRankSNFCertificateZ := rfl

noncomputable def simpleSmithSNFCertificateQX :
    TwoSidedCertificate simpleSmithMatrixQX :=
  { U := 1
    result := simpleSmithMatrixQX
    V := 1
    equation := by simp }

theorem simpleSmithSNFCertificateQXSmoke :
    simpleSmithSNFCertificateQX.U * simpleSmithMatrixQX * simpleSmithSNFCertificateQX.V =
      simpleSmithSNFCertificateQX.result := by
  exact simpleSmithSNFCertificateQX.equation

theorem simpleSmithSNFOfCertificateRoundTripQXSmoke
    (hSmith : IsSmithNormalForm (R := Polynomial Rat) simpleSmithSNFCertificateQX.result) :
    (SNFResult.ofCertificate simpleSmithSNFCertificateQX hSmith).toCertificate =
      simpleSmithSNFCertificateQX := rfl

theorem fullRankRowSwapSmoke :
    applyRowOperation fullRankMatrixZ (.swap (0 : Fin 2) (1 : Fin 2)) = swappedFullRankMatrixZ := by
  decide

theorem fullRankRowAddSmoke :
    applyRowOperation fullRankMatrixZ (.add (0 : Fin 2) (1 : Fin 2) 2) = rowAddedFullRankMatrixZ := by
  decide

theorem fullRankRowScaleSmoke :
    applyRowOperation fullRankMatrixZ (.smul (1 : Fin 2) (-1)) = rowScaledFullRankMatrixZ := by
  decide

theorem presentationColumnSwapSmoke :
    applyColumnOperation presentationMatrixZ (.swap (0 : Fin 3) (2 : Fin 3)) =
      swappedPresentationColumnsZ := by
  decide

theorem presentationColumnAddSmoke :
    applyColumnOperation presentationMatrixZ (.add (0 : Fin 3) (1 : Fin 3) (-1)) =
      addedPresentationColumnsZ := by
  decide

theorem presentationColumnScaleSmoke :
    applyColumnOperation presentationMatrixZ (.smul (2 : Fin 3) (-1)) =
      scaledPresentationColumnsZ := by
  decide

theorem mixedReplaySmoke :
    replayLog presentationMatrixZ mixedLog = mixedReplayMatrixZ := by
  decide

theorem fullRankRowSwapMatrixSmoke :
    rowOperationMatrix (.swap (0 : Fin 2) (1 : Fin 2)) * fullRankMatrixZ = swappedFullRankMatrixZ := by
  calc
    rowOperationMatrix (.swap (0 : Fin 2) (1 : Fin 2)) * fullRankMatrixZ
        = applyRowOperation fullRankMatrixZ (.swap (0 : Fin 2) (1 : Fin 2)) :=
          rowOperationMatrix_mul fullRankMatrixZ (.swap (0 : Fin 2) (1 : Fin 2))
    _ = swappedFullRankMatrixZ := fullRankRowSwapSmoke

theorem fullRankRowAddMatrixSmoke :
    rowOperationMatrix (.add (0 : Fin 2) (1 : Fin 2) 2) * fullRankMatrixZ = rowAddedFullRankMatrixZ := by
  calc
    rowOperationMatrix (.add (0 : Fin 2) (1 : Fin 2) 2) * fullRankMatrixZ
        = applyRowOperation fullRankMatrixZ (.add (0 : Fin 2) (1 : Fin 2) 2) :=
          rowOperationMatrix_mul fullRankMatrixZ (.add (0 : Fin 2) (1 : Fin 2) 2)
    _ = rowAddedFullRankMatrixZ := fullRankRowAddSmoke

theorem fullRankRowScaleMatrixSmoke :
    rowOperationMatrix (.smul (1 : Fin 2) (-1)) * fullRankMatrixZ = rowScaledFullRankMatrixZ := by
  calc
    rowOperationMatrix (.smul (1 : Fin 2) (-1)) * fullRankMatrixZ
        = applyRowOperation fullRankMatrixZ (.smul (1 : Fin 2) (-1)) :=
          rowOperationMatrix_mul fullRankMatrixZ (.smul (1 : Fin 2) (-1))
    _ = rowScaledFullRankMatrixZ := fullRankRowScaleSmoke

theorem presentationColumnSwapMatrixSmoke :
    presentationMatrixZ * columnOperationMatrix (.swap (0 : Fin 3) (2 : Fin 3)) =
      swappedPresentationColumnsZ := by
  calc
    presentationMatrixZ * columnOperationMatrix (.swap (0 : Fin 3) (2 : Fin 3))
        = applyColumnOperation presentationMatrixZ (.swap (0 : Fin 3) (2 : Fin 3)) :=
          mul_columnOperationMatrix presentationMatrixZ (.swap (0 : Fin 3) (2 : Fin 3))
    _ = swappedPresentationColumnsZ := presentationColumnSwapSmoke

theorem presentationColumnAddMatrixSmoke :
    presentationMatrixZ * columnOperationMatrix (.add (0 : Fin 3) (1 : Fin 3) (-1)) =
      addedPresentationColumnsZ := by
  calc
    presentationMatrixZ * columnOperationMatrix (.add (0 : Fin 3) (1 : Fin 3) (-1))
        = applyColumnOperation presentationMatrixZ (.add (0 : Fin 3) (1 : Fin 3) (-1)) :=
          mul_columnOperationMatrix presentationMatrixZ (.add (0 : Fin 3) (1 : Fin 3) (-1))
    _ = addedPresentationColumnsZ := presentationColumnAddSmoke

theorem presentationColumnScaleMatrixSmoke :
    presentationMatrixZ * columnOperationMatrix (.smul (2 : Fin 3) (-1)) =
      scaledPresentationColumnsZ := by
  calc
    presentationMatrixZ * columnOperationMatrix (.smul (2 : Fin 3) (-1))
        = applyColumnOperation presentationMatrixZ (.smul (2 : Fin 3) (-1)) :=
          mul_columnOperationMatrix presentationMatrixZ (.smul (2 : Fin 3) (-1))
    _ = scaledPresentationColumnsZ := presentationColumnScaleSmoke

theorem mixedReplayCertificateSmoke :
    leftAccumulator mixedLog * presentationMatrixZ * rightAccumulator mixedLog = mixedReplayMatrixZ := by
  calc
    leftAccumulator mixedLog * presentationMatrixZ * rightAccumulator mixedLog
        = replayLog presentationMatrixZ mixedLog := replayLog_eq_left_right presentationMatrixZ mixedLog
    _ = mixedReplayMatrixZ := mixedReplaySmoke

theorem mixedLogCertificateSafe : mixedLog.Forall UnimodularStep := by
  simp [List.Forall, UnimodularStep, UnimodularRowOperation, UnimodularColumnOperation]

theorem rowOnlyLogIsRow : rowOnlyLog.Forall IsRowStep := by
  simp [List.Forall, IsRowStep]

theorem mixedLogLeftUnimodular :
    Unimodular (leftAccumulator mixedLog) :=
  leftAccumulator_unimodular_of_forall mixedLog mixedLogCertificateSafe

theorem mixedLogRightUnimodular :
    Unimodular (rightAccumulator mixedLog) :=
  rightAccumulator_unimodular_of_forall mixedLog mixedLogCertificateSafe

theorem mixedLogTwoSidedCertificateSmoke :
    (TwoSidedCertificate.ofLog (A := presentationMatrixZ) mixedLog).U * presentationMatrixZ *
      (TwoSidedCertificate.ofLog (A := presentationMatrixZ) mixedLog).V =
      (TwoSidedCertificate.ofLog (A := presentationMatrixZ) mixedLog).result := by
  exact (TwoSidedCertificate.ofLog (A := presentationMatrixZ) mixedLog).equation

theorem rowOnlyLogLeftCertificateSmoke :
    (LeftCertificate.ofRowLog (A := fullRankMatrixZ) rowOnlyLog rowOnlyLogIsRow).U * fullRankMatrixZ =
      (LeftCertificate.ofRowLog (A := fullRankMatrixZ) rowOnlyLog rowOnlyLogIsRow).result := by
  exact (LeftCertificate.ofRowLog (A := fullRankMatrixZ) rowOnlyLog rowOnlyLogIsRow).equation

theorem nonUnitScaleStillExecutes :
    applyRowOperation fullRankMatrixZ (.smul (0 : Fin 2) (2 : Int)) =
      !![2, 4;
         3, 5] := by
  decide

theorem nonUnitScaleNotCertificateSafe :
    ¬ UnimodularStep (MatrixStep.row (.smul (0 : Fin 2) (2 : Int)) : MatrixStep Int (Fin 2) (Fin 3)) := by
  simpa [UnimodularStep, UnimodularRowOperation] using (show ¬ IsUnit (2 : Int) by decide)

theorem bezoutIntSmoke :
    _root_.Matrix.mulVec (bezoutReductionMatrix (6 : Int) 15) ![6, 15] = ![3, 0] := by
  calc
    _ = ![EuclideanDomain.gcd (6 : Int) 15, 0] := bezoutReductionMatrix_mulVec (6 : Int) 15
    _ = ![3, 0] := by native_decide

theorem bezoutIntTransposeSmoke :
    _root_.Matrix.vecMul ![6, 15] (bezoutReductionMatrix (6 : Int) 15).transpose = ![3, 0] := by
  calc
    _ = ![EuclideanDomain.gcd (6 : Int) 15, 0] := vecMul_bezoutReductionMatrix_transpose (6 : Int) 15
    _ = ![3, 0] := by native_decide

theorem bezoutIntUnimodularSmoke :
    IsUnit (bezoutReductionMatrix (6 : Int) 15).det := by
  simpa [det_bezoutReductionMatrix (6 : Int) 15]

theorem bezoutPolynomialSmoke :
    _root_.Matrix.mulVec
        (bezoutReductionMatrix ((Polynomial.X : Polynomial Rat) + 1) (Polynomial.X : Polynomial Rat))
        ![((Polynomial.X : Polynomial Rat) + 1), (Polynomial.X : Polynomial Rat)] =
      ![EuclideanDomain.gcd ((Polynomial.X : Polynomial Rat) + 1) (Polynomial.X : Polynomial Rat), 0] := by
  simpa using
    (bezoutReductionMatrix_mulVec ((Polynomial.X : Polynomial Rat) + 1) (Polynomial.X : Polynomial Rat))

theorem presentationColumnSpanBridgeSmoke :
    NormalForms.Bridge.MathlibPID.pidSmithColumnSpan presentationMatrixZ =
      LinearMap.range presentationMatrixZ.mulVecLin := by
  simpa using
    NormalForms.Bridge.MathlibPID.pidSmithColumnSpan_eq_range_mulVecLin presentationMatrixZ

end NormalForms.Examples.AbelianGroups
