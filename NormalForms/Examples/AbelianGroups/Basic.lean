import NormalForms.Matrix.Hermite.Basic
import NormalForms.Bridge.MathlibPID

/-!
# Abelian Group Examples

Sample matrices for the future finitely generated abelian-group showcase.
The current module includes executable smoke checks for elementary matrices,
mixed log certificates, the Phase 1 Bezout reduction gadget, and Phase 2 HNF smoke coverage.
-/

namespace NormalForms.Examples.AbelianGroups

open Polynomial
open NormalForms.Matrix.Elementary
open NormalForms.Matrix.Certificates
open NormalForms.Matrix.Hermite

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
  !![1, 2;
     0, 0]

def rankDeficientHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![2, 4;
     0, 0]

def unitBoundaryHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 2) Int :=
  !![1, 0;
     0, 0]

def presentationHNFMatrixZ : _root_.Matrix (Fin 2) (Fin 3) Int :=
  !![2, 4, 6;
     0, 0, 0]

noncomputable def fullRankHNFPublic : HNFResult fullRankMatrixZ :=
  Classical.choose (hermiteNormalForm_exists fullRankMatrixZ)
theorem zeroMatrixHNFSmoke :
    (Internal.hermiteNormalFormFin zeroMatrixZ).H = zeroMatrixZ := by
  decide

theorem fullRankHNFSmoke :
    (Internal.hermiteNormalFormFin fullRankMatrixZ).H = fullRankHNFMatrixZ := by
  decide

theorem rankDeficientHNFSmoke :
    (Internal.hermiteNormalFormFin rankDeficientMatrixZ).H = rankDeficientHNFMatrixZ := by
  decide

theorem unitBoundaryHNFSmoke :
    (Internal.hermiteNormalFormFin unitBoundaryMatrixZ).H = unitBoundaryHNFMatrixZ := by
  decide

theorem presentationHNFSmoke :
    (Internal.hermiteNormalFormFin presentationMatrixZ).H = presentationHNFMatrixZ := by
  decide

theorem zeroMatrixHNFExists :
    ∃ result, hermiteNormalForm zeroMatrixZ = some result :=
  hermiteNormalForm_exists zeroMatrixZ

theorem fullRankHNFExists :
    ∃ result, hermiteNormalForm fullRankMatrixZ = some result :=
  hermiteNormalForm_exists fullRankMatrixZ

theorem rankDeficientHNFExists :
    ∃ result, hermiteNormalForm rankDeficientMatrixZ = some result :=
  hermiteNormalForm_exists rankDeficientMatrixZ

theorem unitBoundaryHNFExists :
    ∃ result, hermiteNormalForm unitBoundaryMatrixZ = some result :=
  hermiteNormalForm_exists unitBoundaryMatrixZ

theorem fullRankHNFPublicSmoke :
    hermiteNormalForm fullRankMatrixZ = some fullRankHNFPublic :=
  Classical.choose_spec (hermiteNormalForm_exists fullRankMatrixZ)

theorem fullRankHNFPublicLeftMulSmoke :
    fullRankHNFPublic.U * fullRankMatrixZ = fullRankHNFPublic.H :=
  fullRankHNFPublic.left_mul

theorem fullRankHNFPublicIsHermiteSmoke :
    IsHermiteNormalForm fullRankHNFPublic.H :=
  fullRankHNFPublic.isHermite

theorem fullRankHNFPublicCertificateSmoke :
    (fullRankHNFPublic.toCertificate).U * fullRankMatrixZ =
      (fullRankHNFPublic.toCertificate).result := by
  exact (fullRankHNFPublic.toCertificate).equation

theorem fullRankHNFPublicCertificateMatchesResult :
    (fullRankHNFPublic.toCertificate).result = fullRankHNFPublic.H := by
  rfl
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

theorem presentationClassificationRoadmap :
    NormalForms.Bridge.MathlibPID.InvariantFactorsAgreeUpToNormalization presentationMatrixZ := by
  trivial

end NormalForms.Examples.AbelianGroups






