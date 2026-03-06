import NormalForms.Bridge.MathlibPID

/-!
# Abelian Group Examples

Sample matrices for the future finitely generated abelian-group showcase.
The current module includes small executable smoke checks for elementary row and
column operations while the HNF and SNF algorithms remain scaffolds.
-/

namespace NormalForms.Examples.AbelianGroups

open Polynomial
open NormalForms.Matrix.Elementary

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
  [MatrixStep.row (.add (0 : Fin 2) (1 : Fin 2) 2), MatrixStep.col (.swap (0 : Fin 3) (2 : Fin 3))]

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

theorem fullRankRowSwapSmoke :
    NormalForms.Matrix.Elementary.applyRowOperation fullRankMatrixZ
      (.swap (0 : Fin 2) (1 : Fin 2)) = swappedFullRankMatrixZ := by
  decide

theorem fullRankRowAddSmoke :
    NormalForms.Matrix.Elementary.applyRowOperation fullRankMatrixZ
      (.add (0 : Fin 2) (1 : Fin 2) 2) = rowAddedFullRankMatrixZ := by
  decide

theorem fullRankRowScaleSmoke :
    NormalForms.Matrix.Elementary.applyRowOperation fullRankMatrixZ
      (.smul (1 : Fin 2) (-1)) = rowScaledFullRankMatrixZ := by
  decide

theorem presentationColumnSwapSmoke :
    NormalForms.Matrix.Elementary.applyColumnOperation presentationMatrixZ
      (.swap (0 : Fin 3) (2 : Fin 3)) = swappedPresentationColumnsZ := by
  decide

theorem presentationColumnAddSmoke :
    NormalForms.Matrix.Elementary.applyColumnOperation presentationMatrixZ
      (.add (0 : Fin 3) (1 : Fin 3) (-1)) = addedPresentationColumnsZ := by
  decide

theorem presentationColumnScaleSmoke :
    NormalForms.Matrix.Elementary.applyColumnOperation presentationMatrixZ
      (.smul (2 : Fin 3) (-1)) = scaledPresentationColumnsZ := by
  decide

theorem mixedReplaySmoke :
    replayLog presentationMatrixZ mixedLog = mixedReplayMatrixZ := by
  decide

theorem presentationClassificationRoadmap :
    NormalForms.Bridge.MathlibPID.InvariantFactorsAgreeUpToNormalization presentationMatrixZ := by
  trivial

end NormalForms.Examples.AbelianGroups
