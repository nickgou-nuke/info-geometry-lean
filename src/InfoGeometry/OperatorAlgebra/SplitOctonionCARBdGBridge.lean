/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionCARPeirceSL3Bridge
import InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge

/-!
# CAR stabilizer action in the split-octonion BdG grading

The CAR/Peirce owner identifies the action of the selected `SL₃` stabilizer
on the six-dimensional off-diagonal carrier. The BdG owner identifies the
two extreme grades with the ordered commutators of its diagonal and
off-diagonal operators. This module proves that these are the same action
after transport: the particle grade is the induced CAR-label action and the
hole grade is its negative. The result concerns the existing stabilizer
subalgebra, not all of split `G₂`.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonionCARBdGBridge

open InfoGeometry.Lie.SplitOctonionCARPeirceSL3Bridge
open InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
open InfoGeometry.Lie.CanonicalZornPeirceStabilizer
open InfoGeometry.Physics.Algebra
open InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge
open InfoGeometry.Physics

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev EndCZ := InfoGeometry.Lie.SplitOctonionCARPeirceSL3Bridge.EndCZ

/-- The particle extreme grade of the CAR interaction is precisely the
left-regular image of the infinitesimal `SL₃` action on its CAR label. -/
theorem sl3_CAR_action_is_BdG_positive_grade (M : SL3) (p : CARLabel) :
    fiveGradeProjector (chiralGrading (A := EndCZ)) .posTwo
      (massiveBdGCommutatorAnomaly
        ((sl3ToPeirceStabilizer M).1.1 : EndCZ)
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
          (carPeirceCarrierEquiv p).val)) =
      !![0, InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
          (carPeirceCarrierEquiv (sl3CARInfinitesimal M p)).val;
        0, 0] := by
  let D : EndCZ := (sl3ToPeirceStabilizer M).1.1
  let X : offDiagonal :=
    carPeirceCarrierEquiv p
  have hAction := sl3Stabilizer_commutator_on_CAR_generator M p
  have hComm : D *
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val -
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val * D =
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (carPeirceCarrierEquiv (sl3CARInfinitesimal M p)).val := by
    simpa [D, X, LieRing.of_associative_ring_bracket] using hAction
  have hGrades := massiveBdG_chiral_anomaly_exact_fiveGrade_components D
    (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val)
  exact hGrades.1.trans (congrArg (fun T : EndCZ => !![0, T; 0, 0]) hComm)

/-- The hole extreme grade carries the opposite CAR action. Its negative is
the same transported generator that appears in the particle grade. -/
theorem sl3_CAR_action_is_BdG_negative_grade (M : SL3) (p : CARLabel) :
    fiveGradeProjector (chiralGrading (A := EndCZ)) .negTwo
      (massiveBdGCommutatorAnomaly
        ((sl3ToPeirceStabilizer M).1.1 : EndCZ)
        (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
          (carPeirceCarrierEquiv p).val)) =
      !![0, 0;
        -InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
          (carPeirceCarrierEquiv (sl3CARInfinitesimal M p)).val, 0] := by
  let D : EndCZ := (sl3ToPeirceStabilizer M).1.1
  let X : offDiagonal :=
    carPeirceCarrierEquiv p
  have hAction := sl3Stabilizer_commutator_on_CAR_generator M p
  have hComm : D *
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val -
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val * D =
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (carPeirceCarrierEquiv (sl3CARInfinitesimal M p)).val := by
    simpa [D, X, LieRing.of_associative_ring_bracket] using hAction
  have hReverse :
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val * D -
      D * InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val =
      -InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (carPeirceCarrierEquiv (sl3CARInfinitesimal M p)).val := by
    calc
      _ = -(D * InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val -
        InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val * D) := by
          noncomm_ring
      _ = _ := congrArg Neg.neg hComm
  have hGrades := massiveBdG_chiral_anomaly_exact_fiveGrade_components D
    (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular X.val)
  exact hGrades.2.1.trans
    (congrArg (fun T : EndCZ => !![0, 0; T, 0]) hReverse)

end InfoGeometry.OperatorAlgebra.SplitOctonionCARBdGBridge
