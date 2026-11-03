/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionFureyOperatorLift
import InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge

/-!
# CAR generators as the Peirce off-diagonal representation of the SL₃ stabilizer

The six-generator CAR carrier is related to the upper and lower Peirce
coordinates by an explicit linear equivalence.  The existing trace-zero
Peirce stabilizer therefore induces a genuine linear action on CAR labels,
and its derivation commutator on the transported split-octonion left
multiplication operators is exactly that action.  This is the stabilizer
action; it does not assert invariance under all of split `G₂`.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCARPeirceSL3Bridge

open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.CanonicalZornPeirceStabilizer
open InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
open InfoGeometry.Lie.SplitOctonionFureyOperatorLift
open InfoGeometry.Algebra.ZornPinorReconstruction

abbrev CARLabel := InfoGeometry.Algebra.ZornPinorReconstruction.V ×
  InfoGeometry.Algebra.ZornPinorReconstruction.V
abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- CAR labels and upper/lower Peirce coordinates are related by the same
linear change of variables used by the existing split-CAR Clifford vector. -/
noncomputable def carPeirceCoordinates :
    CARLabel ≃ₗ[ℝ] offDiagonalCoordinates where
  toFun p := (-(p.1 + p.2), p.1 - p.2)
  invFun q := ((q.2 - q.1) / 2, -(q.1 + q.2) / 2)
  left_inv p := by
    ext i <;> simp <;> ring
  right_inv q := by
    ext i <;> simp <;> ring
  map_add' p q := by
    ext i <;> simp <;> abel
  map_smul' r p := by
    ext i <;> simp <;> ring

/-- The transported CAR six-plane is exactly the canonical Peirce
off-diagonal subspace, not merely a subspace of the regular operator algebra. -/
noncomputable def carPeirceCarrierEquiv :
    CARLabel ≃ₗ[ℝ] offDiagonal :=
  carPeirceCoordinates.trans offDiagonalLinearEquiv.symm

/-- Under this equivalence the CAR Clifford vector is the original split-Zorn
off-diagonal element. -/
theorem carPeirceCarrierEquiv_value (p : CARLabel) :
    (carPeirceCarrierEquiv p : CZ) =
      InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
        (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector p) := by
  change InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis.canonicalVectorLinearEquiv.symm
      (InfoGeometry.Algebra.ZornLeftCAR.cliffordVector p) = _
  rfl

/-- Infinitesimal action of a trace-zero matrix on the CAR label space,
transported from the established Peirce stabilizer action. -/
def sl3CARInfinitesimal (M : SL3) : CARLabel →ₗ[ℝ] CARLabel :=
  carPeirceCarrierEquiv.symm.toLinearMap.comp
    ((restrictOffDiagonal (sl3ToPeirceStabilizer M)).comp
      carPeirceCarrierEquiv.toLinearMap)

/-- In Peirce coordinates the transported CAR action is the standard action
on the upper slot and the contragredient action on the lower slot. -/
theorem sl3CARInfinitesimal_peirceCoordinates (M : SL3) (p : CARLabel) :
    carPeirceCoordinates (sl3CARInfinitesimal M p) =
      (M.1.mulVec (carPeirceCoordinates p).1,
        (-Matrix.transpose M.1).mulVec (carPeirceCoordinates p).2) := by
  have h := sl3ToPeirceStabilizer_restrictOffDiagonal_apply M
    (carPeirceCarrierEquiv p)
  simpa [sl3CARInfinitesimal, carPeirceCarrierEquiv] using h

/-- The selected split-`G₂` Peirce-stabilizing derivation acts on each
transported CAR generator by the induced CAR-label action.  Thus the
commutator action preserves the six-generator subspace and realizes the
existing trace-zero stabilizer representation on it. -/
theorem sl3Stabilizer_commutator_on_CAR_generator (M : SL3) (p : CARLabel) :
    ⁅(sl3ToPeirceStabilizer M).1.1,
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
        (carPeirceCarrierEquiv p).val⁆ =
    InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
      (carPeirceCarrierEquiv (sl3CARInfinitesimal M p)).val := by
  have hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation
      ((sl3ToPeirceStabilizer M).1.1) :=
    (sl3ToPeirceStabilizer M).1.property
  rw [InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.derivation_lie_leftRegular
    ((sl3ToPeirceStabilizer M).1.1) hD]
  simp [sl3CARInfinitesimal,
    InfoGeometry.Lie.CanonicalZornPeirceStabilizer.restrictOffDiagonal_apply]

end InfoGeometry.Lie.SplitOctonionCARPeirceSL3Bridge

end
