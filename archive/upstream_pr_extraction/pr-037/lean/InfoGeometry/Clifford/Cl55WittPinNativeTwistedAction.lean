import InfoGeometry.Clifford.Cl55WittPinParity
import InfoGeometry.Clifford.Cl55WittPinOrthogonalAction
import InfoGeometry.Clifford.Cl55WittPinCoverBridge
import InfoGeometry.Clifford.Cl55WittNegativeVectorPin
import InfoGeometry.Clifford.Cl55WittOrthogonalNative

namespace InfoGeometry.Clifford.Clifford55

/-!
# Native `Q55.IsometryEquiv` readout of the twisted Pin action

The twisted action is already constructed as a monoid homomorphism into the
repository's orthogonal subgroup.  This owner only changes the codomain to
Mathlib's native `QuadraticMap.IsometryEquiv` interface.  It makes no claim
that the native `pinGroup Q55` action is surjective.
-/

noncomputable def pinTwistedNativeOrthogonalAction :
    Pin55 →* Q55.IsometryEquiv Q55 :=
  orthogonalGroup55MulEquiv.toMonoidHom.comp pinTwistedOrthogonalAction

@[simp] theorem pinTwistedNativeOrthogonalAction_apply (g : Pin55) :
    pinTwistedNativeOrthogonalAction g =
      orthogonalGroup55IsometryEquiv (pinTwistedOrthogonalAction g) :=
  rfl

theorem pinTwistedNativeOrthogonalAction_spinToPin_eq_pinNativeOrthogonalAction
    (g : Spin55) :
    pinTwistedNativeOrthogonalAction (spinToPin g) =
      pinNativeOrthogonalAction (spinToPin g) := by
  rw [pinTwistedNativeOrthogonalAction_apply,
    pinNativeOrthogonalAction_apply,
    pinTwistedOrthogonalAction_spinToPin_eq_pinOrthogonalAction]

theorem pinTwistedNativeOrthogonalAction_fNegPin (i : Fin 5) :
    pinTwistedNativeOrthogonalAction (fNegPin i) =
      orthogonalGroup55IsometryEquiv (coordinateReflectionGenerator i) := by
  rw [pinTwistedNativeOrthogonalAction_apply,
    pinTwistedOrthogonalAction_fNegPin]

theorem pinTwistedNativeOrthogonalAction_fNegPin_eq_negativeReflectionIsometry
    (i : Fin 5) :
    pinTwistedNativeOrthogonalAction (fNegPin i) =
      negativeReflectionIsometry i := by
  rw [pinTwistedNativeOrthogonalAction_fNegPin]
  rfl

theorem pinTwistedNativeOrthogonalAction_globalSheetPin :
    pinTwistedNativeOrthogonalAction globalSheetPin =
      orthogonalGroup55IsometryEquiv globalSheetReflectionGenerator := by
  rw [pinTwistedNativeOrthogonalAction_apply,
    pinTwistedOrthogonalAction_globalSheetPin]

theorem pinTwistedNativeOrthogonalAction_globalSheetPin_eq_globalSheetReflectionIsometry :
    pinTwistedNativeOrthogonalAction globalSheetPin =
      globalSheetReflectionIsometry := by
  rw [pinTwistedNativeOrthogonalAction_globalSheetPin]
  rfl

theorem pinTwistedNativeOrthogonalAction_negativeVectorPin
    (v : V55) (hv : Q55 v = -1) :
    pinTwistedNativeOrthogonalAction (negativeVectorPin v hv) =
      realQuadraticReflectionIsometry Q55 v (by simp [hv]) := by
  rw [pinTwistedNativeOrthogonalAction_apply]
  rw [negativeVectorPin_orthogonalAction_eq_quadraticReflectionElement]
  rfl

theorem nativeNegativeQuadraticReflectionSubgroup_le_pinTwistedNativeImage :
    Subgroup.map orthogonalGroup55MulEquiv
        negativeQuadraticReflectionSubgroup ≤
      Subgroup.map pinTwistedNativeOrthogonalAction ⊤ := by
  refine (Subgroup.map_le_iff_le_comap).2 ?_
  intro g hg
  have hg' : g ∈ Subgroup.map pinTwistedOrthogonalAction ⊤ :=
    negativeQuadraticReflectionSubgroup_le_pinImage hg
  rcases hg' with ⟨p, hp, hpg⟩
  refine ⟨p, hp, ?_⟩
  change pinTwistedNativeOrthogonalAction p =
    orthogonalGroup55MulEquiv g
  change orthogonalGroup55IsometryEquiv
      (pinTwistedOrthogonalAction p) =
    orthogonalGroup55IsometryEquiv g
  rw [hpg]

end InfoGeometry.Clifford.Clifford55
