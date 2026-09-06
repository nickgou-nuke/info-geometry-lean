import InfoGeometry.Canonical.Spin55NativeOrthogonalActionBridge
import InfoGeometry.Clifford.Cl55WittSpinOrthogonalAction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Coherence of the two native `Spin(5,5)` orthogonal-action readouts

The Clifford owner exposes the action first as an element of the concrete
subgroup `orthogonalGroup55`.  The canonical owner also exposes the same
action directly as an isometry of `Q55`.  This file records their equality
without adding any surjectivity, kernel, or double-cover assertion.
-/

theorem spinActionOrthogonalHom_native_readback (g : Spin55) :
    orthogonalGroup55IsometryEquiv (spinActionOrthogonalHom g) =
      spinNativeOrthogonalAction g := by
  rw [spinActionOrthogonalHom_apply,
    spinNativeOrthogonalAction_apply]
  rfl

theorem spinActionOrthogonal_native_readback (g : Spin55) :
    orthogonalGroup55IsometryEquiv (spinActionOrthogonal g) =
      spinNativeOrthogonalAction g := by
  simpa only [spinActionOrthogonalHom_apply] using
    spinActionOrthogonalHom_native_readback g

theorem spinActionOrthogonalHom_native_readback_hom :
    orthogonalGroup55MulEquiv.toMonoidHom.comp
        spinActionOrthogonalHom =
      spinNativeOrthogonalAction := by
  ext g
  exact spinActionOrthogonalHom_native_readback g

end InfoGeometry.Clifford.Clifford55
