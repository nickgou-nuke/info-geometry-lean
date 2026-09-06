import InfoGeometry.Clifford.Cl55WittSpinOrthogonalAction
import InfoGeometry.Clifford.Cl55WittOrthogonalNative
import InfoGeometry.Clifford.Cl55WittPinNativeTwistedAction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Native orthogonal action of the real split Spin group

The pointwise native isometry `spinActionIsometryEquiv` is already owned by
the Clifford Pin action file.  This owner packages it as a multiplicative
homomorphism, without asserting surjectivity onto the full native orthogonal
group or identifying the kernel.
-/

noncomputable def spinNativeOrthogonalAction :
    Spin55 →* Q55.IsometryEquiv Q55 where
  toFun := spinActionIsometryEquiv
  map_one' := by
    apply DFunLike.ext
    intro v
    change pinTwistedAction (spinToPin (1 : Spin55)) v = v
    rw [show spinToPin (1 : Spin55) = 1 by rfl]
    rw [pinTwistedAction_one]
    rfl
  map_mul' g h := by
    apply DFunLike.ext
    intro v
    exact spinActionIsometryEquiv_mul_apply g h v

@[simp] theorem spinNativeOrthogonalAction_apply (g : Spin55) :
    spinNativeOrthogonalAction g = spinActionIsometryEquiv g :=
  rfl

theorem spinNativeOrthogonalAction_preserves_Q55
    (g : Spin55) (v : V55) :
    Q55 (spinNativeOrthogonalAction g v) = Q55 v := by
  change Q55 (spinAction g v) = Q55 v
  exact spinAction_preserves_Q55 g v

theorem spinNativeOrthogonalAction_eq_pinNativeOrthogonalAction
    (g : Spin55) :
    spinNativeOrthogonalAction g =
      pinNativeOrthogonalAction (spinToPin g) := by
  rw [spinNativeOrthogonalAction_apply,
    spinActionIsometryEquiv]
  exact pinTwistedNativeOrthogonalAction_spinToPin_eq_pinNativeOrthogonalAction g

end InfoGeometry.Clifford.Clifford55
