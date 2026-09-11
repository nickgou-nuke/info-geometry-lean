import InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionPolarTransport

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionQuaternionCalibratedZornBridge

open SplitOctonion
open InfoGeometry.Canonical.SplitOctonionQuaternionZornPolarBridge
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

abbrev H := Quaternion ℝ
abbrev Vec3 := InfoGeometry.Algebra.FiniteSpin.Vec3R
abbrev QuaternionCoordinates := ℝ × Vec3
abbrev CartesianCoordinates := QuaternionCoordinates × QuaternionCoordinates
abbrev CanonicalZorn := InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates.CZ

/-! The quaternion-pair convention and the canonical Zorn product use opposite
Witt placements for the two imaginary triples.  The multiplicative
calibration is the global exchange `x = r - q`, `y = q + r`. -/
noncomputable def calibratedCartesianZornLinearEquiv :
    CartesianCoordinates ≃ₗ[ℝ] CanonicalZorn where
  toFun qr :=
    { a := qr.1.1 + qr.2.1
      b := qr.1.1 - qr.2.1
      x := qr.2.2 - qr.1.2
      y := qr.1.2 + qr.2.2 }
  invFun Z :=
    (((Z.a + Z.b) / 2, (Z.y - Z.x) / 2),
      ((Z.a - Z.b) / 2, (Z.x + Z.y) / 2))
  left_inv qr := by
    rcases qr with ⟨⟨q0, q⟩, ⟨r0, r⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · dsimp
        ring
      · funext i
        simp [sub_eq_add_neg]
        ring
    · apply Prod.ext
      · dsimp
        ring
      · funext i
        simp
        ring
  right_inv Z := by
    ext i <;> simp <;> ring
  map_add' X Y := by
    ext i <;> simp <;> ring
  map_smul' c X := by
    ext <;>
      simp [Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
        smul_eq_mul] <;>
      ring

@[simp] theorem calibratedCartesianZornLinearEquiv_apply
    (qr : CartesianCoordinates) :
    calibratedCartesianZornLinearEquiv qr =
      { a := qr.1.1 + qr.2.1
        b := qr.1.1 - qr.2.1
        x := qr.2.2 - qr.1.2
        y := qr.1.2 + qr.2.2 } := rfl

noncomputable def splitOctonionCalibratedCanonicalZornEquiv :
    SplitOctonion ≃ CanonicalZorn :=
  splitOctonionCartesianEquiv.trans
    calibratedCartesianZornLinearEquiv.toEquiv

@[simp] theorem splitOctonionCalibratedCanonicalZornEquiv_apply
    (X : SplitOctonion) :
    splitOctonionCalibratedCanonicalZornEquiv X =
      calibratedCartesianZornLinearEquiv
        (splitOctonionCartesianEquiv X) := rfl

theorem splitOctonionCalibratedCanonicalZornEquiv_norm (X : SplitOctonion) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
        (splitOctonionCalibratedCanonicalZornEquiv X) = normSQ X := by
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
      (calibratedCartesianZornLinearEquiv
        (splitOctonionCartesianEquiv X)) = normSQ X
  simp [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ,
    realCrossProduct3,
    calibratedCartesianZornLinearEquiv,
    splitOctonionCartesianEquiv,
    splitOctonionPairEquiv,
    quaternionCoordinatesEquiv,
    InfoGeometry.Canonical.ZornMatrix.dot,
    normSQ]
  ring

theorem splitOctonionCalibratedCanonicalZornEquiv_mul
    (X Y : SplitOctonion) :
    splitOctonionCalibratedCanonicalZornEquiv (X * Y) =
      splitOctonionCalibratedCanonicalZornEquiv X *
        splitOctonionCalibratedCanonicalZornEquiv Y := by
  rw [splitOctonionCalibratedCanonicalZornEquiv_apply,
    splitOctonionCartesianEquiv_mul]
  apply InfoGeometry.Canonical.ZornMatrix.ext
  · simp [calibratedCartesianZornLinearEquiv,
      splitOctonionCartesianMul, quaternionCoordinatesMul,
      quaternionCoordinatesStar,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot]
    ring
  · simp [calibratedCartesianZornLinearEquiv,
      splitOctonionCartesianMul, quaternionCoordinatesMul,
      quaternionCoordinatesStar,
      InfoGeometry.Canonical.ZornMatrix.mul,
      InfoGeometry.Canonical.ZornMatrix.dot]
    ring
  · funext i
    fin_cases i <;>
      simp [calibratedCartesianZornLinearEquiv,
        splitOctonionCartesianMul, quaternionCoordinatesMul,
        quaternionCoordinatesStar,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.cross]
      <;> ring
  · funext i
    fin_cases i <;>
      simp [calibratedCartesianZornLinearEquiv,
        splitOctonionCartesianMul, quaternionCoordinatesMul,
        quaternionCoordinatesStar,
        InfoGeometry.Canonical.ZornMatrix.mul,
        InfoGeometry.Canonical.ZornMatrix.cross]
      <;> ring

theorem polar_decomposition_calibratedCanonicalZorn
    (X : SplitOctonion) (h : isHyperbolic X) (hb : X.b ≠ 0) :
    splitOctonionCalibratedCanonicalZornEquiv X =
      splitOctonionCalibratedCanonicalZornEquiv
        ⟨polarRho X h • polarU X (a_ne_zero_of_isHyperbolic X h), 0⟩ *
      splitOctonionCalibratedCanonicalZornEquiv
        (expHyperbolic 1 (polarEta X h)
          (J_g (polarG X (a_ne_zero_of_isHyperbolic X h) hb))) := by
  exact SplitOctonion.polar_decomposition_transport
    splitOctonionCalibratedCanonicalZornEquiv
    splitOctonionCalibratedCanonicalZornEquiv_mul X h hb

end InfoGeometry.Canonical.SplitOctonionQuaternionCalibratedZornBridge
