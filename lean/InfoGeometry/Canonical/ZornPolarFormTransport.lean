/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornNullRotorPolar

/-! Pull back the native split-polar form along an inverse operator.
Pairing and ket-bra covariance use a transported form, not fixed-form unitarity. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornPolarFormTransport
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ZornNullPeirceWeyl
open ReflexiveNilpotentFlows

def transportedPolar (T : Module.End ℝ ZornCoord) : LinearMap.BilinForm ℝ ZornCoord :=
  polarForm.compl₁₂ T T

theorem transported_pairing (S T : Module.End ℝ ZornCoord) (h : T*S=1)
    (X Y : ZornCoord) : transportedPolar T (S X) (S Y) = polarForm X Y := by
  change polarForm ((T*S) X) ((T*S) Y) = _
  rw [h]
  rfl

theorem transported_ketBra (S T : Module.End ℝ ZornCoord) (h : T*S=1)
    (X Y : ZornCoord) :
    ((transportedPolar T (S Y)).smulRight (S X) : Module.End ℝ ZornCoord) =
      S * ketBra X Y * T := by
  apply LinearMap.ext
  intro W
  change polarForm ((T*S) Y) (T W) • S X = S (polarForm Y (T W) • X)
  rw [h, map_smul]
  rfl

theorem transported_adjoint (S T f g : Module.End ℝ ZornCoord) (h : T*S=1)
    (ha : LinearMap.IsAdjointPair polarForm polarForm f g) :
    LinearMap.IsAdjointPair (transportedPolar T) (transportedPolar T)
      (S*f*T : Module.End ℝ ZornCoord) (S*g*T : Module.End ℝ ZornCoord) := by
  intro X Y
  change polarForm ((T*S) (f (T X))) (T Y) = polarForm (T X) ((T*S) (g (T Y)))
  rw [h]
  exact ha (T X) (T Y)

theorem nullRotor_transported_pairing (X Y : ZornCoord)
    (hX : polarPair X X=0) (hY : polarPair Y Y=0) (h : polarPair X Y=1)
    (c s : ℝ) (hc : c*c+s*s=1) (U V : ZornCoord) :
    transportedPolar (rotor c (-s) (ketBra X X) (ketBra Y Y))
      (rotor c s (ketBra X X) (ketBra Y Y) U)
      (rotor c s (ketBra X X) (ketBra Y Y) V) = polarForm U V := by
  apply transported_pairing
  simpa only [neg_neg] using rotor_inverse (ketBra_sq_zero X X hX)
    (ketBra_sq_zero Y Y hY) (nullPair_reflexive X Y h)
    (nullPair_reflexive Y X (by rwa [polarPair_symm])) c (-s) (by simpa using hc)

end InfoGeometry.Canonical.ZornPolarFormTransport
