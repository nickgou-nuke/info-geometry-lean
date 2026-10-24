/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornNullMajoranaAdjoint

/-! Inverse and split-polar adjoint are different operations for the null-pair
rotor. These results concern its actual action on the native Zorn module. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornNullRotorPolar
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ZornNullPeirceWeyl
open ZornNullSupportAdjoint ZornNullMajoranaAdjoint ReflexiveNilpotentFlows

theorem nullRotor_self_adjoint (X Y : ZornCoord) (c s : ℝ) :
    LinearMap.IsAdjointPair polarForm polarForm
      (rotor c s (ketBra X X) (ketBra Y Y) : Module.End ℝ ZornCoord)
      (rotor c s (ketBra X X) (ketBra Y Y) : Module.End ℝ ZornCoord) := by
  intro U V
  simp only [rotor, complement, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, map_add, map_sub, map_smul,
    smul_eq_mul]
  rw [nullSupport_self_adjoint X Y U V, ketBra_adjoint X X U V,
    ketBra_adjoint Y Y U V]
  rfl

theorem nullRotor_pairing_transport (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1)
    (c s : ℝ) (U V : ZornCoord) :
    polarForm (rotor c s (ketBra X X) (ketBra Y Y) U)
      (rotor c s (ketBra X X) (ketBra Y Y) V) =
    polarForm U (rotor (c*c-s*s) (c*s+s*c) (ketBra X X) (ketBra Y Y) V) := by
  rw [nullRotor_self_adjoint X Y c s]
  change polarForm U ((rotor c s (ketBra X X) (ketBra Y Y) *
    rotor c s (ketBra X X) (ketBra Y Y)) V) = _
  rw [rotor_mul (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)
    (nullPair_reflexive X Y h) (nullPair_reflexive Y X (by rwa [polarPair_symm]))]

theorem nullRotor_quarter_pairing (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1) :
    polarForm (rotor (0 : ℝ) 1 (ketBra X X) (ketBra Y Y) X)
      (rotor (0 : ℝ) 1 (ketBra X X) (ketBra Y Y) Y) = -1 := by
  rw [nullRotor_pairing_transport X Y hX hY h]
  norm_num only [zero_mul, one_mul, sub_self, zero_sub, add_zero]
  have hnY : zornNorm Y = 0 := by simpa only [polarPair_self] using hY
  have hz : polarPair X 0 = 0 := map_zero (polarForm X)
  simp [rotor, complement, support, ketBra, polarPair_symm Y X, h, hnY, hz]
  change polarForm X (-Y) = -1
  rw [map_neg]
  exact congrArg Neg.neg h

end InfoGeometry.Canonical.ZornNullRotorPolar
