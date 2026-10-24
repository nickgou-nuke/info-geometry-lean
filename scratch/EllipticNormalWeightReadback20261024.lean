/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance
import InfoGeometry.Canonical.ReflexiveNilpotentFlows

/-! # Diagonal projection of the existing circular pole orbit

The native weighted support is exactly the normal Peirce part of the moving
pole. This polynomial readback does not assert a state or a KMS condition.
-/
namespace InfoGeometry.Canonical.EllipticNormalWeightReadback
open DeBruijnRotorAlternationCycle
open GrassmannianBundleCyclotomicOrientability
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Removing the off-diagonal part gives Stream 3's actual weighted support,
with the coefficient order determined by its native definition. -/
theorem normalBundlePart_movingPolePlus {d B : A}
    (h : IsDualSeedPair d B) (c s : R) :
    normalBundlePart (polePlus d B) (movingPolePlus c s d B) =
      UnifiedGeometryOperatorSignificance.kmsModularWeight s c d B := by
  obtain ⟨hpp, _, hpm, hmp, _, _, _, _, _⟩ :=
    ReflexiveNilpotentFlows.support_table h.d_sq h.B_sq h.dBd h.BdB
  have hpB : (d*B)*B=0 := by rw [mul_assoc, h.B_sq, mul_zero]
  have hdp : d*(d*B)=0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  have hBp : B*(d*B)=B := by rw [← mul_assoc, h.BdB]
  rw [movingPolePlus_eq h]
  simp only [normalBundlePart, polePlus, poleMinus, transitionVelocity,
    UnifiedGeometryOperatorSignificance.kmsModularWeight,
    UnifiedGeometryOperatorSignificance.projPlus,
    UnifiedGeometryOperatorSignificance.projMinus, smul_add,
    mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    one_mul, mul_one, hpp, hpm, hmp, h.dBd, hpB, hdp, hBp,
    smul_zero, mul_zero, zero_mul, add_zero, zero_add, sub_zero, sub_self]
  abel

end InfoGeometry.Canonical.EllipticNormalWeightReadback
