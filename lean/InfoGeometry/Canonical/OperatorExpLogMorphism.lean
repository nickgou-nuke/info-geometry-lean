import Mathlib
import InfoGeometry.Canonical.ModularTensorInduction

/-!
# InfoGeometry.Canonical.OperatorExpLogMorphism

Operator-level exp/log morphism laws on the finite `M₂(ℝ)` modular seed.

This file lifts the scalar additive/multiplicative morphism pattern to
the concrete operator family `expKExact : ℝ → M₂(ℝ)`.
-/

namespace OperatorExpLogMorphism

open Matrix
open InfoGeometry.Canonical.ModularTensorInduction

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Left spectral log-coordinate on the `expKExact` image. -/
noncomputable def opLogLeft (A : M2R) : ℝ := Real.log (A 0 0)

/-- Right spectral log-coordinate on the `expKExact` image. -/
noncomputable def opLogRight (A : M2R) : ℝ := Real.log (A 1 1)

/-- Additive-to-multiplicative morphism at operator level. -/
theorem opExp_add_morphism (s t : ℝ) :
    expKExact (s + t) = expKExact s * expKExact t := by
  symm
  exact expKExact_mul s t

/-- Left log-coordinate recovers the additive parameter on the image. -/
theorem opLogLeft_on_exp (t : ℝ) :
    opLogLeft (expKExact t) = t := by
  unfold opLogLeft
  rw [expKExact_eval]
  norm_num

/-- Right log-coordinate recovers the negative additive parameter on the image. -/
theorem opLogRight_on_exp (t : ℝ) :
    opLogRight (expKExact t) = -t := by
  unfold opLogRight
  rw [expKExact_eval]
  norm_num

/-- Left log-coordinate is additive over operator multiplication on the image. -/
theorem opLogLeft_mul_on_image (s t : ℝ) :
    opLogLeft (expKExact s * expKExact t) =
      opLogLeft (expKExact s) + opLogLeft (expKExact t) := by
  rw [← opExp_add_morphism, opLogLeft_on_exp, opLogLeft_on_exp, opLogLeft_on_exp]

/-- Right log-coordinate is additive over operator multiplication on the image. -/
theorem opLogRight_mul_on_image (s t : ℝ) :
    opLogRight (expKExact s * expKExact t) =
      opLogRight (expKExact s) + opLogRight (expKExact t) := by
  rw [← opExp_add_morphism, opLogRight_on_exp, opLogRight_on_exp, opLogRight_on_exp]
  ring

/-- Reconstruct the operator from the left log-coordinate (on the image). -/
theorem opExp_of_opLogLeft_on_image (t : ℝ) :
    expKExact (opLogLeft (expKExact t)) = expKExact t := by
  rw [opLogLeft_on_exp]

/-- Left and right log-coordinates are opposite on the `expKExact` image. -/
theorem opLogLeft_add_opLogRight_on_image (t : ℝ) :
    opLogLeft (expKExact t) + opLogRight (expKExact t) = 0 := by
  rw [opLogLeft_on_exp, opLogRight_on_exp]
  ring

/-- Right channel is reconstructed from the left log-coordinate on the image. -/
theorem opExp_of_opLogRight_on_image (t : ℝ) :
    expKExact (- opLogRight (expKExact t)) = expKExact t := by
  rw [opLogRight_on_exp]
  ring

/-- Product of diagonal channels is constant `1` on the `expKExact` image. -/
theorem opDiag_product_one_on_image (t : ℝ) :
    (expKExact t) 0 0 * (expKExact t) 1 1 = 1 := by
  rw [expKExact_eval]
  norm_num
  rw [← Real.exp_add]
  ring_nf
  simpa using Real.exp_zero

/-- Joint left/right log readout on the `expKExact` image. -/
theorem opLog_pair_on_exp (t : ℝ) :
    (opLogLeft (expKExact t), opLogRight (expKExact t)) = (t, -t) := by
  ext <;> simp [opLogLeft_on_exp, opLogRight_on_exp]

end OperatorExpLogMorphism
