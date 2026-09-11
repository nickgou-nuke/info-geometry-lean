import InfoGeometry.Quantum.ComplexKramersAntiunitary
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! The finite phase-inverting glide carried by the native Kramers operator.
The antiunitary and the deck action remain distinct carriers.
-/
noncomputable section
namespace InfoGeometry.Quantum.KramersPhaseGlideRepresentation

open InfoGeometry.Quantum.ComplexKramersAntiunitary

def phaseEnd (z : ℂ) : Module.End ℂ H2 := z • LinearMap.id

@[simp] theorem phaseEnd_apply (z : ℂ) (v : H2) :
    phaseEnd z v = z • v := by
  simp [phaseEnd]

@[simp] theorem phaseEnd_one : phaseEnd 1 = 1 := by
  apply LinearMap.ext
  intro v
  simp

@[simp] theorem phaseEnd_mul (z w : ℂ) :
    phaseEnd z * phaseEnd w = phaseEnd (z * w) := by
  apply LinearMap.ext
  intro v
  simp [Module.End.mul_apply, smul_smul]
  ring

theorem kramers_phase_conjugation (z : ℂ) (v : H2) :
    timeReversal (phaseEnd z v) =
      phaseEnd (star z) (timeReversal v) := by
  simp

theorem star_eq_inv_of_star_mul_self
    {z : ℂ} (hunit : star z * z = 1) :
    star z = z⁻¹ := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    simp at hunit
  calc
    star z = star z * 1 := by simp
    _ = star z * (z * z⁻¹) := by rw [mul_inv_cancel₀ hz]
    _ = (star z * z) * z⁻¹ := by ring
    _ = z⁻¹ := by rw [hunit]; simp

theorem kramers_phase_inverse
    {z : ℂ} (hunit : star z * z = 1) (v : H2) :
    timeReversal (phaseEnd z v) =
      phaseEnd z⁻¹ (timeReversal v) := by
  rw [kramers_phase_conjugation,
    star_eq_inv_of_star_mul_self hunit]

theorem kramers_glide_lift_packet
    {z : ℂ} (hunit : star z * z = 1) (v : H2) :
    timeReversal (phaseEnd z v) =
        phaseEnd z⁻¹ (timeReversal v) ∧
      timeReversal (timeReversal v) = -v := by
  exact ⟨kramers_phase_inverse hunit v, timeReversal_sq v⟩

end InfoGeometry.Quantum.KramersPhaseGlideRepresentation
end noncomputable section
