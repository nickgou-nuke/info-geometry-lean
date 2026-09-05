import InfoGeometry.Quantum.ComplexKramersAntiunitary

/-!
# Kramers phase inversion and the lifted glide relation

An orientation-reversing deck generator and a square-minus-one antiunitary are
not the same object.  Their exact representation-theoretic bridge is that an
antiunitary conjugates a unit complex phase to its inverse.

This file proves the pointwise semilinear relation

`T (U_z v) = U_(conj z) (T v)`

and, on the unit circle,

`T (U_z v) = U_(z⁻¹) (T v)`.

Together with `T²=-1`, this is the finite Pin/Kramers lift of the phase-inverting
glide relation.
-/

noncomputable section

namespace InfoGeometry.Quantum.KramersPhaseGlideRepresentation

open InfoGeometry.Quantum.ComplexKramersAntiunitary

/-- Scalar phase action as a complex-linear endomorphism. -/
def phaseEnd (z : ℂ) : Module.End ℂ H2 :=
  z • LinearMap.id

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

/-- Antiunitarity conjugates scalar phase multiplication. -/
theorem kramers_phase_conjugation (z : ℂ) (v : H2) :
    timeReversal (phaseEnd z v) =
      phaseEnd (star z) (timeReversal v) := by
  simp

/-- A unit-norm algebraic phase has conjugate equal to inverse. -/
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

/-- On the unit circle, Kramers conjugation implements phase inversion. -/
theorem kramers_phase_inverse
    {z : ℂ} (hunit : star z * z = 1) (v : H2) :
    timeReversal (phaseEnd z v) =
      phaseEnd z⁻¹ (timeReversal v) := by
  rw [kramers_phase_conjugation,
    star_eq_inv_of_star_mul_self hunit]

/-- Two Kramers applications produce the central sign while one application
inverts every unit phase. -/
theorem kramers_glide_lift_packet
    {z : ℂ} (hunit : star z * z = 1) (v : H2) :
    timeReversal (phaseEnd z v) =
        phaseEnd z⁻¹ (timeReversal v) ∧
      timeReversal (timeReversal v) = -v := by
  exact ⟨kramers_phase_inverse hunit v,
    timeReversal_sq v⟩

end InfoGeometry.Quantum.KramersPhaseGlideRepresentation
