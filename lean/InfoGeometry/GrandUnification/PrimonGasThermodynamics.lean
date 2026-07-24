import Mathlib.Analysis.Complex.Basic
import InfoGeometry.GrandUnification.HodgeCartanTrifactor

/-!
# Local primon partition-factor algebra

This module proves only a one-prime algebraic identity: the local factor
`(1 - x)⁻¹` multiplied by `1 - x` is `1` when `x ≠ 1`.  It does not prove an
Euler product theorem, a zeta-function identity, a Witten-index formula, a
Bose--Einstein phase transition, or a Cuntz/UHF Fock-space theorem.
-/

namespace InfoGeometry.GrandUnification.PrimonThermodynamics

variable (p : ℝ) (h_prime : 1 < p)
variable (β : ℝ)

/-- The Boltzmann weight of a single prime mode: x_p = p^(-β) -/
noncomputable def boltzmann_weight (p β : ℝ) : ℝ :=
  p ^ (-β)

/-- The local inverse factor `(1 - x_p)⁻¹` for a single mode. -/
noncomputable def bosonic_local_factor (p β : ℝ) : ℝ :=
  (1 - boltzmann_weight p β)⁻¹

/-- The local plus factor `1 + x_p` for a single mode. -/
noncomputable def fermionic_local_factor (p β : ℝ) : ℝ :=
  1 + boltzmann_weight p β

/-- The local complementary factor `1 - x_p`. -/
noncomputable def witten_local_factor (p β : ℝ) : ℝ :=
  1 - boltzmann_weight p β

/-- The local inverse factor and complementary factor multiply to `1` when
`x_p ≠ 1`. -/
theorem thermodynamic_supersymmetry (p β : ℝ) (h : boltzmann_weight p β ≠ 1) :
    bosonic_local_factor p β * witten_local_factor p β = 1 := by
  unfold bosonic_local_factor witten_local_factor
  exact inv_mul_cancel₀ (sub_ne_zero.mpr h.symm)

end InfoGeometry.GrandUnification.PrimonThermodynamics
