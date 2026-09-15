import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open scoped InnerProductSpace

namespace InfoGeometry.EmergentGeometry.HodgeDiracFactorization

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

theorem square_energy_identity (operator : Space →ₗ[ℝ] Space)
    (symmetric : operator.IsSymmetric) (state : Space) :
    ⟪(operator * operator) state, state⟫_ℝ = ‖operator state‖ ^ 2 := by
  change ⟪operator (operator state), state⟫_ℝ = ‖operator state‖ ^ 2
  rw [symmetric, real_inner_self_eq_norm_sq]

theorem square_energy_nonneg (operator : Space →ₗ[ℝ] Space)
    (symmetric : operator.IsSymmetric) (state : Space) :
    0 ≤ ⟪(operator * operator) state, state⟫_ℝ := by
  rw [square_energy_identity operator symmetric]
  exact sq_nonneg _

theorem square_apply_eq_zero_iff (operator : Space →ₗ[ℝ] Space)
    (symmetric : operator.IsSymmetric) (state : Space) :
    (operator * operator) state = 0 ↔ operator state = 0 := by
  constructor
  · intro harmonic
    have energy := square_energy_identity operator symmetric state
    rw [harmonic, inner_zero_left] at energy
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp energy.symm)
  · intro vacuum
    change operator (operator state) = 0
    rw [vacuum, map_zero]

theorem square_kernel_eq (operator : Space →ₗ[ℝ] Space)
    (symmetric : operator.IsSymmetric) :
    LinearMap.ker (operator * operator) = LinearMap.ker operator := by
  ext state
  exact square_apply_eq_zero_iff operator symmetric state

theorem sqrt_square_energy (operator : Space →ₗ[ℝ] Space)
    (symmetric : operator.IsSymmetric) (state : Space) :
    Real.sqrt ⟪(operator * operator) state, state⟫_ℝ = ‖operator state‖ := by
  rw [square_energy_identity operator symmetric]
  exact Real.sqrt_sq (norm_nonneg _)

theorem sqrt_square_energy_smul (operator : Space →ₗ[ℝ] Space)
    (symmetric : operator.IsSymmetric) (scalar : ℝ) (state : Space) :
    Real.sqrt ⟪(operator * operator) (scalar • state), scalar • state⟫_ℝ =
      |scalar| * ‖operator state‖ := by
  rw [sqrt_square_energy operator symmetric, map_smul, norm_smul, Real.norm_eq_abs]

end InfoGeometry.EmergentGeometry.HodgeDiracFactorization
