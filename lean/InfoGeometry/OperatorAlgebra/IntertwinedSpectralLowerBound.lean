import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

namespace InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

theorem eigenvalue_ge_of_quadratic_bound (operator : Space →ₗ[ℝ] Space)
    (lower : ℝ)
    (bound : ∀ vector, lower * inner ℝ vector vector ≤ inner ℝ vector (operator vector))
    {vector : Space} {eigenvalue : ℝ} (nonzero : vector ≠ 0)
    (eigen : operator vector = eigenvalue • vector) : lower ≤ eigenvalue := by
  have hpositive : 0 < inner ℝ vector vector := real_inner_self_pos.mpr nonzero
  have hbound := bound vector
  rw [eigen, real_inner_smul_right] at hbound
  nlinarith

variable {Source : Type*} [AddCommGroup Source] [Module ℝ Source]

theorem lower_bound_of_intertwining
    (source : Source →ₗ[ℝ] Source) (target : Space →ₗ[ℝ] Space)
    (observation : Source →ₗ[ℝ] Space)
    (intertwines : observation.comp source = target.comp observation)
    (lower : ℝ)
    (bound : ∀ vector, lower * inner ℝ vector vector ≤ inner ℝ vector (target vector))
    {vector : Source} {eigenvalue : ℝ}
    (visible : observation vector ≠ 0)
    (eigen : source vector = eigenvalue • vector) : lower ≤ eigenvalue := by
  have transported : target (observation vector) = eigenvalue • observation vector := by
    have equality := congrArg (fun operator => operator vector) intertwines
    simpa only [LinearMap.comp_apply, eigen, map_smul] using equality.symm
  exact eigenvalue_ge_of_quadratic_bound target lower bound visible transported

theorem deviation_eq_zero_of_quarter_bound
    (source : Source →ₗ[ℝ] Source) (target : Space →ₗ[ℝ] Space)
    (observation : Source →ₗ[ℝ] Space)
    (intertwines : observation.comp source = target.comp observation)
    (bound : ∀ vector, (1 / 4 : ℝ) * inner ℝ vector vector ≤
      inner ℝ vector (target vector))
    {vector : Source} {deviation : ℝ}
    (visible : observation vector ≠ 0)
    (eigen : source vector = (1 / 4 - deviation ^ 2) • vector) : deviation = 0 := by
  have lower := lower_bound_of_intertwining source target observation intertwines
    (1 / 4) bound visible eigen
  apply sq_eq_zero_iff.mp
  nlinarith [sq_nonneg deviation]

end InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound
