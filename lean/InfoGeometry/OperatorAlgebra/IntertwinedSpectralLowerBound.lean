/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

namespace InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

/-- A symmetric operator whose square is the sum of a Laplacian term and a
curvature term induces the corresponding quadratic-form decomposition.

This is the operator-level bridge: symmetry moves one copy of `dirac` across
the inner product, and the exact linear-map identity supplies the two terms.
No positivity or spectral-gap conclusion is built into this identity. -/
theorem dirac_square_operator_identity_gives_energy_split
    (dirac laplacian curvature : Space →ₗ[ℝ] Space)
    (dirac_symmetric : ∀ x y, inner ℝ (dirac x) y = inner ℝ x (dirac y))
    (square_decomposition : dirac.comp dirac = laplacian + curvature)
    (vector : Space) :
    inner ℝ (dirac vector) (dirac vector) =
      inner ℝ (laplacian vector) vector + inner ℝ (curvature vector) vector := by
  calc
    inner ℝ (dirac vector) (dirac vector) =
        inner ℝ vector (dirac (dirac vector)) := dirac_symmetric vector (dirac vector)
    _ = inner ℝ ((dirac.comp dirac) vector) vector := by
      simp only [LinearMap.comp_apply]
      exact real_inner_comm _ _
    _ = inner ℝ ((laplacian + curvature) vector) vector := by
      rw [square_decomposition]
    _ = inner ℝ (laplacian vector) vector + inner ℝ (curvature vector) vector := by
      simp only [LinearMap.add_apply, inner_add_left]

theorem eigenvalue_ge_of_quadratic_bound (operator : Space →ₗ[ℝ] Space)
    (lower : ℝ)
    (bound : ∀ vector, lower * inner ℝ vector vector ≤ inner ℝ vector (operator vector))
    {vector : Space} {eigenvalue : ℝ} (nonzero : vector ≠ 0)
    (eigen : operator vector = eigenvalue • vector) : lower ≤ eigenvalue := by
  have hpositive : 0 < inner ℝ vector vector := real_inner_self_pos.mpr nonzero
  have hbound := bound vector
  rw [eigen, real_inner_smul_right] at hbound
  nlinarith

/-- A uniform quadratic lower bound for an operator gives a norm lower bound.

This is the precise analytic input needed to turn a coercive Dirac-square
identity into a spectral gap. Pointwise strict positivity of an auxiliary
curvature term is not enough: the constant `gap` here is uniform over every
vector. -/
theorem norm_lower_bound_of_quadratic_coercivity
    (operator : Space →ₗ[ℝ] Space) (gap : ℝ) (hgap : 0 < gap)
    (bound : ∀ vector,
      gap ^ 2 * inner ℝ vector vector ≤
        inner ℝ (operator vector) (operator vector)) :
    ∀ vector, gap * ‖vector‖ ≤ ‖operator vector‖ := by
  intro vector
  have hbound := bound vector
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hbound
  have hgap0 : 0 ≤ gap := le_of_lt hgap
  have hnorm : 0 ≤ ‖vector‖ := norm_nonneg _
  have hopen : 0 ≤ ‖operator vector‖ := norm_nonneg _
  nlinarith [sq_nonneg (gap * ‖vector‖ - ‖operator vector‖)]

/-- A nonnegative norm gap is equivalent to the corresponding uniform
quadratic-form lower bound. This packages both directions of the quantitative
criterion: neither pointwise positivity nor absence of kernel vectors is
silently promoted to a uniform gap. -/
theorem norm_lower_bound_iff_quadratic_coercivity
    (operator : Space →ₗ[ℝ] Space) (gap : ℝ) (hgap : 0 ≤ gap) :
    (∀ vector, gap * ‖vector‖ ≤ ‖operator vector‖) ↔
      ∀ vector,
        gap ^ 2 * inner ℝ vector vector ≤
          inner ℝ (operator vector) (operator vector) := by
  constructor
  · intro hnorm vector
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have h := hnorm vector
    have hg : 0 ≤ gap := hgap
    have hv : 0 ≤ ‖vector‖ := norm_nonneg _
    have ho : 0 ≤ ‖operator vector‖ := norm_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr h)
      (add_nonneg (mul_nonneg hg hv) ho)]
  · intro hquad vector
    rcases lt_or_eq_of_le hgap with hpos | hzero
    · exact norm_lower_bound_of_quadratic_coercivity operator gap hpos
        hquad vector
    · subst gap
      simp

/-- Unit approximate zero-modes obstruct every positive uniform norm gap.

This is the sequential converse to the coercivity estimates above: a concrete
sequence of normalized vectors with images tending to zero is enough to show
that no positive constant can bound the operator below on the whole space.
The theorem is stated for the existing operator carrier and does not assume
that the operator has a nontrivial kernel. -/
theorem no_positive_norm_gap_of_unit_approximate_zero_modes
    (operator : Space →ₗ[ℝ] Space) (vectors : ℕ → Space)
    (unit : ∀ n, ‖vectors n‖ = 1)
    (images_tend_to_zero :
      Filter.Tendsto (fun n => ‖operator (vectors n)‖) Filter.atTop (nhds 0)) :
    ¬ ∃ gap : ℝ, 0 < gap ∧
      ∀ vector, gap * ‖vector‖ ≤ ‖operator vector‖ := by
  rintro ⟨gap, hgap, lower⟩
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      ‖operator (vectors n)‖ < gap :=
    images_tend_to_zero.eventually (Iio_mem_nhds hgap)
  rcases Filter.eventually_atTop.mp hsmall with ⟨N, hN⟩
  have hbound := lower (vectors N)
  rw [unit N] at hbound
  have hstrict := hN N le_rfl
  linarith

/-- A form-level Lichnerowicz decomposition yields a norm gap when its
curvature contribution has a uniform quadratic lower bound.

The decomposition hypothesis is stated at the quadratic-form level so the
owner does not silently assume self-adjointness or identify `D²` with an
energy form. In applications it can be discharged from a self-adjoint
operator identity `D² = Δ + R`. Pointwise strict positivity of
`⟪R v, v⟫` alone is insufficient: the constant `gap` must work uniformly for
all vectors. -/
theorem norm_lower_bound_of_lichnerowicz_energy_split
    (dirac laplacian curvature : Space →ₗ[ℝ] Space)
    (gap : ℝ) (hgap : 0 < gap)
    (energy_split : ∀ vector,
      inner ℝ (dirac vector) (dirac vector) =
        inner ℝ (laplacian vector) vector + inner ℝ (curvature vector) vector)
    (laplacian_nonneg : ∀ vector, 0 ≤ inner ℝ (laplacian vector) vector)
    (curvature_uniform_bound : ∀ vector,
      gap ^ 2 * inner ℝ vector vector ≤ inner ℝ (curvature vector) vector) :
    ∀ vector, gap * ‖vector‖ ≤ ‖dirac vector‖ := by
  apply norm_lower_bound_of_quadratic_coercivity dirac gap hgap
  intro vector
  rw [energy_split vector]
  linarith [laplacian_nonneg vector, curvature_uniform_bound vector]

/-- A symmetric operator square decomposition gives the norm gap directly
when the Laplacian term is nonnegative and the curvature term has a uniform
quadratic lower bound. This composes the operator identity with the energy
estimate without treating pointwise positivity as a uniform spectral bound. -/
theorem norm_lower_bound_of_symmetric_operator_square_decomposition
    (dirac laplacian curvature : Space →ₗ[ℝ] Space)
    (dirac_symmetric : ∀ x y, inner ℝ (dirac x) y = inner ℝ x (dirac y))
    (square_decomposition : dirac.comp dirac = laplacian + curvature)
    (gap : ℝ) (hgap : 0 < gap)
    (laplacian_nonneg : ∀ vector, 0 ≤ inner ℝ (laplacian vector) vector)
    (curvature_uniform_bound : ∀ vector,
      gap ^ 2 * inner ℝ vector vector ≤ inner ℝ (curvature vector) vector) :
    ∀ vector, gap * ‖vector‖ ≤ ‖dirac vector‖ := by
  apply norm_lower_bound_of_lichnerowicz_energy_split
    dirac laplacian curvature gap hgap
  · intro vector
    exact dirac_square_operator_identity_gives_energy_split
      dirac laplacian curvature dirac_symmetric square_decomposition vector
  · exact laplacian_nonneg
  · exact curvature_uniform_bound

/-- Uniform coercivity in the energy split excludes nonzero zero-modes. The
uniform lower-bound hypothesis is essential; pointwise strict positivity
without a common constant does not establish this conclusion. -/
theorem dirac_kernel_trivial_of_lichnerowicz_energy_split
    (dirac laplacian curvature : Space →ₗ[ℝ] Space)
    (gap : ℝ) (hgap : 0 < gap)
    (energy_split : ∀ vector,
      inner ℝ (dirac vector) (dirac vector) =
        inner ℝ (laplacian vector) vector + inner ℝ (curvature vector) vector)
    (laplacian_nonneg : ∀ vector, 0 ≤ inner ℝ (laplacian vector) vector)
    (curvature_uniform_bound : ∀ vector,
      gap ^ 2 * inner ℝ vector vector ≤ inner ℝ (curvature vector) vector)
    (vector : Space) (hzero : dirac vector = 0) : vector = 0 := by
  have hbound := norm_lower_bound_of_lichnerowicz_energy_split
    dirac laplacian curvature gap hgap energy_split laplacian_nonneg
    curvature_uniform_bound vector
  rw [hzero, norm_zero] at hbound
  have hnorm : ‖vector‖ = 0 := by
    nlinarith [norm_nonneg vector]
  exact norm_eq_zero.mp hnorm

/-- Pointwise positive curvature in an exact Lichnerowicz energy split rules
out nonzero zero-modes. This conclusion needs no uniform lower bound and does
not assert a norm or spectral gap. -/
theorem dirac_kernel_trivial_of_pointwise_curvature_positive
    (dirac laplacian curvature : Space →ₗ[ℝ] Space)
    (energy_split : ∀ vector,
      inner ℝ (dirac vector) (dirac vector) =
        inner ℝ (laplacian vector) vector + inner ℝ (curvature vector) vector)
    (laplacian_nonneg : ∀ vector, 0 ≤ inner ℝ (laplacian vector) vector)
    (curvature_positive : ∀ vector, vector ≠ 0 →
      0 < inner ℝ (curvature vector) vector)
    (vector : Space) (zero_mode : dirac vector = 0) : vector = 0 := by
  by_contra hvector
  have hsplit := energy_split vector
  rw [zero_mode] at hsplit
  have henergy :
      inner ℝ (laplacian vector) vector +
        inner ℝ (curvature vector) vector = 0 := by
    simpa using hsplit.symm
  have hcurvature := curvature_positive vector hvector
  linarith [laplacian_nonneg vector]

/-- Under a pointwise-positive Lichnerowicz energy split, the Dirac operator
has zero kernel exactly at the zero vector. This is the exact qualitative
conclusion; it makes no uniform norm-gap assertion. -/
theorem dirac_eq_zero_iff_vector_eq_zero_of_pointwise_curvature_positive
    (dirac laplacian curvature : Space →ₗ[ℝ] Space)
    (energy_split : ∀ vector,
      inner ℝ (dirac vector) (dirac vector) =
        inner ℝ (laplacian vector) vector + inner ℝ (curvature vector) vector)
    (laplacian_nonneg : ∀ vector, 0 ≤ inner ℝ (laplacian vector) vector)
    (curvature_positive : ∀ vector, vector ≠ 0 →
      0 < inner ℝ (curvature vector) vector)
    (vector : Space) :
    dirac vector = 0 ↔ vector = 0 := by
  constructor
  · exact dirac_kernel_trivial_of_pointwise_curvature_positive
      dirac laplacian curvature energy_split laplacian_nonneg
      curvature_positive vector
  · intro h
    rw [h]
    exact map_zero dirac

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
