import InfoGeometry.Convex.Legendre
import InfoGeometry.Canonical.FisherWoottersQuantumPotential
import Mathlib.Topology.Order.MonotoneConvergence

namespace InfoGeometry.Amari.DuallyFlatThermodynamics

open InfoGeometry.Convex
open scoped RealInnerProductSpace Topology
open Filter

namespace DualityDependency

inductive Archetype
  | convexDifferentiablePotential
  | fenchelYoungEquality
  | canonicalDivergence
  | threePointIdentity
  | orthogonalProjection
  | decreasingDivergences
  | inverseGradients
  | inverseHessians
  | affineCoordinates
  | zeroAcceleration
  deriving DecidableEq, Fintype

open Archetype

def prerequisites : Archetype → Finset Archetype
  | convexDifferentiablePotential => {convexDifferentiablePotential}
  | fenchelYoungEquality => {convexDifferentiablePotential, fenchelYoungEquality}
  | canonicalDivergence =>
      {convexDifferentiablePotential, fenchelYoungEquality, canonicalDivergence}
  | threePointIdentity =>
      {convexDifferentiablePotential, fenchelYoungEquality, canonicalDivergence, threePointIdentity}
  | orthogonalProjection =>
      {convexDifferentiablePotential, fenchelYoungEquality, canonicalDivergence,
        threePointIdentity, orthogonalProjection}
  | decreasingDivergences =>
      {convexDifferentiablePotential, fenchelYoungEquality, canonicalDivergence,
        threePointIdentity, orthogonalProjection, decreasingDivergences}
  | inverseGradients => {inverseGradients}
  | inverseHessians => {inverseGradients, inverseHessians}
  | affineCoordinates => {affineCoordinates}
  | zeroAcceleration => {affineCoordinates, zeroAcceleration}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem dependency_branches :
    convexDifferentiablePotential ≤ fenchelYoungEquality ∧
    fenchelYoungEquality ≤ canonicalDivergence ∧
    canonicalDivergence ≤ threePointIdentity ∧
    threePointIdentity ≤ orthogonalProjection ∧
    orthogonalProjection ≤ decreasingDivergences ∧
    inverseGradients ≤ inverseHessians ∧ affineCoordinates ≤ zeroAcceleration := by
  change prerequisites convexDifferentiablePotential ⊆ prerequisites fenchelYoungEquality ∧
    prerequisites fenchelYoungEquality ⊆ prerequisites canonicalDivergence ∧
    prerequisites canonicalDivergence ⊆ prerequisites threePointIdentity ∧
    prerequisites threePointIdentity ⊆ prerequisites orthogonalProjection ∧
    prerequisites orthogonalProjection ⊆ prerequisites decreasingDivergences ∧
    prerequisites inverseGradients ⊆ prerequisites inverseHessians ∧
    prerequisites affineCoordinates ⊆ prerequisites zeroAcceleration
  decide

theorem pythagoras_and_affine_acceleration_incomparable :
    ¬ orthogonalProjection ≤ zeroAcceleration ∧ ¬ zeroAcceleration ≤ orthogonalProjection := by
  change ¬ prerequisites orthogonalProjection ⊆ prerequisites zeroAcceleration ∧
    ¬ prerequisites zeroAcceleration ⊆ prerequisites orthogonalProjection
  decide

end DualityDependency

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
  [CompleteSpace Space]

theorem conjugate_support_bounded (potential : ConvexFunctional Space) (point : Space) :
    BddAbove (potential.affineSet (potential.grad point)) := by
  refine ⟨⟪point, potential.grad point⟫ - potential.F point, ?_⟩
  rintro value ⟨candidate, rfl⟩
  have support := potential.supporting_ineq_of_convex_differentiable point candidate
  rw [inner_sub_right, ← real_inner_comm (potential.grad point) candidate,
    ← real_inner_comm (potential.grad point) point] at support
  linarith

theorem fenchel_young_at_gradient (potential : ConvexFunctional Space) (point : Space) :
    potential.F point + potential.legendre (potential.grad point) =
      ⟪point, potential.grad point⟫ :=
  potential.fenchel_young_eq_of_grad point (conjugate_support_bounded potential point)

def canonicalDivergence (potential : ConvexFunctional Space) (first second : Space) : ℝ :=
  potential.F second + potential.legendre (potential.grad first) -
    ⟪second, potential.grad first⟫

theorem canonical_divergence_eq_bregman
    (potential : ConvexFunctional Space) (first second : Space) :
    canonicalDivergence potential first second =
      potential.F second - potential.F first - ⟪potential.grad first, second - first⟫ := by
  have duality := fenchel_young_at_gradient potential first
  simp only [canonicalDivergence, inner_sub_right, real_inner_comm]
  linarith

theorem canonical_divergence_nonneg
    (potential : ConvexFunctional Space) (first second : Space) :
    0 ≤ canonicalDivergence potential first second := by
  rw [canonical_divergence_eq_bregman]
  have support := potential.supporting_ineq_of_convex_differentiable first second
  linarith

theorem canonical_divergence_self (potential : ConvexFunctional Space) (point : Space) :
    canonicalDivergence potential point point = 0 := by
  simp [canonical_divergence_eq_bregman]

theorem amari_three_point_identity
    (potential : ConvexFunctional Space) (first middle last : Space) :
    canonicalDivergence potential first last - canonicalDivergence potential first middle -
      canonicalDivergence potential middle last =
        ⟪last - middle, potential.grad middle - potential.grad first⟫ := by
  simp only [canonical_divergence_eq_bregman, inner_sub_left, inner_sub_right,
    real_inner_comm]
  ring

theorem amari_pythagorean
    (potential : ConvexFunctional Space) (first middle last : Space)
    (orthogonal : ⟪last - middle, potential.grad middle - potential.grad first⟫ = 0) :
    canonicalDivergence potential first last = canonicalDivergence potential first middle +
      canonicalDivergence potential middle last := by
  have identity := amari_three_point_identity potential first middle last
  rw [orthogonal] at identity
  linarith

theorem projection_decreases_divergence
    (potential : ConvexFunctional Space) (target projected initial : Space)
    (orthogonal : ⟪initial - projected, potential.grad projected - potential.grad target⟫ = 0) :
    canonicalDivergence potential target projected ≤ canonicalDivergence potential target initial := by
  rw [amari_pythagorean potential target projected initial orthogonal]
  exact le_add_of_nonneg_right (canonical_divergence_nonneg potential projected initial)

theorem projection_divergences_antitone
    (potential : ConvexFunctional Space) (target : Space) (iterate : ℕ → Space)
    (orthogonal : ∀ step,
      ⟪iterate step - iterate (step + 1),
        potential.grad (iterate (step + 1)) - potential.grad target⟫ = 0) :
    Antitone (fun step => canonicalDivergence potential target (iterate step)) := by
  apply antitone_nat_of_succ_le
  intro step
  exact projection_decreases_divergence potential target _ _ (orthogonal step)

theorem projection_divergences_converge
    (potential : ConvexFunctional Space) (target : Space) (iterate : ℕ → Space)
    (orthogonal : ∀ step,
      ⟪iterate step - iterate (step + 1),
        potential.grad (iterate (step + 1)) - potential.grad target⟫ = 0) :
    Tendsto (fun step => canonicalDivergence potential target (iterate step)) atTop
      (𝓝 (⨅ step, canonicalDivergence potential target (iterate step))) := by
  apply tendsto_atTop_ciInf (projection_divergences_antitone potential target iterate orthogonal)
  refine ⟨0, ?_⟩
  rintro value ⟨step, rfl⟩
  exact canonical_divergence_nonneg potential target (iterate step)

theorem dual_hessian_comp_primal
    (primal dual : ConvexFunctional Space)
    (inverse : Function.LeftInverse dual.grad primal.grad) (point : Space)
    (primal_diff : DifferentiableAt ℝ primal.grad point)
    (dual_diff : DifferentiableAt ℝ dual.grad (primal.grad point)) :
    (fderiv ℝ dual.grad (primal.grad point)).comp (fderiv ℝ primal.grad point) =
      ContinuousLinearMap.id ℝ Space := by
  have composition := dual_diff.hasFDerivAt.comp point primal_diff.hasFDerivAt
  have maps_equal : dual.grad ∘ primal.grad = id := funext inverse
  rw [maps_equal] at composition
  exact composition.unique (hasFDerivAt_id point)

theorem legendre_hessians_two_sided_inverse
    (primal dual : ConvexFunctional Space)
    (left_inverse : Function.LeftInverse dual.grad primal.grad)
    (right_inverse : Function.RightInverse dual.grad primal.grad) (point : Space)
    (primal_diff : DifferentiableAt ℝ primal.grad point)
    (dual_diff : DifferentiableAt ℝ dual.grad (primal.grad point)) :
    (fderiv ℝ dual.grad (primal.grad point)).comp (fderiv ℝ primal.grad point) =
        ContinuousLinearMap.id ℝ Space ∧
      (fderiv ℝ primal.grad point).comp (fderiv ℝ dual.grad (primal.grad point)) =
        ContinuousLinearMap.id ℝ Space := by
  constructor
  · exact dual_hessian_comp_primal primal dual left_inverse point primal_diff dual_diff
  · simpa only [left_inverse point] using
      dual_hessian_comp_primal dual primal right_inverse (primal.grad point) dual_diff
        (by simpa only [left_inverse point] using primal_diff)

def eCoordinateLine (first last : Space) : ℝ → Space := AffineMap.lineMap first last

def mCoordinateLine (first last : Space) : ℝ → Space := AffineMap.lineMap first last

omit [CompleteSpace Space] in
theorem coordinate_line_endpoints (first last : Space) :
    eCoordinateLine first last 0 = first ∧ eCoordinateLine first last 1 = last ∧
      mCoordinateLine first last 0 = first ∧ mCoordinateLine first last 1 = last := by
  simp [eCoordinateLine, mCoordinateLine]

omit [CompleteSpace Space] in
theorem hasDerivAt_eCoordinateLine (first last : Space) (time : ℝ) :
    HasDerivAt (eCoordinateLine first last) (last - first) time :=
  AffineMap.hasDerivAt_lineMap

omit [CompleteSpace Space] in
theorem hasDerivAt_mCoordinateLine (first last : Space) (time : ℝ) :
    HasDerivAt (mCoordinateLine first last) (last - first) time :=
  AffineMap.hasDerivAt_lineMap

omit [CompleteSpace Space] in
theorem coordinate_lines_zero_acceleration (first last : Space) (time : ℝ) :
    HasDerivAt (deriv (eCoordinateLine first last)) 0 time ∧
      HasDerivAt (deriv (mCoordinateLine first last)) 0 time := by
  have exponential_velocity : deriv (eCoordinateLine first last) = fun _time => last - first :=
    funext (fun time => (hasDerivAt_eCoordinateLine first last time).deriv)
  have mixture_velocity : deriv (mCoordinateLine first last) = fun _time => last - first :=
    funext (fun time => (hasDerivAt_mCoordinateLine first last time).deriv)
  rw [exponential_velocity, mixture_velocity]
  exact ⟨hasDerivAt_const time _, hasDerivAt_const time _⟩

theorem poisson_square_root_metric_pullback (radius : ℝ) (radius_pos : 0 < radius) :
    InfoGeometry.Canonical.FisherWoottersExtended.fisherDensity (radius ^ 2) *
      (deriv (fun value : ℝ => value ^ 2) radius) ^ 2 = 4 := by
  have derivative : HasDerivAt (fun value : ℝ => value ^ 2) (2 * radius) radius := by
    simpa using (hasDerivAt_id radius).pow 2
  rw [derivative.deriv]
  simp only [InfoGeometry.Canonical.FisherWoottersExtended.fisherDensity]
  field_simp [ne_of_gt radius_pos]
  ring

theorem poisson_unit_metric_pullback (radius : ℝ) (radius_pos : 0 < radius) :
    InfoGeometry.Canonical.FisherWoottersExtended.fisherDensity ((radius / 2) ^ 2) *
      (deriv (fun value : ℝ => (value / 2) ^ 2) radius) ^ 2 = 1 := by
  have derivative : HasDerivAt (fun value : ℝ => (value / 2) ^ 2) (radius / 2) radius := by
    convert ((hasDerivAt_id radius).div_const 2).pow 2 using 1
    simp
    ring
  rw [derivative.deriv]
  simp only [InfoGeometry.Canonical.FisherWoottersExtended.fisherDensity]
  field_simp [ne_of_gt radius_pos]

end

end InfoGeometry.Amari.DuallyFlatThermodynamics
