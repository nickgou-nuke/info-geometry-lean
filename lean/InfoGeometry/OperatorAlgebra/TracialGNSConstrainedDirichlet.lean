/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.ConstrainedDirichletLaplacian
import InfoGeometry.OperatorAlgebra.TracialGNSDirichlet

/-!
# Energy-constrained commutator mobility on the completed tracial GNS space

The existing bounded inner commutators are compressed onto the orthogonal
complement of a specified energy direction. The projection stays in the
dense coefficient algebra and has an explicit ordered formula. Faithfulness
is needed only to turn a zero GNS commutator into a coefficient-algebra
commutation equation.

The complex Hilbert carrier is the repository's existing native GNS space.
No simultaneous diagonalization or commutativity of the coefficient algebra
or the commutator family is imposed.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open InfoGeometry.Analysis.ConstrainedDirichletLaplacian

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)
variable (htr : ∀ a b : A, f (a * b) = f (b * a))
variable {ι : Type*} [Fintype ι]

/-- The coefficient representative of the GNS orthogonal energy projection.
The order in both trace pairings is fixed. A zero denominator is handled by
the native inverse convention, just as for projection onto the zero vector. -/
def energyProjectedStatistic (e a : A) : A :=
  a - (f (star e * a) / f (star e * e)) • e

/-- The completed GNS projection has an actual coefficient representative. -/
theorem energyProjection_toPreGNS (e a : A) :
    energyProjection (f.toPreGNS e : f.GNS) (f.toPreGNS a) =
      (f.toPreGNS (f.energyProjectedStatistic e a) : f.GNS) := by
  have hinner : inner ℂ (f.toPreGNS e : f.GNS) (f.toPreGNS a) =
      f (star e * a) := by
    simp only [UniformSpace.Completion.inner_coe, preGNS_inner_def,
      ofPreGNS_toPreGNS]
  have hnorm : (((‖(f.toPreGNS e : f.GNS)‖ ^ 2 : ℝ) : ℂ)) =
      f (star e * e) := by
    simp only [UniformSpace.Completion.norm_coe, Complex.ofReal_pow,
      preGNS_norm_sq, ofPreGNS_toPreGNS]
  rw [energyProjection_apply, hinner, hnorm]
  simp only [energyProjectedStatistic, map_sub, map_smul,
    UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_smul]

/-- The actual bounded energy-constrained commutator mobility. -/
def tracialConstrainedDirichletGNS (H : ι → A) (e : A) :
    f.GNS →L[ℂ] f.GNS :=
  constrainedLaplacian (fun i => f.tracialCommutatorGNS htr (H i))
    (f.toPreGNS e : f.GNS)

theorem tracialConstrainedDirichletGNS_isPositive (H : ι → A) (e : A) :
    (f.tracialConstrainedDirichletGNS htr H e).IsPositive :=
  constrainedLaplacian_isPositive _ _

/-- The energy kernel is a consequence of the projection construction. -/
@[simp] theorem tracialConstrainedDirichletGNS_energy (H : ι → A) (e : A) :
    f.tracialConstrainedDirichletGNS htr H e (f.toPreGNS e) = 0 :=
  constrainedLaplacian_energy _ _

/-- No commutativity assumption is needed for this exact positive-square identity. -/
theorem re_inner_tracialConstrainedDirichletGNS_toPreGNS
    (H : ι → A) (e a : A) :
    (inner ℂ (f.toPreGNS a : f.GNS)
      (f.tracialConstrainedDirichletGNS htr H e (f.toPreGNS a))).re =
      ∑ i, (f (star (H i * f.energyProjectedStatistic e a -
          f.energyProjectedStatistic e a * H i) *
        (H i * f.energyProjectedStatistic e a -
          f.energyProjectedStatistic e a * H i))).re := by
  rw [tracialConstrainedDirichletGNS, re_inner_constrainedLaplacian]
  simp only [energyProjection_toPreGNS, tracialCommutatorGNS_toPreGNS,
    gns_norm_sq_toPreGNS]

/-- On faithful coefficients, the projected statistic must lie in the joint
commutant exactly when its dissipative motion vanishes. -/
theorem tracialConstrainedDirichletGNS_toPreGNS_eq_zero_iff
    (hfaith : ∀ a : A, f (star a * a) = 0 → a = 0)
    (H : ι → A) (e a : A) :
    f.tracialConstrainedDirichletGNS htr H e (f.toPreGNS a) = 0 ↔
      ∀ i, Commute (H i) (f.energyProjectedStatistic e a) := by
  rw [tracialConstrainedDirichletGNS, constrainedLaplacian_apply_eq_zero_iff]
  simp only [energyProjection_toPreGNS, tracialCommutatorGNS_toPreGNS,
    f.toPreGNS_coe_eq_zero_iff_of_faithful hfaith, sub_eq_zero, commute_iff_eq]

/-- Zero entropy production tests the projected joint commutant, not
commutativity of the unprojected entropy statistic. -/
theorem re_inner_tracialConstrainedDirichletGNS_eq_zero_iff
    (hfaith : ∀ a : A, f (star a * a) = 0 → a = 0)
    (H : ι → A) (e a : A) :
    (inner ℂ (f.toPreGNS a : f.GNS)
      (f.tracialConstrainedDirichletGNS htr H e (f.toPreGNS a))).re = 0 ↔
      ∀ i, Commute (H i) (f.energyProjectedStatistic e a) := by
  change (inner ℂ (f.toPreGNS a : f.GNS)
    (constrainedLaplacian (fun i => f.tracialCommutatorGNS htr (H i))
      (f.toPreGNS e : f.GNS) (f.toPreGNS a))).re = 0 ↔ _
  rw [re_inner_constrainedLaplacian_eq_zero_iff]
  simp only [energyProjection_toPreGNS, tracialCommutatorGNS_toPreGNS,
    f.toPreGNS_coe_eq_zero_iff_of_faithful hfaith, sub_eq_zero, commute_iff_eq]

/-- Strictly positive production detects a surviving noncommuting direction
after the energy component has been removed. -/
theorem re_inner_tracialConstrainedDirichletGNS_pos_iff
    (hfaith : ∀ a : A, f (star a * a) = 0 → a = 0)
    (H : ι → A) (e a : A) :
    0 < (inner ℂ (f.toPreGNS a : f.GNS)
      (f.tracialConstrainedDirichletGNS htr H e (f.toPreGNS a))).re ↔
      ∃ i, ¬ Commute (H i) (f.energyProjectedStatistic e a) := by
  change 0 < (inner ℂ (f.toPreGNS a : f.GNS)
    (constrainedLaplacian (fun i => f.tracialCommutatorGNS htr (H i))
      (f.toPreGNS e : f.GNS) (f.toPreGNS a))).re ↔ _
  rw [re_inner_constrainedLaplacian_pos_iff]
  simp only [energyProjection_toPreGNS, tracialCommutatorGNS_toPreGNS,
    ne_eq, f.toPreGNS_coe_eq_zero_iff_of_faithful hfaith,
    sub_eq_zero, commute_iff_eq]

end PositiveLinearMap
