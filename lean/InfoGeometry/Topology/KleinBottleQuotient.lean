import InfoGeometry.Topology.KleinAffineOrbitQuotient
import InfoGeometry.Arithmetic.ZetaCoordinateSymmetryBase
import InfoGeometry.Arithmetic.AmariZetaDuallyFlatGeometry

noncomputable section

namespace InfoGeometry.Topology.KleinBottleQuotient

open InfoGeometry.Topology.KleinAffineOrbitQuotient
open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry
open InfoGeometry.Arithmetic.AmariZeta

inductive DependencyNode
  | deckAction
  | orbitQuotient
  | invariantFields
  | affineReflection
  | fixedLocus
  | parameterEvaluation
  deriving DecidableEq, Fintype

def prerequisites : DependencyNode → Finset ℕ
  | .deckAction => {0}
  | .orbitQuotient => {0, 1}
  | .invariantFields => {0, 1, 2}
  | .affineReflection => {3}
  | .fixedLocus => {3, 4}
  | .parameterEvaluation => {3, 4, 5}

theorem prerequisites_injective : Function.Injective prerequisites := by decide

instance : PartialOrder DependencyNode :=
  PartialOrder.lift prerequisites prerequisites_injective

instance : DecidableRel (α := DependencyNode) (· ≤ ·) :=
  fun first second =>
    inferInstanceAs (Decidable (prerequisites first ⊆ prerequisites second))

theorem dependency_branches :
    DependencyNode.deckAction ≤ DependencyNode.orbitQuotient ∧
    DependencyNode.orbitQuotient ≤ DependencyNode.invariantFields ∧
    DependencyNode.affineReflection ≤ DependencyNode.fixedLocus ∧
    DependencyNode.fixedLocus ≤ DependencyNode.parameterEvaluation := by decide

theorem quotient_and_parameter_branches_incomparable :
    ¬ DependencyNode.orbitQuotient ≤ DependencyNode.parameterEvaluation ∧
    ¬ DependencyNode.parameterEvaluation ≤ DependencyNode.orbitQuotient := by decide

theorem glide_has_no_fixed_point (point : Plane) : deckB point ≠ point := by
  intro hfixed
  have hsecond := congrArg Prod.snd hfixed
  dsimp [deckB] at hsecond
  linarith

theorem glide_identified_in_quotient (point : Plane) :
    quotientMap (deckB point) = quotientMap point := by
  simpa [deckAct, deckAction, KleinDeckGroup.b, deckB, signR, signZ] using
    quotientMap_deckAct KleinDeckGroup.b point

theorem quotient_identification_without_fixed_points (point : Plane) :
    quotientMap (deckB point) = quotientMap point ∧ deckB point ≠ point :=
  ⟨glide_identified_in_quotient point, glide_has_no_fixed_point point⟩

theorem quotient_observable_is_glide_invariant {Target : Type*}
    (observable : KleinAffineQuotient → Target) (point : Plane) :
    observable (quotientMap (deckB point)) = observable (quotientMap point) := by
  rw [glide_identified_in_quotient]

theorem functional_reflection_involutive : Function.Involutive functionalReflection := by
  intro parameter
  simp [functionalReflection]

theorem functional_reflection_fixed_iff (parameter : ℂ) :
    functionalReflection parameter = parameter ↔ parameter = 1 / 2 := by
  constructor
  · intro hfixed
    change 1 - parameter = parameter at hfixed
    calc
      parameter = (parameter + (1 - parameter)) / 2 := by rw [hfixed]; ring
      _ = 1 / 2 := by ring
  · rintro rfl
    norm_num [functionalReflection]

theorem critical_reflection_fixed_iff (parameter : ℂ) :
    antiunitaryCriticalReflection parameter = parameter ↔ parameter.re = 1 / 2 := by
  constructor
  · intro hfixed
    have hreal := congrArg Complex.re hfixed
    simp [antiunitaryCriticalReflection] at hreal
    linarith
  · intro hreal
    apply Complex.ext
    · simp [antiunitaryCriticalReflection]
      linarith
    · simp [antiunitaryCriticalReflection]

theorem parameter_reflection_invariant (parameter : ℂ) :
    fisherRaoMetric (functionalReflection parameter) = fisherRaoMetric parameter := by
  unfold fisherRaoMetric functionalReflection
  ring

theorem parameter_at_functional_fixed_point {parameter : ℂ}
    (hfixed : functionalReflection parameter = parameter) :
    fisherRaoMetric parameter = 1 / 4 := by
  rw [(functional_reflection_fixed_iff parameter).mp hfixed]
  norm_num [fisherRaoMetric]

theorem critical_line_parameter_lower_bound (height : ℝ) :
    (1 / 4 : ℝ) ≤
      (fisherRaoMetric ((1 / 2 : ℂ) + Complex.I * (height : ℂ))).re := by
  rw [fisherRaoMetric_on_critical_line]
  norm_num [Complex.add_re, Complex.mul_re, pow_two]
  nlinarith [sq_nonneg height]

theorem critical_line_parameter_eq_quarter_iff (height : ℝ) :
    fisherRaoMetric ((1 / 2 : ℂ) + Complex.I * (height : ℂ)) = 1 / 4 ↔
      height = 0 := by
  rw [fisherRaoMetric_on_critical_line]
  constructor
  · intro heq
    have hreal := congrArg Complex.re heq
    norm_num at hreal
    nlinarith [sq_nonneg height]
  · rintro rfl
    norm_num

theorem reflected_parameters_can_have_zero_value :
    functionalReflection (0 : ℂ) = 1 ∧
    fisherRaoMetric (0 : ℂ) = 0 ∧ fisherRaoMetric (1 : ℂ) = 0 := by
  norm_num [functionalReflection, fisherRaoMetric]

theorem no_unconditional_quarter_lower_bound :
    ¬ ∀ parameter : ℂ, (1 / 4 : ℝ) ≤ (fisherRaoMetric parameter).re := by
  intro hbound
  have hzero := hbound 0
  norm_num [fisherRaoMetric] at hzero

end InfoGeometry.Topology.KleinBottleQuotient
