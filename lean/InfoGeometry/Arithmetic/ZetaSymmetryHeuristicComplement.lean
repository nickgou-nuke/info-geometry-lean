import Mathlib.Tactic

/-!
# Zeta Symmetry Heuristic Complement

Centered coordinates make the functional-equation symmetry transparent, but the
symmetry alone is not a critical-line theorem.

This module records the precise finite logic:

* `s = 1/2 + z` turns `s ↦ 1 - s` into `z ↦ -z`;
* an even centered function reflects zeros in pairs;
* evenness alone permits off-axis zeros;
* a separate `NoOffAxisZeros` complement is the exact missing selection
  hypothesis needed to conclude `re z = 0`.

No theorem here asserts the Riemann hypothesis, analytic continuation, or that
the completed zeta zeros satisfy the complement.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement

/-- Recovery from centered coordinates: `s = 1/2 + z`. -/
def criticalCentered (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + z

/-- The centered critical line is the imaginary axis in `z = s - 1/2`. -/
def centeredCriticalLine (z : ℂ) : Prop :=
  z.re = 0

/-- A function is even in centered coordinates when it is invariant under `z ↦ -z`. -/
def EvenCentered (F : ℂ → ℂ) : Prop :=
  ∀ z, F (-z) = F z

/-- Pointwise zero predicate. -/
def ZeroAt (F : ℂ → ℂ) (z : ℂ) : Prop :=
  F z = 0

/-- In centered coordinates, the functional-equation reflection is central inversion. -/
theorem one_sub_criticalCentered (z : ℂ) :
    (1 : ℂ) - criticalCentered z = criticalCentered (-z) := by
  unfold criticalCentered
  ring

/-- Evenness reflects zeros, but only to the opposite centered point. -/
theorem even_zero_reflection {F : ℂ → ℂ} (hEven : EvenCentered F) {z : ℂ}
    (hz : ZeroAt F z) :
    ZeroAt F (-z) := by
  unfold ZeroAt
  rw [hEven z, hz]

/-! ## Counterexample to the heuristic implication -/

/-- A minimal even function with off-axis zeros: `z^2 - 1`. -/
def evenOffAxisWitness (z : ℂ) : ℂ :=
  z ^ 2 - 1

/-- The witness is centered-even. -/
theorem evenOffAxisWitness_even : EvenCentered evenOffAxisWitness := by
  intro z
  unfold evenOffAxisWitness
  ring

/-- `z = 1` is a zero of the witness. -/
theorem evenOffAxisWitness_one_zero : ZeroAt evenOffAxisWitness (1 : ℂ) := by
  unfold ZeroAt evenOffAxisWitness
  norm_num

/-- `z = -1` is the reflected zero of the witness. -/
theorem evenOffAxisWitness_neg_one_zero : ZeroAt evenOffAxisWitness (-1 : ℂ) := by
  simpa using
    (even_zero_reflection evenOffAxisWitness_even evenOffAxisWitness_one_zero)

/-- The zero `z = 1` is not on the centered critical line. -/
theorem one_not_centeredCriticalLine : ¬ centeredCriticalLine (1 : ℂ) := by
  unfold centeredCriticalLine
  norm_num

/--
Even centered symmetry does not imply critical-line confinement.  The polynomial
`z^2 - 1` is even, has the reflected zero-pair `±1`, and `re 1 ≠ 0`.
-/
theorem even_symmetry_allows_off_axis_zero_pair :
    ∃ F : ℂ → ℂ, ∃ z : ℂ,
      EvenCentered F ∧ ZeroAt F z ∧ ZeroAt F (-z) ∧ z.re ≠ 0 := by
  refine ⟨evenOffAxisWitness, (1 : ℂ), evenOffAxisWitness_even,
    evenOffAxisWitness_one_zero, ?_, ?_⟩
  · simpa using evenOffAxisWitness_neg_one_zero
  · norm_num

/-! ## The explicit complement needed for confinement -/

/--
The complement that symmetry does not supply: there are no zeros with nonzero
centered real part.
-/
def NoOffAxisZeros (F : ℂ → ℂ) : Prop :=
  ∀ z, ZeroAt F z → z.re ≠ 0 → False

/-- The complement is exactly what converts a zero into a critical-line point. -/
theorem centeredCriticalLine_of_noOffAxisZeros {F : ℂ → ℂ} {z : ℂ}
    (hNo : NoOffAxisZeros F) (hz : ZeroAt F z) :
    centeredCriticalLine z := by
  unfold centeredCriticalLine
  by_contra hzre
  exact hNo z hz hzre

/--
The honest package: centered evenness gives the reflected zero, while the
separate no-off-axis complement gives critical-line confinement.
-/
theorem zero_reflection_and_confinement_of_even_and_complement {F : ℂ → ℂ}
    (hEven : EvenCentered F) (hNo : NoOffAxisZeros F) {z : ℂ}
    (hz : ZeroAt F z) :
    ZeroAt F (-z) ∧ centeredCriticalLine z := by
  exact ⟨even_zero_reflection hEven hz, centeredCriticalLine_of_noOffAxisZeros hNo hz⟩

end InfoGeometry.Arithmetic.ZetaSymmetryHeuristicComplement

