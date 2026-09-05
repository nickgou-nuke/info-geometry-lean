import InfoGeometry.External.Auto.SarsModularWeakValue
import InfoGeometry.Physics.NuclearWignerSupermultipletSymmetry

/-!
# Guarded weak values and amplification without automatic dynamics

The existing Option-valued definition is retained, including its undefined
orthogonal case. Complex weak values are distinct from positive conditional
expectations. No semantic velocity, measurement instrument, or retrocausal
physical process is inferred from their algebraic formula.
-/

noncomputable section
namespace InfoGeometry.Streaming.WeakValueBoundary

open SarsModularWeakValue
open InfoGeometry.Physics.NuclearWignerSupermultiplet

/-- The identity cannot be amplified, regardless of a small nonzero overlap. -/
theorem identity_weak_value (ψ φ : State2) (h : weakDenominator ψ φ ≠ 0) :
    weakValue? (1 : M2C) ψ φ = some 1 := by
  rw [weak_value_some_of_nonorthogonal _ _ _ h]
  have hn : weakNumerator (1 : M2C) ψ φ = weakDenominator ψ φ := by
    simp [weakNumerator, weakDenominator, matVec, cinner]
  rw [hn, div_self h]

/-- Linearity in the probe is valid on the regular overlap domain. -/
theorem weak_probe_add (A B : M2C) (ψ φ : State2) (h : weakDenominator ψ φ ≠ 0) :
    weakValue? (A + B) ψ φ =
      some (weakNumerator A ψ φ / weakDenominator ψ φ +
        weakNumerator B ψ φ / weakDenominator ψ φ) := by
  rw [weak_value_some_of_nonorthogonal _ _ _ h]
  congr 1
  have hn : weakNumerator (A + B) ψ φ = weakNumerator A ψ φ + weakNumerator B ψ φ := by
    simp [weakNumerator, cinner, matVec]
    ring
  rw [hn, add_div]

/-- An explicit nearly orthogonal post-selection direction; normalization cancels in the ratio. -/
def postDirection (ε : ℝ) : State2 := ![(ε : ℂ), 1]

theorem post_overlap (ε : ℝ) : weakDenominator ket0 (postDirection ε) = (ε : ℂ) := by
  simp [weakDenominator, cinner, ket0, postDirection]

theorem pauli_probe_numerator (ε : ℝ) : weakNumerator pauli1 ket0 (postDirection ε) = 1 := by
  simp [weakNumerator, cinner, matVec, ket0, postDirection, pauli1]

/-- A genuine anomalous ratio for a fixed bounded two-level probe. -/
theorem pauli_weak_amplification (ε : ℝ) (hε : ε ≠ 0) :
    weakValue? pauli1 ket0 (postDirection ε) = some ((ε : ℂ)⁻¹) := by
  have hc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  rw [weak_value_some_of_nonorthogonal _ _ _ (by rwa [post_overlap]),
    pauli_probe_numerator, post_overlap, one_div]

/-- Exactly orthogonal selection is undefined, not an infinite weak value. -/
theorem orthogonal_probe_undefined : weakValue? pauli1 ket0 (postDirection 0) = none := by
  apply weak_value_none_of_orthogonal
  simp [post_overlap]

/-- Normalized squared-overlap readout of the two explicitly specified directions. -/
def postSuccess (ε : ℝ) : ℝ :=
  Complex.normSq (weakDenominator ket0 (postDirection ε)) /
    (Complex.normSq (postDirection ε 0) + Complex.normSq (postDirection ε 1))

theorem postSuccess_eq (ε : ℝ) : postSuccess ε = ε ^ 2 / (1 + ε ^ 2) := by
  simp [postSuccess, post_overlap, postDirection, Complex.normSq_apply, pow_two, add_comm]

/-- The amplification probability cost is kept in the same exact calculation. -/
theorem amplification_success_product (ε : ℝ) (hε : ε ≠ 0) :
    postSuccess ε * (ε⁻¹) ^ 2 = 1 / (1 + ε ^ 2) := by
  rw [postSuccess_eq]
  have hd : 1 + ε ^ 2 ≠ 0 := by positivity
  field_simp [hε, hd]
  ring

theorem amplification_success_bound (ε : ℝ) (hε : ε ≠ 0) :
    postSuccess ε * (ε⁻¹) ^ 2 ≤ 1 := by
  rw [amplification_success_product ε hε]
  have hp : 0 < 1 + ε ^ 2 := by positivity
  apply (div_le_one hp).2
  nlinarith [sq_nonneg ε]

/-- Nonzero scalar changes of a post-selection vector do not change the weak ratio. -/
theorem weak_post_rescaling (A : M2C) (ψ φ : State2) (c : ℂ)
    (hc : c ≠ 0) (h : weakDenominator ψ φ ≠ 0) :
    weakValue? A ψ (c • φ) = weakValue? A ψ φ := by
  have hden : weakDenominator ψ (c • φ) = star c * weakDenominator ψ φ := by
    simp [weakDenominator, cinner]
    ring
  have hnum : weakNumerator A ψ (c • φ) = star c * weakNumerator A ψ φ := by
    simp [weakNumerator, cinner]
    ring
  have hcs : star c ≠ 0 := by simpa using hc
  rw [weak_value_some_of_nonorthogonal _ _ _ (by rw [hden]; exact mul_ne_zero hcs h),
    weak_value_some_of_nonorthogonal _ _ _ h, hden, hnum]
  congr 1
  field_simp [hcs, h]

end InfoGeometry.Streaming.WeakValueBoundary
