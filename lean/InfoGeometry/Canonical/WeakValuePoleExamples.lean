import InfoGeometry.Streaming.WeakValueBoundary
import InfoGeometry.Canonical.WeakValuePoleCriterion
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact poles and counterexamples for the existing guarded weak value

The native owner returns `none` at zero overlap. Limits below concern the
punctured regular domain. A Pauli probe has a real pole, the identity has exact
numerator cancellation, and another Hermitian Pauli probe has a purely
imaginary pole. No physical momentum operator or fluid equation is identified.
-/

noncomputable section

namespace InfoGeometry.Canonical.WeakValuePoleExamples

open SarsModularWeakValue InfoGeometry.Streaming.WeakValueBoundary
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open Filter
open scoped Topology

/-- Real readout retains the existing Option-valued domain guard. -/
def guardedReal (A : M2C) (psi phi : State2) : Option ℝ :=
  (weakValue? A psi phi).map Complex.re

/-- Totalized scalar expression used only for punctured-limit calculations. -/
def pauliReal (epsilon : ℝ) : ℝ :=
  (weakNumerator pauli1 ket0 (postDirection epsilon) /
    weakDenominator ket0 (postDirection epsilon)).re

theorem pauliReal_eq (epsilon : ℝ) : pauliReal epsilon = epsilon⁻¹ := by
  simp [pauliReal, pauli_probe_numerator, post_overlap]

theorem guarded_pauli_real (epsilon : ℝ) (h : epsilon ≠ 0) :
    guardedReal pauli1 ket0 (postDirection epsilon) = some epsilon⁻¹ := by
  simp [guardedReal, pauli_weak_amplification epsilon h]

theorem guarded_pauli_at_zero : guardedReal pauli1 ket0 (postDirection 0) = none := by
  simp [guardedReal, orthogonal_probe_undefined]

/-- The existing Pauli family has a genuine one-sided real pole. -/
theorem pauliReal_tendsto_atTop : Tendsto pauliReal (𝓝[>] (0 : ℝ)) atTop := by
  rw [show pauliReal = (fun r : ℝ => r⁻¹) from funext pauliReal_eq]
  exact tendsto_inv_nhdsGT_zero

/-- A readout pole alone does not force a spatial derivative pole. -/
theorem real_pole_with_zero_spatial_derivative :
    ∃ u : ℝ → ℝ → ℝ,
      Tendsto (fun t => u t 0) (𝓝[>] (0 : ℝ)) atTop ∧
      (∀ t x : ℝ, deriv (u t) x = 0) := by
  exact ⟨fun t _ => pauliReal t, pauliReal_tendsto_atTop,
    fun t x => (hasDerivAt_const x (pauliReal t)).deriv⟩

/-- The same vanishing-overlap family has no identity-probe amplification. -/
theorem identity_readout_no_amplification (epsilon : ℝ) (h : epsilon ≠ 0) :
    guardedReal (1 : M2C) ket0 (postDirection epsilon) = some 1 := by
  have hd : weakDenominator ket0 (postDirection epsilon) ≠ 0 := by
    rw [post_overlap]
    exact_mod_cast h
  simp [guardedReal, identity_weak_value ket0 (postDirection epsilon) hd]

theorem imaginary_pauli_numerator (epsilon : ℝ) :
    weakNumerator pauli2 ket0 (postDirection epsilon) = Complex.I := by
  simp [weakNumerator, matVec, cinner, pauli2, ket0, postDirection]

/-- A nonzero purely imaginary residue produces zero real readout. -/
theorem imaginary_pauli_real_zero (epsilon : ℝ) (h : epsilon ≠ 0) :
    guardedReal pauli2 ket0 (postDirection epsilon) = some 0 := by
  have hd : weakDenominator ket0 (postDirection epsilon) ≠ 0 := by
    rw [post_overlap]
    exact_mod_cast h
  rw [guardedReal, weak_value_some_of_nonorthogonal _ _ _ hd,
    imaginary_pauli_numerator, post_overlap]
  simp [Complex.div_re]

/-- This is the normalized postselection surprisal, not fluid enstrophy. -/
def postselectionBarrier (epsilon : ℝ) : ℝ := -Real.log (postSuccess epsilon)

theorem postselectionBarrier_eq (epsilon : ℝ) (h : epsilon ≠ 0) :
    postselectionBarrier epsilon = Real.log (1 + epsilon ^ 2) - 2 * Real.log |epsilon| := by
  have hp : 1 + epsilon ^ 2 ≠ 0 := by positivity
  rw [postselectionBarrier, postSuccess_eq, Real.log_div (pow_ne_zero 2 h) hp,
    Real.log_pow]
  rw [Real.log_abs]
  ring

theorem postselectionBarrier_lower (epsilon : ℝ) (h : epsilon ≠ 0) :
    -2 * Real.log |epsilon| ≤ postselectionBarrier epsilon := by
  rw [postselectionBarrier_eq epsilon h]
  have hn : 0 ≤ Real.log (1 + epsilon ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg epsilon])
  linarith

/-- The normalized postselection barrier diverges at the overlap node. -/
theorem postselectionBarrier_tendsto_atTop :
    Tendsto postselectionBarrier (𝓝[≠] (0 : ℝ)) atTop := by
  have hlog : Tendsto (fun r : ℝ => -2 * Real.log |r|) (𝓝[≠] (0 : ℝ)) atTop := by
    simpa only [Real.log_abs] using
      (Filter.Tendsto.const_mul_atBot_of_neg (by norm_num : (-2 : ℝ) < 0)
        Real.tendsto_log_nhdsNE_zero)
  apply tendsto_atTop_mono' (𝓝[≠] (0 : ℝ)) _ hlog
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact postselectionBarrier_lower r (by simpa using hr)

/-- A genuine simple pole of the existing two-boundary readout, with explicit
real-residue and differentiability hypotheses and the native Option guard. -/
theorem guarded_real_pole {A : ℝ → M2C} {psi phi : ℝ → State2}
    {t0 : ℝ} {c : ℂ}
    (hd0 : weakDenominator (psi t0) (phi t0) = 0)
    (hd : HasDerivAt (fun t => weakDenominator (psi t) (phi t)) c t0)
    (hc : c ≠ 0)
    (hn : ContinuousAt (fun t => weakNumerator (A t) (psi t) (phi t)) t0)
    (hr : (weakNumerator (A t0) (psi t0) (phi t0) / c).re ≠ 0) :
    ∀ᶠ t in 𝓝[≠] t0, ∃ w : ℂ,
      weakValue? (A t) (psi t) (phi t) = some w ∧
      (|(weakNumerator (A t0) (psi t0) (phi t0) / c).re| / 2) / |t - t0| ≤ |w.re| := by
  filter_upwards [WeakValuePoleCriterion.eventually_abs_readout_lower_bound
    hd0 hd hc hn hr] with t ht
  exact ⟨_, weak_value_some_of_nonorthogonal _ _ _ ht.1, ht.2⟩

end InfoGeometry.Canonical.WeakValuePoleExamples
