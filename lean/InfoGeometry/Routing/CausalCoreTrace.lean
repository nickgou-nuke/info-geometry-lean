/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.CausalRouteDynamics
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A coupling-independent causal core diagnostic

For causal deterministic routes every recurrent point is fixed. Consequently
the trace of the stabilized Drazin core equals the trace of the original route.
For any exact mixture supported on causal routes, expected core trace is just
the diagonal sum of the attention matrix. The final theorem consumes the
native product-coupling decomposition and requires no route enumeration at
runtime. No analogous coupling independence is asserted for noncausal routes.
-/

namespace InfoGeometry.Routing.AttentionPolytope
open Matrix DeterministicArgmaxAttention
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open InfoGeometry.Routing.CausalRouteDynamics
open scoped BigOperators

variable {n : ℕ}

/-- Causal routing has no nontrivial cycles, so every positive power has the same trace. -/
theorem causal_deterministic_trace_pow (f : Fin n → Fin n) (hf : ∀ i, f i ≤ i)
    {r : ℕ} (hr : 0 < r) :
    trace (deterministicAttention f ^ r) = trace (deterministicAttention f) := by
  rw [deterministic_pow]
  apply Finset.sum_congr rfl
  intro i _
  change (if i = f^[r] i then (1 : ℝ) else 0) = if i = f i then 1 else 0
  have hi : i = f^[r] i ↔ i = f i := by
    simpa only [eq_comm] using iterate_fixed_iff f hf hr i
  simpa only [hi]

/-- Core trace is independent of the supplied valid Drazin witness and its exponent. -/
theorem causal_deterministic_core_trace (f : Fin n → Fin n) (hf : ∀ i, f i ≤ i)
    {D : Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    (hD : IsDrazinInverse (deterministicAttention f) D k) :
    trace (projection (deterministicAttention f) D) = trace (deterministicAttention f) := by
  have hd := unique_of_indices hD (causal_deterministic_drazin f hf)
  rw [hd, causal_deterministic_projection f hf]
  cases n with
  | zero => simp [Matrix.trace]
  | succ n => exact causal_deterministic_trace_pow f hf (Nat.succ_pos n)

/-- Any exact causal coupling has the same weighted core trace. Positivity is not
needed for this linear identity; probability couplings are a special case. -/
theorem causal_mixture_core_trace (P : Matrix (Fin n) (Fin n) ℝ)
    (w : (Fin n → Fin n) → ℝ)
    (hsupport : ∀ f, w f ≠ 0 → ∀ i, f i ≤ i)
    (hreconstruct : (∑ f, w f • deterministicAttention f) = P) :
    (∑ f, w f * trace (projection (deterministicAttention f)
      (deterministicAttention f ^ n))) = trace P := by
  calc
    _ = ∑ f, w f * trace (deterministicAttention f) := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases hw : w f = 0
      · simp only [hw, zero_mul]
      · rw [causal_deterministic_core_trace f (hsupport f hw)
          (causal_deterministic_drazin f (hsupport f hw))]
    _ = trace (∑ f, w f • deterministicAttention f) := by
      simp only [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
    _ = trace P := congrArg trace hreconstruct

/-- Expected causal Drazin core trace is a diagonal-sum diagnostic of attention,
not an exponential-time sum that must be evaluated by enumerating routes. -/
theorem attention_expected_causal_core_trace (P : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1)
    (hcausal : ∀ i j, i < j → P i j = 0) :
    (∑ f, routeWeight P f * trace (projection (deterministicAttention f)
      (deterministicAttention f ^ n))) = trace P := by
  exact causal_mixture_core_trace P (routeWeight P)
    (nonzero_causal_route P hcausal) (reconstruct P hrow)

end InfoGeometry.Routing.AttentionPolytope
