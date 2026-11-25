/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0.
-/
module

public import CoreLean.CutoffComparison
public import CoreLean.CutoffSummability

set_option linter.style.header.license
  "Released under Apache 2.0 license; see LICENSE-InfoGeometry-Apache-2.0." in
/-!
# Applying the cutoff remainder to normalized observables

This file joins the explicit relative-error inequality to the summability
theorem with the extra linear scale loss. The conclusion concerns the full
normalized sequence, and the quantitative bound retains all constants.

The physical ingredients still needed are positive partition functions,
a uniform bound on normalized observables, and the two displayed relative
comparison inequalities. These are substantive hypotheses about the RG
construction, not conclusions established by this generic analytic bridge.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace CoreLean.CutoffLimit

/-- The manuscript's cutoff error including the possible extra factor `K`.
The nonnegative offset `c` can be instantiated with `gbar⁻²`. -/
def linearLossRemainder (κ b c p : ℝ) (K : ℕ) : ℝ :=
  (K : ℝ) * ((K : ℝ) ^ (3 - κ / 2) * (Real.log (b * K + c)) ^ p)

/-- The actual logarithmic cutoff profile, including the linear scale loss,
is summable for a nonnegative real log exponent; its summability is derived
from `κ ≥ 13`. -/
theorem summable_linearLossRemainder {κ b c : ℝ}
    (hκ : 13 ≤ κ) (hb : 0 < b) (hc : 0 ≤ c) (p : ℝ) (hp : 0 ≤ p) :
    Summable (linearLossRemainder κ b c p) :=
  CutoffSummability.summable_cutoff_remainder_mul_cutoff hκ hb hc p hp

/-- Relative cutoff comparisons with the manuscript's logarithmic remainder
yield convergence of the full normalized sequence and an explicit tail
bound. Both comparison constants and the uniform normalized bound remain
visible in the conclusion. -/
theorem exists_limit_of_cutoff_remainder
    (N : ℕ → ℂ) (Z : ℕ → ℝ) (K₀ : ℕ) (p : ℝ) {κ b c B CN CZ : ℝ}
    (hκ : 13 ≤ κ) (hb : 0 < b) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hZ : ∀ k, 0 < Z (K₀ + k)) (hB : 0 ≤ B)
    (hN : ∀ k, ‖N (K₀ + (k + 1)) - N (K₀ + k)‖ ≤
      (CN * linearLossRemainder κ b c p (K₀ + k)) * Z (K₀ + k))
    (hPartition : ∀ k, |Z (K₀ + (k + 1)) - Z (K₀ + k)| ≤
      (CZ * linearLossRemainder κ b c p (K₀ + k)) * Z (K₀ + k))
    (hNormalized : ∀ k, ‖N (K₀ + (k + 1)) / (Z (K₀ + (k + 1)) : ℂ)‖ ≤ B) :
    ∃ limit : ℂ,
      Tendsto (fun k => N k / (Z k : ℂ)) atTop (𝓝 limit) ∧
      ∀ k, ‖N (K₀ + k) / (Z (K₀ + k) : ℂ) - limit‖ ≤
        (CN + B * CZ) * ∑' j, linearLossRemainder κ b c p (K₀ + (k + j)) := by
  have hs : Summable (fun k => linearLossRemainder κ b c p (K₀ + k)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff K₀).mpr (summable_linearLossRemainder hκ hb hc p hp)
  obtain ⟨limit, hlimit, htail⟩ :=
    CutoffComparison.exists_limit_of_relative_errors N Z
      (fun k => CN * linearLossRemainder κ b c p (K₀ + k))
      (fun k => CZ * linearLossRemainder κ b c p (K₀ + k)) K₀
      hZ hB hN hPartition hNormalized (hs.mul_left CN) (hs.mul_left CZ)
  refine ⟨limit, hlimit, fun k => (htail k).trans_eq ?_⟩
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  ring

end CoreLean.CutoffLimit
