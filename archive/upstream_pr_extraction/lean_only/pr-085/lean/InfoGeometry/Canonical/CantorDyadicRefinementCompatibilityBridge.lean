import Mathlib.Tactic
import InfoGeometry.Canonical.CantorDyadicDifferenceScaleBridge

/-!
# Refinement compatibility for dyadic difference operators

The refinement map and the translations are supplied data.  The theorem below
is the exact finite-level intertwining law; it does not assert existence of a
Cantor refinement or convergence to an unbounded momentum generator.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorDyadicRefinementCompatibilityBridge

open InfoGeometry.Canonical.CantorDyadicDifferenceScaleBridge

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem dyadicDifference_refinement_intertwines
    {Hn Hnext : Type*} [AddCommGroup Hn] [AddCommGroup Hnext]
    [Module ℝ Hn] [Module ℝ Hnext]
    (r : Hn →ₗ[ℝ] Hnext)
    (Tn : Hn →ₗ[ℝ] Hn) (Tnext : Hnext →ₗ[ℝ] Hnext)
    (hcompat : r.comp Tn = Tnext.comp r) :
    ∀ f : Hn,
      (2 : ℝ) ^ (n + 1) • (r f - Tnext (r f)) =
        ((2 : ℝ) * (2 : ℝ) ^ n) • r (f - Tn f) := by
  intro f
  have hpoint : r (Tn f) = Tnext (r f) := by
    exact LinearMap.congr_fun hcompat f
  rw [map_sub]
  rw [← hpoint, pow_succ]
  rw [mul_comm ((2 : ℝ) ^ n) 2]

end InfoGeometry.Canonical.CantorDyadicRefinementCompatibilityBridge
