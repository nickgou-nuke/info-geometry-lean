import InfoGeometry.Canonical.CurrentSugawaraMetricDatum
import Mathlib.Tactic

/-!
# Metric Sugawara bridge

This file records the finite-channel Sugawara kernel used by the metric datum
layer.

It packages the channel-indexed normal-ordered pair and the explicit
`kappa`-contracted stress kernel.  The full Virasoro bracket theorem is still
owned by the existing single-current Sugawara lane; this file only introduces
the finite-channel operator formula in a repo-native form.
-/

namespace InfoGeometry.Canonical.MetricSugawaraBridge

open scoped BigOperators
open CurrentSugawaraMetricDatum
open CurrentMetricDatum

variable {𝕜 I V : Type*}
variable [Field 𝕜] [Fintype I] [DecidableEq I]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Channel-indexed normal-ordered pair of current operators. -/
noncomputable def channelPairNO
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (i j : I) (m n : ℤ) : V →ₗ[𝕜] V :=
  if n ≤ m then (H.J j n).comp (H.J i m) else (H.J i m).comp (H.J j n)

@[simp] theorem channelPairNO_def
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (i j : I) (m n : ℤ) :
    channelPairNO H i j m n =
      (if n ≤ m then (H.J j n).comp (H.J i m) else (H.J i m).comp (H.J j n)) := by
  rfl

/--
Explicit finite-channel Sugawara kernel.

This is the formal finite-channel version of

`L_n = 1/2 ∑_{k,i,j} κ^{ij} :J_{i,n-k} J_{j,k}:`

written directly as a finitely supported sum of operator values.
-/
noncomputable def channelSugawaraKernel
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (n : ℤ) : V → V :=
  fun v =>
    (2 : 𝕜)⁻¹ • ∑ᶠ k, ∑ i, ∑ j, H.metric.kappaInv i j •
      channelPairNO H i j (n - k) k v

@[simp] theorem channelSugawaraKernel_def
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (n : ℤ) (v : V) :
    channelSugawaraKernel H n v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, ∑ i, ∑ j, H.metric.kappaInv i j •
        channelPairNO H i j (n - k) k v := by
  rfl

/-- The split 8-channel kernel uses the canonical split metric datum. -/
noncomputable def splitEightKernel
    (V : Type*) [AddCommGroup V] [Module ℝ V] :
    CurrentMetricDatum.MetricHeisenbergCurrent ℝ V (Fin 8) →
      ℤ → V → V :=
  channelSugawaraKernel

@[simp] theorem splitEightKernel_def
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    (H : CurrentMetricDatum.MetricHeisenbergCurrent ℝ V (Fin 8))
    (n : ℤ) (v : V) :
    splitEightKernel (V := V) H n v =
      (2 : ℝ)⁻¹ • ∑ᶠ k, ∑ i : Fin 8, ∑ j : Fin 8, H.metric.kappaInv i j •
        channelPairNO H i j (n - k) k v := by
  rfl

end InfoGeometry.Canonical.MetricSugawaraBridge
