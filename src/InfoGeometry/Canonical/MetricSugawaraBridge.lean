/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CurrentSugawaraMetricDatum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Metric Sugawara Bridge

This module defines the channel-indexed normal-ordered current pair `channelPairNO`
and the `kappaInv`-contracted finite-channel Sugawara stress kernel
`channelSugawaraKernel`, together with its 8-channel split specialization
`splitEightKernel`, and proves their evaluation and mode-ordering identities.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.CurrentSugawaraMetricDatum`:
    `CurrentMetricDatum`, `MetricHeisenbergCurrent`, `splitEightCurrentMetricDatum`.
- BUCKET 2 (Deconfabulation):
  * All normal-ordered pair and Sugawara kernel evaluation theorems are proved
    via explicit unfolding.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `channelPairNO`, `channelSugawaraKernel`, `splitEightKernel`.
  * `channelPairNO_def`, `channelPairNO_of_le`, `channelPairNO_of_gt`,
    `channelSugawaraKernel_def`, `splitEightKernel_def`.
-/

namespace InfoGeometry.Canonical.MetricSugawaraBridge

open scoped BigOperators
open CurrentSugawaraMetricDatum
open CurrentMetricDatum

variable {𝕜 I V : Type*}
variable [Field 𝕜] [Fintype I] [DecidableEq I]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Channel-indexed normal-ordered pair of current operators `:J_{i,m} J_{j,n}:`. -/
noncomputable def channelPairNO
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (i j : I) (m n : ℤ) : V →ₗ[𝕜] V :=
  if n ≤ m then (H.J j n).comp (H.J i m) else (H.J i m).comp (H.J j n)

/-- Explicit definition of `channelPairNO H i j m n`. -/
@[simp] theorem channelPairNO_def
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (i j : I) (m n : ℤ) :
    channelPairNO H i j m n =
      (if n ≤ m then (H.J j n).comp (H.J i m) else (H.J i m).comp (H.J j n)) := by
  unfold channelPairNO
  exact Eq.refl _

/-- When `n ≤ m`, `channelPairNO H i j m n` places `H.J i m` on the right. -/
theorem channelPairNO_of_le
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (i j : I) {m n : ℤ} (hnm : n ≤ m) :
    channelPairNO H i j m n = (H.J j n).comp (H.J i m) := by
  unfold channelPairNO
  exact if_pos hnm

/-- When `m < n`, `channelPairNO H i j m n` places `H.J j n` on the right. -/
theorem channelPairNO_of_gt
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (i j : I) {m n : ℤ} (hmn : m < n) :
    channelPairNO H i j m n = (H.J i m).comp (H.J j n) := by
  unfold channelPairNO
  exact if_neg (not_le.mpr hmn)

/-- Explicit finite-channel Sugawara kernel
`L_n v = 2⁻¹ • ∑ᶠ k, ∑ i, ∑ j, κ^{ij} • :J_{i,n-k} J_{j,k}: v`. -/
noncomputable def channelSugawaraKernel
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (n : ℤ) : V → V :=
  fun v =>
    (2 : 𝕜)⁻¹ • ∑ᶠ k, ∑ i, ∑ j, H.metric.kappaInv i j •
      channelPairNO H i j (n - k) k v

/-- Pointwise evaluation of `channelSugawaraKernel H n v`. -/
@[simp] theorem channelSugawaraKernel_def
    (H : CurrentMetricDatum.MetricHeisenbergCurrent 𝕜 V I)
    (n : ℤ) (v : V) :
    channelSugawaraKernel H n v =
      (2 : 𝕜)⁻¹ • ∑ᶠ k, ∑ i, ∑ j, H.metric.kappaInv i j •
        channelPairNO H i j (n - k) k v := by
  unfold channelSugawaraKernel
  exact Eq.refl _

/-- The split 8-channel Sugawara kernel specialized to `Fin 8` over `ℝ`. -/
noncomputable def splitEightKernel
    (V : Type*) [AddCommGroup V] [Module ℝ V] :
    CurrentMetricDatum.MetricHeisenbergCurrent ℝ V (Fin 8) →
      ℤ → V → V :=
  channelSugawaraKernel

/-- Pointwise evaluation of `splitEightKernel H n v`. -/
@[simp] theorem splitEightKernel_def
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    (H : CurrentMetricDatum.MetricHeisenbergCurrent ℝ V (Fin 8))
    (n : ℤ) (v : V) :
    splitEightKernel (V := V) H n v =
      (2 : ℝ)⁻¹ • ∑ᶠ k, ∑ i : Fin 8, ∑ j : Fin 8, H.metric.kappaInv i j •
        channelPairNO H i j (n - k) k v := by
  unfold splitEightKernel channelSugawaraKernel
  exact Eq.refl _

end InfoGeometry.Canonical.MetricSugawaraBridge
