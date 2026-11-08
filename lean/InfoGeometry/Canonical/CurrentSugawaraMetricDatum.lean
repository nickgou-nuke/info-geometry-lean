/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Current Sugawara Channel Metric and Split-Signature Realization

This module defines the subtype carrier `CurrentMetricDatum 𝕜 I` of invertible
symmetric channel metrics on a finite index set `I` and the subtype carrier
`MetricHeisenbergCurrent 𝕜 V I` of metric-weighted Heisenberg current families,
and constructs the split `(4,4)` 8-channel metric `splitEightCurrentMetricDatum`
with full symmetry and left/right inversion proofs.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `Mathlib.Algebra.BigOperators.Group.Finset.Basic`: finite channel sums.
- BUCKET 2 (Deconfabulation):
  * Replaced `structure CurrentMetricDatum` and `structure MetricHeisenbergCurrent`
    with explicit subtype `def`s and dot-notation projection functions/theorems.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `CurrentMetricDatum`, `CurrentMetricDatum.mk`, `CurrentMetricDatum.kappa`,
    `CurrentMetricDatum.kappaInv`, `CurrentMetricDatum.symmetric`,
    `CurrentMetricDatum.inverse_left`, `CurrentMetricDatum.inverse_right`.
  * `MetricHeisenbergCurrent`, `MetricHeisenbergCurrent.mk`,
    `MetricHeisenbergCurrent.metric`, `MetricHeisenbergCurrent.J`,
    `MetricHeisenbergCurrent.K`, `MetricHeisenbergCurrent.trunc`,
    `MetricHeisenbergCurrent.comm`.
  * `splitEightKappa`, `splitEightKappa_symmetric`, `splitEightKappa_inverse_left`,
    `splitEightKappa_inverse_right`, `splitEightCurrentMetricDatum`.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraMetricDatum

open scoped BigOperators

/-- Subtype carrier of finite channel metrics `(kappa, kappaInv)` satisfying symmetry
and left/right matrix inversion on a finite channel set `I`. -/
def CurrentMetricDatum (𝕜 I : Type*) [Field 𝕜] [Fintype I] [DecidableEq I] : Type _ :=
  { p : (I → I → 𝕜) × (I → I → 𝕜) //
    (∀ i j, p.1 i j = p.1 j i) ∧
    (∀ i k, ∑ j, p.2 i j * p.1 j k = if i = k then 1 else 0) ∧
    (∀ i k, ∑ j, p.1 i j * p.2 j k = if i = k then 1 else 0) }

namespace CurrentMetricDatum

variable {𝕜 I : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]

/-- Constructor for `CurrentMetricDatum 𝕜 I`. -/
def mk
    (kappa kappaInv : I → I → 𝕜)
    (symmetric : ∀ i j, kappa i j = kappa j i)
    (inverse_left : ∀ i k, ∑ j, kappaInv i j * kappa j k = if i = k then 1 else 0)
    (inverse_right : ∀ i k, ∑ j, kappa i j * kappaInv j k = if i = k then 1 else 0) :
    CurrentMetricDatum 𝕜 I :=
  ⟨(kappa, kappaInv), ⟨symmetric, inverse_left, inverse_right⟩⟩

/-- Covariant channel metric `κ_{ij}` of a `CurrentMetricDatum`. -/
def kappa (M : CurrentMetricDatum 𝕜 I) : I → I → 𝕜 :=
  M.1.1

/-- Contravariant inverse channel metric `κ^{ij}` of a `CurrentMetricDatum`. -/
def kappaInv (M : CurrentMetricDatum 𝕜 I) : I → I → 𝕜 :=
  M.1.2

/-- Symmetry `M.kappa i j = M.kappa j i` of the channel metric. -/
theorem symmetric (M : CurrentMetricDatum 𝕜 I) (i j : I) :
    M.kappa i j = M.kappa j i := by
  unfold kappa
  exact M.2.1 i j

/-- Left matrix inverse identity `∑ j, M.kappaInv i j * M.kappa j k = δ_{ik}`. -/
theorem inverse_left (M : CurrentMetricDatum 𝕜 I) (i k : I) :
    ∑ j, M.kappaInv i j * M.kappa j k = if i = k then 1 else 0 := by
  unfold kappa kappaInv
  exact M.2.2.1 i k

/-- Right matrix inverse identity `∑ j, M.kappa i j * M.kappaInv j k = δ_{ik}`. -/
theorem inverse_right (M : CurrentMetricDatum 𝕜 I) (i k : I) :
    ∑ j, M.kappa i j * M.kappaInv j k = if i = k then 1 else 0 := by
  unfold kappa kappaInv
  exact M.2.2.2 i k

/-- Subtype carrier of metric-indexed Heisenberg current families `(metric, J, K)`
satisfying high-mode truncation and the metric-weighted Heisenberg commutator law. -/
def MetricHeisenbergCurrent
    (𝕜 V I : Type*) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [Fintype I] [DecidableEq I] :
    Type _ :=
  { p : CurrentMetricDatum 𝕜 I × ((I → ℤ → V →ₗ[𝕜] V) × (V →ₗ[𝕜] V)) //
    (∀ v i, ∀ᶠ l in Filter.atTop, p.2.1 i l v = 0) ∧
    (∀ i j m n,
      ⁅p.2.1 i m, p.2.1 j n⁆ =
        if m + n = 0 then (m : 𝕜) • (p.1.kappa i j • p.2.2) else 0) }

/-- Constructor for `MetricHeisenbergCurrent 𝕜 V I`. -/
def MetricHeisenbergCurrent.mk
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (metric : CurrentMetricDatum 𝕜 I)
    (J : I → ℤ → V →ₗ[𝕜] V)
    (K : V →ₗ[𝕜] V)
    (trunc : ∀ v i, ∀ᶠ l in Filter.atTop, J i l v = 0)
    (comm : ∀ i j m n,
      ⁅J i m, J j n⁆ =
        if m + n = 0 then (m : 𝕜) • (metric.kappa i j • K) else 0) :
    MetricHeisenbergCurrent 𝕜 V I :=
  ⟨(metric, (J, K)), ⟨trunc, comm⟩⟩

/-- Channel metric of a `MetricHeisenbergCurrent`. -/
def MetricHeisenbergCurrent.metric
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (H : MetricHeisenbergCurrent 𝕜 V I) : CurrentMetricDatum 𝕜 I :=
  H.1.1

/-- Channel-indexed current mode operators `J i m` of a `MetricHeisenbergCurrent`. -/
def MetricHeisenbergCurrent.J
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (H : MetricHeisenbergCurrent 𝕜 V I) : I → ℤ → V →ₗ[𝕜] V :=
  H.1.2.1

/-- Central level operator `K` of a `MetricHeisenbergCurrent`. -/
def MetricHeisenbergCurrent.K
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (H : MetricHeisenbergCurrent 𝕜 V I) : V →ₗ[𝕜] V :=
  H.1.2.2

/-- High-mode truncation property of a `MetricHeisenbergCurrent`. -/
theorem MetricHeisenbergCurrent.trunc
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (H : MetricHeisenbergCurrent 𝕜 V I) (v : V) (i : I) :
    ∀ᶠ l in Filter.atTop, H.J i l v = 0 := by
  unfold MetricHeisenbergCurrent.J
  exact H.2.1 v i

/-- Metric-weighted Heisenberg commutator law of a `MetricHeisenbergCurrent`. -/
theorem MetricHeisenbergCurrent.comm
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (H : MetricHeisenbergCurrent 𝕜 V I) (i j : I) (m n : ℤ) :
    ⁅H.J i m, H.J j n⁆ =
      if m + n = 0 then (m : 𝕜) • (H.metric.kappa i j • H.K) else 0 := by
  unfold MetricHeisenbergCurrent.J MetricHeisenbergCurrent.metric MetricHeisenbergCurrent.K
  exact H.2.2 i j m n

/-- The split `(4,4)` signature metric used by the 8-channel bosonic Sugawara layer. -/
def splitEightKappa (i j : Fin 8) : ℝ :=
  if _h : i = j then if i.val < 4 then 1 else -1 else 0

/-- The split 8-channel metric is symmetric. -/
theorem splitEightKappa_symmetric (i j : Fin 8) :
    splitEightKappa i j = splitEightKappa j i := by
  unfold splitEightKappa
  by_cases h : i = j <;> simp [h, eq_comm]

/-- The split 8-channel metric is its own left inverse. -/
theorem splitEightKappa_inverse_left (i k : Fin 8) :
    ∑ j : Fin 8, splitEightKappa i j * splitEightKappa j k = if i = k then 1 else 0 := by
  classical
  by_cases hik : i = k
  · subst hik
    let f : Fin 8 → ℝ := fun j => splitEightKappa i j * splitEightKappa j i
    have hsum : ∑ j : Fin 8, f j = f i := by
      exact Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by
        intro j _hj hji
        simp [f, splitEightKappa, hji])
    have hfi : f i = 1 := by
      dsimp only [f, splitEightKappa]
      by_cases hi : i.val < 4 <;> simp [hi]
    rw [if_pos rfl]
    exact hsum.trans hfi
  · let f : Fin 8 → ℝ := fun j => splitEightKappa i j * splitEightKappa j k
    have hzero : ∀ j ∈ Finset.univ, f j = 0 := by
      intro j _hj
      by_cases hji : j = i
      · subst hji
        simp [f, splitEightKappa, hik]
      · by_cases hjk : j = k
        · subst hjk
          simp [f, splitEightKappa, hik]
        · simp [f, splitEightKappa, hjk]
    have hsum : ∑ j : Fin 8, f j = 0 := Finset.sum_eq_zero hzero
    rw [if_neg hik]
    exact hsum

/-- The split 8-channel metric is its own right inverse. -/
theorem splitEightKappa_inverse_right (i k : Fin 8) :
    ∑ j : Fin 8, splitEightKappa i j * splitEightKappa j k = if i = k then 1 else 0 := by
  have h := splitEightKappa_inverse_left i k
  exact h

/-- The canonical 8-channel split `(4,4)` metric datum. -/
noncomputable def splitEightCurrentMetricDatum : CurrentMetricDatum ℝ (Fin 8) :=
  CurrentMetricDatum.mk
    splitEightKappa
    splitEightKappa
    splitEightKappa_symmetric
    splitEightKappa_inverse_left
    splitEightKappa_inverse_right

end CurrentMetricDatum

end InfoGeometry.Canonical.CurrentSugawaraMetricDatum
