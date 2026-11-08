import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Current Sugawara metric datum

This file isolates the channel metric required by the Sugawara bridge.
It keeps the indefinite signature data separate from the split/Krein carrier
used elsewhere in the repo.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraMetricDatum

open scoped BigOperators

/--
The finite channel metric and its inverse used by a Sugawara current family.

This is an algebraic signature datum: it packages the symmetric bilinear form
`κ` and its inverse `κ⁻¹` on a finite channel set.
-/
structure CurrentMetricDatum (𝕜 I : Type*) [Field 𝕜] [Fintype I] [DecidableEq I] where
  kappa : I → I → 𝕜
  kappaInv : I → I → 𝕜
  symmetric : ∀ i j, kappa i j = kappa j i
  inverse_left :
    ∀ i k, ∑ j, kappaInv i j * kappa j k = if i = k then 1 else 0
  inverse_right :
    ∀ i k, ∑ j, kappa i j * kappaInv j k = if i = k then 1 else 0

namespace CurrentMetricDatum

variable {𝕜 I : Type*} [Field 𝕜] [Fintype I]

/--
Metric-indexed Heisenberg currents.

The `trunc` field is kept at the level of the current modes, while the commutator
uses the finite channel metric `κ`.
-/
structure MetricHeisenbergCurrent
    (𝕜 V I : Type*) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] [Fintype I] [DecidableEq I] where
  metric : CurrentMetricDatum 𝕜 I
  J : I → ℤ → V →ₗ[𝕜] V
  K : V →ₗ[𝕜] V
  trunc : ∀ v i, ∀ᶠ l in Filter.atTop, J i l v = 0
  comm :
      ∀ i j m n,
      ⁅J i m, J j n⁆ =
        if m + n = 0 then (m : 𝕜) • (metric.kappa i j • K) else 0

/-- The split signature used by the 8-channel bosonic Sugawara layer. -/
def splitEightKappa (i j : Fin 8) : ℝ :=
  if h : i = j then if i.val < 4 then 1 else -1 else 0

/-- The split 8-channel metric is symmetric. -/
theorem splitEightKappa_symmetric (i j : Fin 8) :
    splitEightKappa i j = splitEightKappa j i := by
  unfold splitEightKappa
  by_cases h : i = j <;> simp [h, eq_comm]

/-- The split 8-channel metric is its own inverse. -/
theorem splitEightKappa_inverse_left (i k : Fin 8) :
    ∑ j : Fin 8, splitEightKappa i j * splitEightKappa j k = if i = k then 1 else 0 := by
  classical
  by_cases hik : i = k
  · subst hik
    let f : Fin 8 → ℝ := fun j => splitEightKappa i j * splitEightKappa j i
    have hsum : ∑ j : Fin 8, f j = f i := by
      exact Finset.sum_eq_single_of_mem i (by simp) (by
        intro j hj hji
        simp [f, splitEightKappa, hji])
    have hfi : f i = 1 := by
      simp [f, splitEightKappa]
      by_cases hi : i.val < 4 <;> simp [hi]
    simpa [f] using hsum.trans hfi
  · let f : Fin 8 → ℝ := fun j => splitEightKappa i j * splitEightKappa j k
    have hzero : ∀ j ∈ Finset.univ, f j = 0 := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        simp [f, splitEightKappa, hik]
      · by_cases hjk : j = k
        · subst hjk
          simp [f, splitEightKappa, hik, hji]
        · simp [f, splitEightKappa, hji, hjk]
    have hsum : ∑ j : Fin 8, f j = 0 := Finset.sum_eq_zero hzero
    simpa [f, hik] using hsum

/-- The split 8-channel metric is its own inverse on the right as well. -/
theorem splitEightKappa_inverse_right (i k : Fin 8) :
    ∑ j : Fin 8, splitEightKappa i j * splitEightKappa j k = if i = k then 1 else 0 := by
  classical
  by_cases hik : i = k
  · subst hik
    let f : Fin 8 → ℝ := fun j => splitEightKappa i j * splitEightKappa j i
    have hsum : ∑ j : Fin 8, f j = f i := by
      exact Finset.sum_eq_single_of_mem i (by simp) (by
        intro j hj hji
        simp [f, splitEightKappa, hji])
    have hfi : f i = 1 := by
      simp [f, splitEightKappa]
      by_cases hi : i.val < 4 <;> simp [hi]
    simpa [f] using hsum.trans hfi
  · let f : Fin 8 → ℝ := fun j => splitEightKappa i j * splitEightKappa j k
    have hzero : ∀ j ∈ Finset.univ, f j = 0 := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        simp [f, splitEightKappa, hik]
      · by_cases hjk : j = k
        · subst hjk
          simp [f, splitEightKappa, hik, hji]
        · simp [f, splitEightKappa, hji, hjk]
    have hsum : ∑ j : Fin 8, f j = 0 := Finset.sum_eq_zero hzero
    simpa [f, hik] using hsum

/-- The canonical 8-channel split metric datum. -/
noncomputable def splitEightCurrentMetricDatum : CurrentMetricDatum ℝ (Fin 8) where
  kappa := splitEightKappa
  kappaInv := splitEightKappa
  symmetric := splitEightKappa_symmetric
  inverse_left := splitEightKappa_inverse_left
  inverse_right := splitEightKappa_inverse_right

end CurrentMetricDatum

end InfoGeometry.Canonical.CurrentSugawaraMetricDatum
