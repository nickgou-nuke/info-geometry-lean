/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.FiniteMarkovReversibilization
import InfoGeometry.Probability.FiniteResamplingGap

/-!
# Reversible averaging preserves symmetric edge observables

The kernel is changed on the original finite state space, but every symmetric
edge readout of its weighted flux is preserved. In particular this preserves
the native Dirichlet energy for every observable. No stationarity or row-sum
assumption is needed for the identity, only nonzero reference weights.
-/

namespace InfoGeometry.Physics

variable {n : Type*} [Fintype n]

/-- Symmetric edge observables cannot detect the antisymmetric flux part. -/
theorem weightedSelfPart_symmetric_readout (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, π i ≠ 0) (g : n → n → ℝ) (hg : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, π i * weightedSelfPart π P i j * g i j) =
      ∑ i, ∑ j, π i * P i j * g i j := by
  have hswap : (∑ i, ∑ j, π j * P j i * g i j) =
      ∑ i, ∑ j, π i * P i j * g i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hg j i]
  calc
    _ = ((∑ i, ∑ j, π i * P i j * g i j) +
        (∑ i, ∑ j, π j * P j i * g i j)) / 2 := by
      simp_rw [weightedSelfPart_flux π P hπ]
      simp only [div_mul_eq_mul_div, add_mul, ← Finset.sum_div,
        Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

/-- Reversibilization preserves quadratic dissipation for every observable. -/
theorem weightedSelfPart_dirichletEnergy (π : n → ℝ) (P : Matrix n n ℝ)
    (hπ : ∀ i, π i ≠ 0) (f : n → ℝ) :
    Probability.FiniteResamplingGap.dirichletEnergy π (weightedSelfPart π P) f =
      Probability.FiniteResamplingGap.dirichletEnergy π P f := by
  unfold Probability.FiniteResamplingGap.dirichletEnergy
  rw [weightedSelfPart_symmetric_readout π P hπ
    (fun i j => (f i - f j) ^ 2) (fun i j => sub_sq_comm (f i) (f j))]

end InfoGeometry.Physics
