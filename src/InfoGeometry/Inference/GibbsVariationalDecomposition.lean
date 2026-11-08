/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteRelativeEntropy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Inference.GibbsVariational

/-!
# Gibbs variational decomposition

The entropy-regularized finite objective differs from its Gibbs value by a
nonnegative relative-entropy term. This is the finite primal-dual certificate
for the Gibbs optimizer.
-/

open scoped BigOperators

namespace InfoGeometry.Inference.FiniteGibbs

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

theorem entropyRegularizedObjective_eq_freeEnergy_add_relativeEntropy
    (M : Model (Data := Data) (Theta := Theta))
    (θ : Theta) {ε : ℝ} (hε : 0 < ε)
    (q : Data → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i : Data, q i = 1) :
    entropyRegularizedObjective M θ ε q =
      freeEnergy M θ ε +
        ε * InfoGeometry.Inference.finiteRelativeEntropy
          q (weight M θ ε) := by
  unfold entropyRegularizedObjective freeEnergy
  unfold InfoGeometry.Inference.finiteRelativeEntropy
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hq_nonzero : ∀ i, q i ≠ 0 := fun i => ne_of_gt (hq_pos i)
  have hw_nonzero : ∀ i, weight M θ ε i ≠ 0 :=
    fun i => (weight_pos M θ ε i).ne'
  have hlogratio : ∀ i,
      Real.log (q i / weight M θ ε i) =
        Real.log (q i) + M.energy i θ / ε +
          Real.log (partitionFunction M θ ε) := by
    intro i
    rw [Real.log_div (hq_nonzero i) (hw_nonzero i)]
    rw [log_weight M θ ε i]
    ring
  calc
    (∑ i : Data, q i * M.energy i θ) +
        ε * ∑ i : Data, q i * Real.log (q i)
        = -ε * Real.log (partitionFunction M θ ε) +
            ε * ∑ i : Data, q i *
              Real.log (q i / weight M θ ε i) := by
          simp_rw [hlogratio]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          rw [Finset.sum_add_distrib]
          rw [← Finset.sum_mul]
          rw [hq_sum]
          simp_rw [div_eq_mul_inv]
          rw [mul_add]
          rw [mul_add]
          have henergy :
              ε * (∑ x : Data, q x * (M.energy x θ * ε⁻¹)) =
                ∑ x : Data, q x * M.energy x θ := by
            calc
              ε * (∑ x : Data, q x * (M.energy x θ * ε⁻¹)) =
                  ε * (∑ x : Data, (q x * M.energy x θ) * ε⁻¹) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro x hx
                    ring
              _ = ε * (∑ x : Data, q x * M.energy x θ) * ε⁻¹ := by
                    rw [← Finset.sum_mul]
                    ring
              _ = ∑ x : Data, q x * M.energy x θ := by
                    field_simp [hεne]
          rw [henergy]
          ring
    _ = -ε * Real.log (partitionFunction M θ ε) +
          ε * InfoGeometry.Inference.finiteRelativeEntropy
            q (weight M θ ε) := by
          rfl

end InfoGeometry.Inference.FiniteGibbs
