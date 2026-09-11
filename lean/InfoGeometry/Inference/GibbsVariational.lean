/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsInference
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Gibbs variational objective

This module identifies the finite Gibbs state with the entropy-regularized
primal objective at its exact free-energy value. Minimality is intentionally
left to a separate finite relative-entropy inequality.
-/

open scoped BigOperators

namespace InfoGeometry.Inference.FiniteGibbs

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

noncomputable def entropyRegularizedObjective
    (M : Model (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (q : Data → ℝ) : ℝ :=
  ∑ i : Data, q i * M.energy i θ +
    ε * ∑ i : Data, q i * Real.log (q i)

theorem log_weight
    (M : Model (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (i : Data) :
    Real.log (weight M θ ε i) =
      -M.energy i θ / ε - Real.log (partitionFunction M θ ε) := by
  unfold weight
  rw [Real.log_div (Real.exp_ne_zero _) (partitionFunction_ne_zero M θ ε)]
  rw [Real.log_exp]

theorem entropyRegularizedObjective_at_weight
    (M : Model (Data := Data) (Theta := Theta))
    (θ : Theta) {ε : ℝ} (hε : 0 < ε) :
    entropyRegularizedObjective M θ ε (weight M θ ε) =
      freeEnergy M θ ε := by
  unfold entropyRegularizedObjective freeEnergy
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hsum : ∑ i : Data, weight M θ ε i = 1 := weights_sum_one M θ ε
  calc
    (∑ i : Data, weight M θ ε i * M.energy i θ) +
        ε * ∑ i : Data, weight M θ ε i * Real.log (weight M θ ε i)
        = (∑ i : Data, weight M θ ε i * M.energy i θ) +
            ε * ∑ i : Data,
              weight M θ ε i *
                (-M.energy i θ / ε - Real.log (partitionFunction M θ ε)) := by
          congr 1
          apply congrArg (fun z : ℝ => ε * z)
          apply Finset.sum_congr rfl
          intro i hi
          rw [log_weight M θ ε i]
    _ = -ε * Real.log (partitionFunction M θ ε) := by
          have hcancel :
              (∑ i : Data, weight M θ ε i * M.energy i θ) +
                ε * ∑ i : Data, weight M θ ε i *
                  (-M.energy i θ / ε) = 0 := by
            calc
              (∑ i : Data, weight M θ ε i * M.energy i θ) +
                  ε * ∑ i : Data, weight M θ ε i *
                    (-M.energy i θ / ε)
                  = (∑ i : Data, weight M θ ε i * M.energy i θ) +
                      ∑ i : Data, ε * (weight M θ ε i *
                        (-M.energy i θ / ε)) := by
                        rw [Finset.mul_sum]
              _ = (∑ i : Data, weight M θ ε i * M.energy i θ) +
                    ∑ i : Data, -(weight M θ ε i * M.energy i θ) := by
                        congr 1
                        apply Finset.sum_congr rfl
                        intro i hi
                        field_simp [hεne]
              _ = 0 := by
                        rw [Finset.sum_neg_distrib]
                        ring
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          rw [← Finset.sum_mul]
          rw [hsum]
          simp only [one_mul]
          calc
            (∑ i : Data, weight M θ ε i * M.energy i θ) +
                ε * (∑ i : Data, weight M θ ε i *
                  (-M.energy i θ / ε) -
                  Real.log (partitionFunction M θ ε)) =
                ((∑ i : Data, weight M θ ε i * M.energy i θ) +
                  ε * ∑ i : Data, weight M θ ε i *
                    (-M.energy i θ / ε)) -
                  ε * Real.log (partitionFunction M θ ε) := by ring
            _ = -ε * Real.log (partitionFunction M θ ε) := by
                  rw [hcancel]
                  ring

end InfoGeometry.Inference.FiniteGibbs
