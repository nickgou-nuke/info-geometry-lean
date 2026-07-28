/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteRelativeEntropyEquality
import InfoGeometry.Inference.GibbsVariationalDecomposition

/-!
# Unique finite Gibbs minimizer
-/

namespace InfoGeometry.Inference.FiniteGibbs

open InfoGeometry.Inference
open scoped BigOperators

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

theorem entropyRegularizedObjective_ge_freeEnergy
    (M : Model (Data := Data) (Theta := Theta))
    (θ : Theta) {ε : ℝ} (hε : 0 < ε)
    (q : Data → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i : Data, q i = 1) :
    freeEnergy M θ ε ≤ entropyRegularizedObjective M θ ε q := by
  rw [entropyRegularizedObjective_eq_freeEnergy_add_relativeEntropy
    M θ hε q hq_pos hq_sum]
  have hkl := finiteRelativeEntropy_nonneg q (weight M θ ε)
    hq_pos (fun i => weight_pos M θ ε i) hq_sum (weights_sum_one M θ ε)
  nlinarith [mul_nonneg hε.le hkl]

theorem entropyRegularizedObjective_eq_freeEnergy_iff
    (M : Model (Data := Data) (Theta := Theta))
    (θ : Theta) {ε : ℝ} (hε : 0 < ε)
    (q : Data → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i : Data, q i = 1) :
    entropyRegularizedObjective M θ ε q = freeEnergy M θ ε ↔
      q = weight M θ ε := by
  rw [entropyRegularizedObjective_eq_freeEnergy_add_relativeEntropy
    M θ hε q hq_pos hq_sum]
  constructor
  · intro h
    have hkl : InfoGeometry.Inference.finiteRelativeEntropy
        q (weight M θ ε) = 0 := by
      nlinarith [hε.ne']
    exact (finiteRelativeEntropy_eq_zero_iff q (weight M θ ε)
      hq_pos (fun i => weight_pos M θ ε i)
      hq_sum (weights_sum_one M θ ε)).mp hkl
  · intro hq
    rw [hq]
    have hkl : InfoGeometry.Inference.finiteRelativeEntropy
        (weight M θ ε) (weight M θ ε) = 0 := by
      unfold InfoGeometry.Inference.finiteRelativeEntropy
      apply Finset.sum_eq_zero
      intro i hi
      rw [div_self (weight_pos M θ ε i).ne']
      simp
    rw [hkl]
    ring

end InfoGeometry.Inference.FiniteGibbs
