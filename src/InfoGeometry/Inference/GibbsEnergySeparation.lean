/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsInference
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Gibbs energy separation

This module makes the isolation mechanism explicit: the ratio of two positive
Gibbs weights is exactly the exponential of the corresponding energy gap.
It is a finite identity, so it does not assert a thermodynamic limit.
-/

namespace InfoGeometry.Inference.FiniteGibbs

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

theorem weight_ratio_eq_exp_energy_gap
    (M : Model (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (i j : Data) :
    weight M θ ε i / weight M θ ε j =
      Real.exp (-(M.energy i θ - M.energy j θ) / ε) := by
  unfold weight
  have hZ : partitionFunction M θ ε ≠ 0 := partitionFunction_ne_zero M θ ε
  field_simp [hZ, Real.exp_ne_zero]
  rw [← Real.exp_add]
  congr 1
  ring_nf

theorem weight_ratio_le_exp_neg_gap
    (M : Model (Data := Data) (Theta := Theta))
    (θ : Theta) {ε δ : ℝ} (hε : 0 < ε) (i j : Data)
    (hgap : M.energy j θ + δ ≤ M.energy i θ) :
    weight M θ ε i / weight M θ ε j ≤ Real.exp (-δ / ε) := by
  rw [weight_ratio_eq_exp_energy_gap M θ ε i j]
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff_of_pos_right hε).2
  linarith

end InfoGeometry.Inference.FiniteGibbs
