/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Thermodynamics.SoftmaxGibbsVariationalPrinciple

noncomputable section

open Finset
open scoped BigOperators

namespace InfoGeometry.Thermodynamics.SoftmaxGibbsVariational

variable {I : Type*} [Fintype I] [Nonempty I]

/-- Equality in the finite softmax Gibbs variational bound characterizes the
Gibbs state among strictly positive normalized vectors. -/
theorem freeEnergy_eq_equilibrium_iff
    (T : InverseTemperature) (H : I → ℝ) (p : I → ℝ)
    (hp_sum : ∑ i : I, p i = 1)
    (hp_pos : ∀ i : I, 0 < p i) :
    freeEnergy T H p = freeEnergy T H (gibbsState T H) ↔
      p = gibbsState T H := by
  have hkl_eq :
      klDivergence p (gibbsState T H) =
        FiniteKLNonnegativity.finiteKL p (gibbsState T H) := rfl
  have hkl_zero_iff :
      klDivergence p (gibbsState T H) = 0 ↔
        p = gibbsState T H := by
    rw [hkl_eq]
    constructor
    · intro hzero
      have hterm : ∀ i : I,
          0 ≤ InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence
            (p i) (gibbsState T H i) := by
        intro i
        exact InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence_nonneg
          (p i) (gibbsState T H i) (hp_pos i) (gibbsState_pos T H i)
      have hsum : ∑ i : I,
          InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence
            (p i) (gibbsState T H i) = 0 := by
        calc
          ∑ i : I,
              InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence
                (p i) (gibbsState T H i) =
              FiniteKLNonnegativity.finiteKL p (gibbsState T H) := by
            unfold InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence
              FiniteKLNonnegativity.finiteKL
            simp_rw [sub_eq_add_neg]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_neg_distrib, hp_sum, gibbsState_sum_one]
            ring
          _ = 0 := hzero
      have hterms : ∀ i : I,
          InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence
            (p i) (gibbsState T H i) = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)).mp hsum i
          (Finset.mem_univ i)
      funext i
      by_contra hne
      have hpos := FiniteKLNonnegativity.scalarKLDivergence_pos_of_ne
        (hp_pos i) (gibbsState_pos T H i) hne
      linarith [hterms i]
    · intro h
      rw [h]
      exact FiniteKLNonnegativity.finiteKL_self_zero
        (gibbsState T H) (gibbsState_pos T H)
  constructor
  · intro hfe
    have hdiff := freeEnergy_sub_equilibrium_eq_kl T H p hp_sum hp_pos
    have hscaled : (1 / T.beta) * klDivergence p (gibbsState T H) = 0 := by
      calc
        (1 / T.beta) * klDivergence p (gibbsState T H) =
            freeEnergy T H p - (-(1 / T.beta) * Real.log (partitionSum T H)) :=
          hdiff.symm
        _ = freeEnergy T H p - freeEnergy T H (gibbsState T H) := by
          rw [freeEnergy_gibbsState T H]
        _ = 0 := by rw [hfe]; ring
    have hbeta : (1 / T.beta) ≠ 0 := one_div_ne_zero T.beta_ne_zero
    exact hkl_zero_iff.mp ((mul_eq_zero.mp hscaled).resolve_left hbeta)
  · intro hp_eq
    rw [hp_eq]

end InfoGeometry.Thermodynamics.SoftmaxGibbsVariational
