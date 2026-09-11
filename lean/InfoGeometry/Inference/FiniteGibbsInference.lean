/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Gibbs inference core

This file is the detector-independent mathematical kernel for the finite Gibbs
inference framework. It deliberately makes no claim about a thermodynamic
limit, numerical optimization, or the interpretation of a weight as an
outlier probability. Those are application-layer obligations.
-/

open scoped BigOperators

namespace InfoGeometry.Inference.FiniteGibbs

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

/-- A finite parameterized energy model. -/
structure Model where
  energy : Data → Theta → ℝ

/-- The finite partition function at parameter `θ` and temperature `ε`. -/
noncomputable def partitionFunction
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) : ℝ :=
  ∑ i : Data, Real.exp (-M.energy i θ / ε)

/-- The canonical Gibbs weight of one observation. -/
noncomputable def weight
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) (i : Data) : ℝ :=
  Real.exp (-M.energy i θ / ε) / partitionFunction M θ ε

/-- The finite free-energy potential. -/
noncomputable def freeEnergy
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) : ℝ :=
  -ε * Real.log (partitionFunction M θ ε)

theorem partitionFunction_pos
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    0 < partitionFunction M θ ε := by
  classical
  unfold partitionFunction
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Data))
      (f := fun i => Real.exp (-M.energy i θ / ε))
      (by
        intro i hi
        exact Real.exp_pos _)
      Finset.univ_nonempty)

theorem partitionFunction_ne_zero
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    partitionFunction M θ ε ≠ 0 :=
  (partitionFunction_pos M θ ε).ne'

theorem weight_pos
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) (i : Data) :
    0 < weight M θ ε i := by
  unfold weight
  exact div_pos (Real.exp_pos _) (partitionFunction_pos M θ ε)

theorem weight_nonneg
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) (i : Data) :
    0 ≤ weight M θ ε i :=
  (weight_pos M θ ε i).le

/-- The Gibbs weights form a normalized finite probability vector. -/
theorem weights_sum_one
    (M : Model (Data := Data) (Theta := Theta)) (θ : Theta) (ε : ℝ) :
    ∑ i : Data, weight M θ ε i = 1 := by
  classical
  unfold weight
  have hZne : partitionFunction M θ ε ≠ 0 := partitionFunction_ne_zero M θ ε
  calc
    ∑ i : Data, Real.exp (-M.energy i θ / ε) / partitionFunction M θ ε
        = (∑ i : Data, Real.exp (-M.energy i θ / ε)) /
            partitionFunction M θ ε := by
            simp_rw [div_eq_mul_inv]
            rw [Finset.sum_mul]
    _ = partitionFunction M θ ε / partitionFunction M θ ε := by
          rfl
    _ = 1 := div_self hZne

end InfoGeometry.Inference.FiniteGibbs
