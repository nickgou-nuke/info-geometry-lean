/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.PoissonGibbsModel
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Regularized Poisson-deviance Gibbs factors

The Poisson deviance is twice the scalar Poisson Bregman energy. Using it as
the Gibbs energy produces the regularized factor `exp (-D / ε)` and its finite
partition normalization without any boundary clamp.
-/

namespace InfoGeometry.Inference

open FiniteGibbs
open scoped BigOperators

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

noncomputable def poissonDeviance (y lam : ℝ) : ℝ :=
  2 * poissonBregman y lam

theorem poissonDeviance_nonneg
    {y lam : ℝ} (hy : 0 ≤ y) (hlam : 0 < lam) :
    0 ≤ poissonDeviance y lam := by
  unfold poissonDeviance
  exact mul_nonneg (by norm_num) (poissonBregman_nonneg hy hlam)

noncomputable def PoissonModel.devianceEnergy
    (M : PoissonModel (Data := Data) (Theta := Theta)) :
    Data → Theta → ℝ :=
  fun i θ => poissonDeviance (M.observed i) (M.mean i θ)

noncomputable def PoissonModel.devianceGibbsModel
    (M : PoissonModel (Data := Data) (Theta := Theta)) :
    FiniteGibbs.Model (Data := Data) (Theta := Theta) :=
  ⟨M.devianceEnergy⟩

noncomputable def regularizedPoissonWeight
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (i : Data) : ℝ :=
  FiniteGibbs.weight M.devianceGibbsModel θ ε i

theorem regularizedPoissonWeight_eq_deviance_factor
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (i : Data) :
    regularizedPoissonWeight M θ ε i =
      Real.exp (-poissonDeviance (M.observed i) (M.mean i θ) / ε) /
        partitionFunction M.devianceGibbsModel θ ε := by
  rfl

theorem regularizedPoissonWeight_pos
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (i : Data) :
    0 < regularizedPoissonWeight M θ ε i := by
  exact FiniteGibbs.weight_pos M.devianceGibbsModel θ ε i

theorem regularizedPoissonWeights_sum_one
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) :
    ∑ i : Data, regularizedPoissonWeight M θ ε i = 1 := by
  exact FiniteGibbs.weights_sum_one M.devianceGibbsModel θ ε

theorem poissonDevianceEnergy_nonneg
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (i : Data) (θ : Theta) :
    0 ≤ M.devianceEnergy i θ := by
  exact poissonDeviance_nonneg (M.observed_nonneg i) (M.mean_pos i θ)

end InfoGeometry.Inference
