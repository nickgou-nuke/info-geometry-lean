/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsInference
import InfoGeometry.Inference.PoissonBregman

/-!
# Poisson Gibbs inference model

This module instantiates the finite Gibbs kernel with the Poisson Bregman
energy. It formalizes the statistical weighting layer only; interpretation as
an outlier assignment remains an application-level model choice.
-/

namespace InfoGeometry.Inference

open FiniteGibbs

variable {Data Theta : Type*} [Fintype Data] [Nonempty Data]

/-- A finite Poisson observation/model pair. -/
structure PoissonModel where
  observed : Data → ℝ
  mean : Data → Theta → ℝ
  observed_nonneg : ∀ i, 0 ≤ observed i
  mean_pos : ∀ i θ, 0 < mean i θ

/-- The Poisson Bregman energy attached to a Poisson observation model. -/
noncomputable def PoissonModel.energy
    (M : PoissonModel (Data := Data) (Theta := Theta)) :
    Data → Theta → ℝ :=
  fun i θ => poissonBregman (M.observed i) (M.mean i θ)

/-- The corresponding finite Gibbs model. -/
noncomputable def PoissonModel.gibbsModel
    (M : PoissonModel (Data := Data) (Theta := Theta)) :
    FiniteGibbs.Model (Data := Data) (Theta := Theta) :=
  M.energy

theorem PoissonModel.energy_nonneg
    (M : PoissonModel (Data := Data) (Theta := Theta)) (i : Data) (θ : Theta) :
    0 ≤ M.energy i θ := by
  exact poissonBregman_nonneg (M.observed_nonneg i) (M.mean_pos i θ)

noncomputable def poissonWeight
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (i : Data) : ℝ :=
  FiniteGibbs.weight M.gibbsModel θ ε i

theorem poissonWeight_pos
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (i : Data) :
    0 < poissonWeight M θ ε i := by
  exact FiniteGibbs.weight_pos M.gibbsModel θ ε i

theorem poissonWeights_sum_one
    (M : PoissonModel (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) :
    ∑ i : Data, poissonWeight M θ ε i = 1 := by
  exact FiniteGibbs.weights_sum_one M.gibbsModel θ ε

end InfoGeometry.Inference
