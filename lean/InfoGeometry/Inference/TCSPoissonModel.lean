/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.PoissonGibbsModel
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# TCS Poisson application model

This is the first application-specific layer of the formal core. It keeps the
raw-count mean explicit as `T * (C * X - K * X^2)` and carries positivity of
that mean as an admissibility field instead of introducing a numerical clamp.
-/

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data] [Nonempty Data]

/-- Physical TCS parameters admissible on a finite experimental design. -/
structure TCSParameter (x liveTime : Data → ℝ) where
  C : ℝ
  K : ℝ
  mean_pos : ∀ i, 0 < liveTime i * (C * x i - K * x i ^ 2)

/-- The raw-count mean of an admissible TCS parameter at one observation. -/
def tcsMean
    {x liveTime : Data → ℝ}
    (p : TCSParameter x liveTime) (i : Data) : ℝ :=
  liveTime i * (p.C * x i - p.K * x i ^ 2)

/-- Construct the Poisson model for a finite TCS experiment. -/
noncomputable def tcsPoissonModel
    (observed x liveTime : Data → ℝ)
    (hobs : ∀ i, 0 ≤ observed i) :
    PoissonModel (Data := Data) (Theta := TCSParameter x liveTime) where
  observed := observed
  mean := fun i p => tcsMean p i
  observed_nonneg := hobs
  mean_pos := fun i p => p.mean_pos i

theorem tcsMean_pos
    {x liveTime : Data → ℝ}
    (p : TCSParameter x liveTime) (i : Data) :
    0 < tcsMean p i := by
  exact p.mean_pos i

theorem tcsEnergy_nonneg
    (observed x liveTime : Data → ℝ)
    (hobs : ∀ i, 0 ≤ observed i)
    (p : TCSParameter x liveTime) (i : Data) :
    0 ≤ (tcsPoissonModel observed x liveTime hobs).energy i p := by
  exact PoissonModel.energy_nonneg
    (tcsPoissonModel observed x liveTime hobs) i p

theorem tcsGibbsWeights_sum_one
    (observed x liveTime : Data → ℝ)
    (hobs : ∀ i, 0 ≤ observed i)
    (p : TCSParameter x liveTime) (ε : ℝ) :
    ∑ i : Data,
      poissonWeight (tcsPoissonModel observed x liveTime hobs) p ε i = 1 := by
  exact poissonWeights_sum_one
    (tcsPoissonModel observed x liveTime hobs) p ε

end InfoGeometry.Inference
