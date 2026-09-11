/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Gibbs temperature susceptibility

For a finite energy spectrum, inverse temperature is `β = 1 / ε`. The
temperature-response diagnostic is the Gibbs energy variance, equivalently the
Hessian of the finite log-partition potential. A large value indicates a sharp
finite crossover; zero variance is the exact finite degeneracy condition.
-/

namespace InfoGeometry.Inference.FiniteGibbs

open scoped BigOperators
open InfoGeometry.GrandCanonical

variable {Data : Type*} [Fintype Data] [Nonempty Data]

noncomputable def temperatureSusceptibility
    (E : Data → ℝ) (ε : ℝ) : ℝ :=
  InfoGeometry.GrandCanonical.variance { energy := E } ε⁻¹

theorem temperatureSusceptibility_eq_logPartition_hessian
    (E : Data → ℝ) (ε : ℝ) :
    temperatureSusceptibility E ε =
      InfoGeometry.GrandCanonical.hessian { energy := E } ε⁻¹ := by
  unfold temperatureSusceptibility
  rw [InfoGeometry.GrandCanonical.potential_second_derivative_eq_variance]

theorem temperatureSusceptibility_nonneg
    (E : Data → ℝ) (ε : ℝ) :
    0 ≤ temperatureSusceptibility E ε := by
  unfold temperatureSusceptibility
  exact InfoGeometry.GrandCanonical.variance_nonneg { energy := E } ε⁻¹

theorem temperatureSusceptibility_eq_zero_iff
    (E : Data → ℝ) (ε : ℝ) :
    temperatureSusceptibility E ε = 0 ↔
      ∀ i, E i = InfoGeometry.GrandCanonical.mean { energy := E } ε⁻¹ := by
  unfold temperatureSusceptibility
  exact InfoGeometry.GrandCanonical.variance_eq_zero_iff_energy_eq_mean
    { energy := E } ε⁻¹

end InfoGeometry.Inference.FiniteGibbs
