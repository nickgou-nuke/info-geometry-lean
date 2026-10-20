/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Thermodynamics.FiniteGibbsGaugeClosure

noncomputable section

namespace InfoGeometry.Algebraic.CartanExponentialFamily

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

section NormalizedGauge

/-- A uniform shift of all Cartan coordinates leaves the pointwise log-density
invariant after the partition function is renormalized. -/
theorem logDensity_add_constant (θ : ι → ℝ) (c : ℝ) (i : ι) :
    logDensity (fun j => θ j + c) i = logDensity θ i := by
  unfold logDensity
  rw [Phi_add_constant]
  ring

/-- The normalized Cartan surprisal is invariant under the additive gauge
shift of the natural parameter. -/
theorem surprisal_add_constant (θ : ι → ℝ) (c : ℝ) (i : ι) :
    surprisal (fun j => θ j + c) i = surprisal θ i := by
  unfold surprisal
  rw [Phi_add_constant]
  ring

end NormalizedGauge

/-- The relative entropy of two Cartan states is invariant when both natural
parameters receive the same additive gauge shift. -/
theorem kl_add_constant (θ η : ι → ℝ) (c : ℝ) :
    kl (fun j => θ j + c) (fun j => η j + c) = kl θ η := by
  unfold kl expect
  apply Finset.sum_congr rfl
  intro i hi
  rw [prob_add_constant]
  change prob θ i *
      (logDensity (fun j => θ j + c) i - logDensity (fun j => η j + c) i) =
    prob θ i * (logDensity θ i - logDensity η i)
  rw [logDensity_add_constant, logDensity_add_constant]

/-- Boltzmann entropy is a gauge invariant of the normalized Cartan family. -/
theorem boltzmannEntropy_add_constant (θ : ι → ℝ) (c : ℝ) :
    boltzmannEntropy (fun j => θ j + c) = boltzmannEntropy θ := by
  unfold boltzmannEntropy expect
  apply Finset.sum_congr rfl
  intro i hi
  rw [prob_add_constant, surprisal_add_constant]


end InfoGeometry.Algebraic.CartanExponentialFamily
