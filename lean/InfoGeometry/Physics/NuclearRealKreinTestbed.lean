/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfigurationWitness
import InfoGeometry.Physics.NuclearThreeConfigurationDoubledTransition
import InfoGeometry.Physics.NuclearRealKreinComplementaryResolvent
import InfoGeometry.Physics.NuclearThreeConfigurationDoubledAnalytic
import InfoGeometry.Physics.NuclearThreeConfigurationAnalytic

/-!
# Real dual Krein testbed: normalized endpoints and joint inference

This entrypoint exposes the observation theorem on the actual native doubled
carrier. Its energy hypotheses refer to the paired Hamiltonian and reconstructed
states; its strength hypothesis refers to the two real clock quadratures.
The normalization is the positive pairing induced by the fundamental symmetry.
Physical spin/parity assignments and a multipole calibration remain model inputs.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearRealKreinTestbed

open InfoGeometry.Krein
open NuclearThreeConfiguration NuclearThreeConfigurationDual
open NuclearThreeConfigurationTransition NuclearThreeConfigurationInference
open NuclearDoubledConfiguration NuclearThreeConfigurationKreinReduction
open NuclearThreeConfigurationDoubledTransition NuclearEffectiveObservables

theorem darkDoubled_ne_zero : darkDoubled ≠ 0 := by
  intro h
  apply darkModel_ne_zero
  simpa [darkDoubled] using congrArg WithLp.fst h

theorem brightDoubled_ne_zero : brightDoubled ≠ 0 := by
  intro h
  apply brightModel_ne_zero
  simpa [brightDoubled] using congrArg WithLp.fst h

/-- The initial reconstructed state has unit positive physical norm. -/
theorem normalized_dark_norm (a c g : ℝ) :
    ‖normalizedState (doubledGraphMap c g a) darkDoubled‖ = 1 :=
  norm_normalizedState _ (doubledGraphMap_injective c g a) darkDoubled_ne_zero

/-- The final reconstructed state uses its own energy and induced metric. -/
theorem normalized_bright_norm (c g E : ℝ) :
    ‖normalizedState (doubledGraphMap c g E) brightDoubled‖ = 1 :=
  norm_normalizedState _ (doubledGraphMap_injective c g E) brightDoubled_ne_zero

theorem configuration_eigen_equation_of_doubled (a c g E : ℝ)
    (h : doubledHamiltonian a c g (doubledGraphMap c g E brightDoubled) =
      E • doubledGraphMap c g E brightDoubled) :
    hamiltonian a c g (graphMap c g E brightModel) =
      E • graphMap c g E brightModel := by
  have hx := congrArg WithLp.fst h
  simpa only [doubledHamiltonian, doubledGraphMap, brightDoubled,
    pairedLift_to_doubled, map_zero, WithLp.smul_fst, fst_to_doubled] using hx

/-- Joint identifiability stated directly for actual doubled eigenstates
and the normalized real two-quadrature observation. -/
theorem doubled_joint_identifiability (a E κ c₁ c₂ g₁ g₂ : ℝ)
    (ha₁ : a < c₁) (ha₂ : a < c₂) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hκ : κ ≠ 0) (hw₁ : E < (a + c₁) / 2) (hw₂ : E < (a + c₂) / 2)
    (he₁ : doubledHamiltonian a c₁ g₁ (doubledGraphMap c₁ g₁ E brightDoubled) =
      E • doubledGraphMap c₁ g₁ E brightDoubled)
    (he₂ : doubledHamiltonian a c₂ g₂ (doubledGraphMap c₂ g₂ E brightDoubled) =
      E • doubledGraphMap c₂ g₂ E brightDoubled)
    (hB : clockMeasuredStrength a c₁ g₁ E κ = clockMeasuredStrength a c₂ g₂ E κ) :
    c₁ = c₂ ∧ (g₁ = g₂ ∨ g₁ = -g₂) := by
  rw [clockMeasuredStrength_eq, clockMeasuredStrength_eq] at hB
  exact joint_identifiability a E κ c₁ c₂ g₁ g₂ ha₁ ha₂ hg₁ hg₂ hκ hw₁ hw₂
    (configuration_eigen_equation_of_doubled a c₁ g₁ E he₁)
    (configuration_eigen_equation_of_doubled a c₂ g₂ E he₂) hB

theorem doubled_recover_parameters (a c g E κ : ℝ)
    (hac : a < c) (hg : g ≠ 0) (hκ : κ ≠ 0) (hw : E < (a + c) / 2)
    (he : doubledHamiltonian a c g (doubledGraphMap c g E brightDoubled) =
      E • doubledGraphMap c g E brightDoubled) :
    c = E + (a - E) * clockMeasuredStrength a c g E κ /
        (κ ^ 2 - clockMeasuredStrength a c g E κ) ∧
    g ^ 2 = (a - E) ^ 2 * clockMeasuredStrength a c g E κ /
        (2 * (κ ^ 2 - clockMeasuredStrength a c g E κ)) := by
  simp only [clockMeasuredStrength_eq]
  exact recover_parameters a c g E κ hac hg hκ hw
    (configuration_eigen_equation_of_doubled a c g E he)

theorem doubled_example_strength : clockMeasuredStrength 2 3 1 1 1 = (2 : ℝ) / 3 := by
  rw [clockMeasuredStrength_eq]
  exact NuclearThreeConfigurationWitness.example_strength

end InfoGeometry.Physics.NuclearRealKreinTestbed
