/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearConfigurationMixing

/-!
# Joint identifiability in the calibrated two-configuration model

The transfer observation is assumed to measure the squared second coordinate.
The transition operator is fixed and calibrated, with both reference
amplitudes nonzero. Under these explicit conditions, a coherent transition
strength resolves the relative-sign ambiguity left by transfer weights.
Together with the energies it identifies the Hamiltonian in the chosen basis.
This does not infer experimental calibration or a sulfur-37 mixing fraction.
-/

namespace InfoGeometry.Physics.NuclearJointIdentifiability

open InfoGeometry.Physics.NuclearConfigurationMixing
open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
open InfoGeometry.Physics.SolovievTransitionStrength

/-- The interference weight is explicitly recoverable from a calibrated
coherent strength and the transfer weight `s²`. -/
theorem cross_weight_from_joint_readout (a b c s : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hunit : c ^ 2 + s ^ 2 = 1) :
    c * s = ((c * a + s * b) ^ 2 - (1 - s ^ 2) * a ^ 2 - s ^ 2 * b ^ 2) /
      (2 * a * b) := by
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb)).mpr
  linear_combination -(a ^ 2) * hunit

/-- Equal transfer weights and equal calibrated coherent strengths determine
the relative interference weight, without choosing a global vector sign. -/
theorem cross_weight_identified (a b c s d t : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ^ 2 + s ^ 2 = 1) (hd : d ^ 2 + t ^ 2 = 1)
    (htransfer : s ^ 2 = t ^ 2)
    (hstrength : (c * a + s * b) ^ 2 = (d * a + t * b) ^ 2) :
    c * s = d * t := by
  rw [cross_weight_from_joint_readout a b c s ha hb hc,
    cross_weight_from_joint_readout a b d t ha hb hd, htransfer, hstrength]

/-- Energies, calibrated transfer weights, and one coherent transition
strength identify the existing spectral Hamiltonian in its configuration basis. -/
theorem spectralHamiltonian_identified_by_joint_readout
    (e₁ e₂ c s d t : ℝ) (O : Observable) (initial : Carrier)
    (hc : c ^ 2 + s ^ 2 = 1) (hd : d ^ 2 + t ^ 2 = 1)
    (htransfer : s ^ 2 = t ^ 2)
    (hstrength : strength O initial ![c, s] = strength O initial ![d, t])
    (ha : amplitude O initial ![1, 0] ≠ 0)
    (hb : amplitude O initial ![0, 1] ≠ 0) :
    spectralHamiltonian e₁ e₂ c s = spectralHamiltonian e₁ e₂ d t := by
  have hcross : c * s = d * t := by
    apply cross_weight_identified
      (amplitude O initial ![1, 0]) (amplitude O initial ![0, 1])
      c s d t ha hb hc hd htransfer
    simpa only [strength, amplitude_mixed_final O initial c s,
      amplitude_mixed_final O initial d t] using hstrength
  have hfirst : c ^ 2 = d ^ 2 := by linarith
  simp only [spectralHamiltonian_eq_block, hfirst, htransfer, hcross]

/-- Even with both energies fixed, transfer weights alone leave an actual
off-diagonal ambiguity in the Hamiltonian. -/
theorem energy_and_transfer_do_not_identify_hamiltonian :
    ∃ c s d t : ℝ,
      c ^ 2 + s ^ 2 = 1 ∧ d ^ 2 + t ^ 2 = 1 ∧ s ^ 2 = t ^ 2 ∧
      spectralHamiltonian 0 1 c s ≠ spectralHamiltonian 0 1 d t := by
  refine ⟨3 / 5, 4 / 5, 3 / 5, -(4 / 5), ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · intro h
    have h01 := congrArg (fun H : Hamiltonian => H 0 1) h
    norm_num [spectralHamiltonian_eq_block, blockHamiltonian] at h01

/-- The unavoidable common sign acts trivially on the reconstructed matrix. -/
theorem spectralHamiltonian_global_sign (e₁ e₂ c s : ℝ) :
    spectralHamiltonian e₁ e₂ (-c) (-s) = spectralHamiltonian e₁ e₂ c s := by
  simp [spectralHamiltonian_eq_block]

end InfoGeometry.Physics.NuclearJointIdentifiability
