/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearConfigurationMixing

/-!
# Conditional identification from joint spectroscopic data

This extends the existing real two-configuration model, with a fixed basis and
ordered energy labels. An inclusive transfer response is diagonal when the
two configuration images under the transfer map are orthogonal; its calibration is an input, not a
reaction-theory result. A calibrated coherent electromagnetic channel supplies
the interference measurement. Unknown operators retain the existing ambiguity.

This identifies the calibrated finite Hamiltonian, not the full microscopic
Hamiltonian. Applying it after energy-dependent Feshbach elimination additionally
requires a common orthonormal real two-configuration realization and consistently
transformed/calibrated responses; this file does not assert such a realization.
This is exact identifiability, not statistical stability or a fit to sulfur-37.
-/

noncomputable section
namespace InfoGeometry.Physics.NuclearJointSpectroscopyInference
open Matrix
open InfoGeometry.Physics.NuclearConfigurationMixing
open InfoGeometry.Physics.SolovievTransitionStrength
open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

/-- Inclusive transfer strength is the expectation of the response TᵀT.
Orthogonality of the final basis alone does not diagonalize this response. -/
theorem inclusive_transfer_response (T : Observable) (x : Carrier) :
    strength T x ![1, 0] + strength T x ![0, 1] = amplitude (Tᵀ * T) x x := by
  simp [strength, amplitude_entries, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Orthogonal configuration images give a diagonal transfer response. -/
theorem orthogonal_transfer_images (T : Observable)
    (horth : T 0 0 * T 0 1 + T 1 0 * T 1 1 = 0) :
    Tᵀ * T = diagonal ![T 0 0 ^ 2 + T 1 0 ^ 2, T 0 1 ^ 2 + T 1 1 ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal] <;> nlinarith [horth]

/-- Native diagonal response readout; tN/tI are calibrated inclusive responses. -/
theorem transfer_response (tN tI c s : ℝ) :
    amplitude (diagonal ![tN, tI]) ![c, s] ![c, s] = tN * c ^ 2 + tI * s ^ 2 := by
  simp [amplitude_entries, diagonal]
  ring

theorem weight_from_calibrated_transfer (tN tI c s : ℝ)
    (h : c ^ 2 + s ^ 2 = 1) (hsep : tI ≠ tN) :
    (amplitude (diagonal ![tN, tI]) ![c, s] ![c, s] - tN) / (tI - tN) = s ^ 2 := by
  rw [transfer_response]
  apply (div_eq_iff (sub_ne_zero.mpr hsep)).mpr
  linear_combination tN * h

/-- Real interference calibration identifies cs once the two weights are known.
For complex amplitudes the denominator must instead use Re(conj(aN)*aI). -/
theorem coherence_from_calibrated_transition (O : Observable) (initial : Carrier)
    (c s : ℝ) (hN : amplitude O initial ![1, 0] ≠ 0)
    (hI : amplitude O initial ![0, 1] ≠ 0) :
    (strength O initial ![c, s] - c ^ 2 * strength O initial ![1, 0] -
      s ^ 2 * strength O initial ![0, 1]) /
      (2 * amplitude O initial ![1, 0] * amplitude O initial ![0, 1]) = c * s := by
  rw [strength_mixed_final]
  field_simp [hN, hI]
  ring

/-- Shared calibrated transfer and EM data identify the real configuration
density entries. Both calibration separation hypotheses are essential. -/
theorem joint_data_identifies_density
    (tN tI c s c' s' : ℝ) (O : Observable) (initial : Carrier)
    (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1)
    (hsep : tI ≠ tN)
    (hN : amplitude O initial ![1, 0] ≠ 0)
    (hI : amplitude O initial ![0, 1] ≠ 0)
    (htransfer : amplitude (diagonal ![tN, tI]) ![c, s] ![c, s] =
      amplitude (diagonal ![tN, tI]) ![c', s'] ![c', s'])
    (hem : strength O initial ![c, s] = strength O initial ![c', s']) :
    c ^ 2 = c' ^ 2 ∧ s ^ 2 = s' ^ 2 ∧ c * s = c' * s' := by
  have hs : s ^ 2 = s' ^ 2 := by
    rw [← weight_from_calibrated_transfer tN tI c s h hsep,
      ← weight_from_calibrated_transfer tN tI c' s' h' hsep, htransfer]
  have hc : c ^ 2 = c' ^ 2 := by linarith
  refine ⟨hc, hs, ?_⟩
  rw [← coherence_from_calibrated_transition O initial c s hN hI,
    ← coherence_from_calibrated_transition O initial c' s' hN hI, hc, hs, hem]

/-- With the same ordered eigenvalues, joint data determine all three entries
of the existing symmetric Hamiltonian, including the signed coupling in the fixed basis. -/
theorem joint_data_identifies_hamiltonian
    (e₁ e₂ tN tI c s c' s' : ℝ) (O : Observable) (initial : Carrier)
    (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1)
    (hsep : tI ≠ tN)
    (hN : amplitude O initial ![1, 0] ≠ 0)
    (hI : amplitude O initial ![0, 1] ≠ 0)
    (htransfer : amplitude (diagonal ![tN, tI]) ![c, s] ![c, s] =
      amplitude (diagonal ![tN, tI]) ![c', s'] ![c', s'])
    (hem : strength O initial ![c, s] = strength O initial ![c', s']) :
    spectralHamiltonian e₁ e₂ c s = spectralHamiltonian e₁ e₂ c' s' := by
  obtain ⟨hc, hs, hcs⟩ := joint_data_identifies_density tN tI c s c' s' O initial
    h h' hsep hN hI htransfer hem
  simp only [spectralHamiltonian_eq_block, hc, hs, hcs]

/-- Even without an interference channel, calibrated transfer and ordered energies
identify both diagonal entries and the squared coupling. Its sign remains free. -/
theorem transfer_energy_identifies_coupling_square
    (e₁ e₂ tN tI c s c' s' : ℝ)
    (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1) (hsep : tI ≠ tN)
    (htransfer : amplitude (diagonal ![tN, tI]) ![c, s] ![c, s] =
      amplitude (diagonal ![tN, tI]) ![c', s'] ![c', s']) :
    spectralHamiltonian e₁ e₂ c s 0 0 = spectralHamiltonian e₁ e₂ c' s' 0 0 ∧
    spectralHamiltonian e₁ e₂ c s 1 1 = spectralHamiltonian e₁ e₂ c' s' 1 1 ∧
    (spectralHamiltonian e₁ e₂ c s 0 1) ^ 2 =
      (spectralHamiltonian e₁ e₂ c' s' 0 1) ^ 2 := by
  have hs : s ^ 2 = s' ^ 2 := by
    rw [← weight_from_calibrated_transfer tN tI c s h hsep,
      ← weight_from_calibrated_transfer tN tI c' s' h' hsep, htransfer]
  have hc : c ^ 2 = c' ^ 2 := by linarith
  simp [spectralHamiltonian_eq_block, blockHamiltonian, mul_pow, hc, hs]

/-- Degenerate transfer calibration supplies no mixing information. -/
theorem equal_transfer_calibration (t c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    amplitude (diagonal ![t, t]) ![c, s] ![c, s] = t := by
  rw [transfer_response]
  linear_combination t * h

/-- A global sign of the real state remains a gauge freedom, even with calibrated O. -/
theorem global_sign_unobservable (O : Observable) (initial : Carrier) (c s : ℝ) :
    strength O initial ![-c, -s] = strength O initial ![c, s] := by
  unfold strength
  rw [amplitude_mixed_final O initial (-c) (-s), amplitude_mixed_final O initial c s]
  ring

/-- Nontrivial calibrated witness: transfer identifies 16/25 and the coherent
EM channel has strength 49/25. These are synthetic exact data, not measurements. -/
theorem calibrated_example :
    (3 / 5 : ℝ) ^ 2 + (4 / 5 : ℝ) ^ 2 = 1 ∧
    amplitude (diagonal ![0, 1]) ![3/5, 4/5] ![3/5, 4/5] = 16/25 ∧
    amplitude (!![1, 0; 1, 0]) ![1, 0] ![1, 0] = 1 ∧
    amplitude (!![1, 0; 1, 0]) ![1, 0] ![0, 1] = 1 ∧
    strength (!![1, 0; 1, 0]) ![1, 0] ![3/5, 4/5] = 49/25 := by
  norm_num [strength, amplitude_entries, diagonal]

end InfoGeometry.Physics.NuclearJointSpectroscopyInference
