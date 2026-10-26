/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.SolovievTransitionStrength
import InfoGeometry.Topology.KatzSarnakRandomMatrixBridge

/-!
# Real two-configuration transition inference

An operator model motivated by Zago et al., EPJ Web Conf. 378, 01050 (2026).
Mixing is within one fixed physical J/parity sector. A transition operator
may connect two different sectors, represented by separate coordinate copies.
Real amplitudes and a two-state truncation are explicit modelling restrictions.
No measured mixing fraction or shell-model interpretation is proved.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearConfigurationMixing

open Matrix
open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem
open InfoGeometry.Physics.SolovievTransitionStrength
open InfoGeometry.Topology.KatzSarnakRandomMatrixBridge

/-- A change of configuration basis applied to a diagonal spectral operator. -/
def spectralHamiltonian (e₁ e₂ c s : ℝ) : Hamiltonian :=
  rotationMatrix c s * diagonal ![e₁, e₂] * (rotationMatrix c s)ᵀ

theorem spectralHamiltonian_eq_block (e₁ e₂ c s : ℝ) :
    spectralHamiltonian e₁ e₂ c s =
      blockHamiltonian (c ^ 2 * e₁ + s ^ 2 * e₂)
        (s ^ 2 * e₁ + c ^ 2 * e₂) (c * s * (e₁ - e₂)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spectralHamiltonian, rotationMatrix, blockHamiltonian,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem spectralHamiltonian_first_eigenpair (e₁ e₂ c s : ℝ)
    (h : c ^ 2 + s ^ 2 = 1) :
    isEigenpair (spectralHamiltonian e₁ e₂ c s) ![c, s] e₁ := by
  rw [spectralHamiltonian_eq_block, block_eigenpair_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · linear_combination e₁ * c * h
  · linear_combination e₁ * s * h

theorem spectralHamiltonian_second_eigenpair (e₁ e₂ c s : ℝ)
    (h : c ^ 2 + s ^ 2 = 1) :
    isEigenpair (spectralHamiltonian e₁ e₂ c s) ![-s, c] e₂ := by
  rw [spectralHamiltonian_eq_block, block_eigenpair_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · linear_combination -(e₂ * s) * h
  · linear_combination e₂ * c * h

theorem mixed_vectors_orthonormal (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    dotProduct ![c, s] ![c, s] = 1 ∧
    dotProduct ![-s, c] ![-s, c] = 1 ∧
    dotProduct ![c, s] ![-s, c] = 0 := by
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem intruder_weight_bounds (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    0 ≤ s ^ 2 ∧ s ^ 2 ≤ 1 := by
  exact ⟨sq_nonneg s, by nlinarith [sq_nonneg c]⟩

theorem amplitude_mixed_final (O : Observable) (initial : Carrier) (c s : ℝ) :
    amplitude O initial ![c, s] =
      c * amplitude O initial ![1, 0] + s * amplitude O initial ![0, 1] := by
  simp only [amplitude_entries, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-- Coherent real amplitudes retain the interference term. -/
theorem strength_mixed_final (O : Observable) (initial : Carrier) (c s : ℝ) :
    strength O initial ![c, s] =
      c ^ 2 * strength O initial ![1, 0] + s ^ 2 * strength O initial ![0, 1] +
        2 * c * s * amplitude O initial ![1, 0] * amplitude O initial ![0, 1] := by
  unfold strength
  rw [amplitude_mixed_final O initial c s]
  ring

/-- The two final-state strengths sum to the unmixed strengths. This is not
a sum rule for raw photon rates at different energies. -/
theorem strength_sum (O : Observable) (initial : Carrier) (c s : ℝ)
    (h : c ^ 2 + s ^ 2 = 1) :
    strength O initial ![c, s] + strength O initial ![-s, c] =
      strength O initial ![1, 0] + strength O initial ![0, 1] := by
  unfold strength
  rw [amplitude_mixed_final O initial c s, amplitude_mixed_final O initial (-s) c]
  linear_combination
    (amplitude O initial ![1, 0] ^ 2 + amplitude O initial ![0, 1] ^ 2) * h

/-- The vanishing normal amplitude is a physical model input, not an E2
selection rule inferred from the observed gamma branch. -/
theorem intruder_weight_from_strengths (O : Observable) (initial : Carrier)
    (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1)
    (hN : amplitude O initial ![1, 0] = 0)
    (hI : amplitude O initial ![0, 1] ≠ 0) :
    strength O initial ![c, s] /
      (strength O initial ![c, s] + strength O initial ![-s, c]) = s ^ 2 := by
  rw [strength_sum O initial c s h]
  unfold strength
  rw [amplitude_mixed_final O initial c s, hN]
  simp only [mul_zero, zero_add, zero_pow (by decide : 2 ≠ 0)]
  field_simp [hI]

/-- For any normalized mixing coordinates an unknown operator can reproduce
the same pair of amplitudes. The operator is explicitly constructed. -/
theorem unknown_operator_same_amplitudes (c s m : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    amplitude (!![m * c, m * s; m * s, 0]) ![1, 0] ![c, s] = m ∧
    amplitude (!![m * c, m * s; m * s, 0]) ![1, 0] ![-s, c] = 0 := by
  simp [amplitude_entries]
  constructor
  · linear_combination m * h
  · ring

/-- Concrete non-identifiability: both measured strengths can agree while
the squared intruder coefficients differ, when the operator is unknown. -/
theorem strength_pair_does_not_identify_mixing :
    ∃ (O₁ O₂ : Observable) (c₁ s₁ c₂ s₂ : ℝ),
      c₁ ^ 2 + s₁ ^ 2 = 1 ∧ c₂ ^ 2 + s₂ ^ 2 = 1 ∧ s₁ ^ 2 ≠ s₂ ^ 2 ∧
      strength O₁ ![1, 0] ![c₁, s₁] = 1 ∧
      strength O₂ ![1, 0] ![c₂, s₂] = 1 ∧
      strength O₁ ![1, 0] ![-s₁, c₁] = 0 ∧
      strength O₂ ![1, 0] ![-s₂, c₂] = 0 := by
  refine ⟨!![3/5, 4/5; 4/5, 0], !![4/5, 3/5; 3/5, 0],
    3/5, 4/5, 4/5, 3/5, ?_⟩
  norm_num [strength, amplitude_entries]

/-- Reduced-strength normalization when `O` contains reduced matrix elements.
The interpretation of those entries is supplied by the physical model. -/
def reducedStrength (twoJInitial : ℕ) (O : Observable) (initial final : Carrier) : ℝ :=
  strength O initial final / ((twoJInitial : ℝ) + 1)

theorem reducedStrength_nonneg (twoJInitial : ℕ) (O : Observable)
    (initial final : Carrier) : 0 ≤ reducedStrength twoJInitial O initial final := by
  unfold reducedStrength
  exact div_nonneg (strength_nonneg O initial final) (by positivity)

theorem reducedStrength_sum (twoJInitial : ℕ) (O : Observable) (initial : Carrier)
    (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    reducedStrength twoJInitial O initial ![c, s] +
      reducedStrength twoJInitial O initial ![-s, c] =
    reducedStrength twoJInitial O initial ![1, 0] +
      reducedStrength twoJInitial O initial ![0, 1] := by
  simp only [reducedStrength, ← add_div, strength_sum O initial c s h]

end InfoGeometry.Physics.NuclearConfigurationMixing
