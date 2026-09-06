/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Canonical.CausalVortexCooperPairing
import InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra

/-!
# Explicit finite Majorana witness

The abstract Cooper-pair theorem is non-vacuous already in dimension two.
This file instantiates its generators with the Pauli `σ1` and `σ3` matrices
owned by the finite Hestenes/Pauli module.
-/

noncomputable section

namespace CausalVortex

open Matrix
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Physics.HestenesCuntzSpacetimeAlgebra

def pauliMajoranaWitness : NullBoundaryMajoranas 2 :=
  { gamma_L := involutiveUnit σ1 pauli_sigma1_sq
    gamma_R := involutiveUnit σ3 pauli_sigma3_sq
    h_anticomm := by
      exact pauli_sigma1_anti_sigma3
    h_L_sq := by
      exact pauli_sigma1_sq
    h_R_sq := by
      exact pauli_sigma3_sq }

theorem pauliMajoranaWitness_exists :
    ∃ m : NullBoundaryMajoranas 2,
      gammaLVal m * gammaLVal m = 1 ∧
      gammaRVal m * gammaRVal m = 1 ∧
      gammaLVal m * gammaRVal m + gammaRVal m * gammaLVal m = 0 := by
  refine ⟨pauliMajoranaWitness, ?_⟩
  exact ⟨pauli_sigma1_sq, pauli_sigma3_sq, pauli_sigma1_anti_sigma3⟩

theorem pauliMajoranaWitness_selfAdjoint :
    (gammaLVal pauliMajoranaWitness)ᴴ = gammaLVal pauliMajoranaWitness ∧
      (gammaRVal pauliMajoranaWitness)ᴴ = gammaRVal pauliMajoranaWitness := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [pauliMajoranaWitness, gammaLVal, involutiveUnit, σ1,
      Matrix.conjTranspose]
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [pauliMajoranaWitness, gammaRVal, involutiveUnit, σ3,
      Matrix.conjTranspose]

theorem pauliMajoranaWitness_majoranasSelfAdjoint :
    MajoranasSelfAdjoint pauliMajoranaWitness := by
  exact pauliMajoranaWitness_selfAdjoint

theorem pauli_cooper_pair_conjugate_eq_conjTranspose :
    (cooperPairCondensate pauliMajoranaWitness)ᴴ =
      cooperPairConjugate pauliMajoranaWitness := by
  exact cooper_pair_conjugate_eq_conjTranspose pauliMajoranaWitness
    pauliMajoranaWitness_majoranasSelfAdjoint

theorem pauli_cooper_pair_is_nilpotent :
    cooperPairCondensate pauliMajoranaWitness *
        cooperPairCondensate pauliMajoranaWitness = 0 := by
  exact cooper_pair_is_nilpotent_cap pauliMajoranaWitness

theorem pauli_cooper_pair_car :
    cooperPairCondensate pauliMajoranaWitness *
          cooperPairConjugate pauliMajoranaWitness +
        cooperPairConjugate pauliMajoranaWitness *
          cooperPairCondensate pauliMajoranaWitness =
      (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  exact majorana_car pauliMajoranaWitness

noncomputable def pauliNumberOperator : M2C :=
  cooperPairConjugate pauliMajoranaWitness *
    cooperPairCondensate pauliMajoranaWitness

theorem pauli_number_operator_eq_one_add_sigma2 :
    pauliNumberOperator = (1 : M2C) + σ2 := by
  have hs : (↑(Real.sqrt 2) : ℂ) ^ 2 = 2 := by
    norm_num [pow_two, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold pauliNumberOperator cooperPairConjugate cooperPairCondensate
    pauliMajoranaWitness gammaLVal gammaRVal involutiveUnit
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ1, σ2, σ3, Matrix.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I] <;>
    field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)] <;>
      norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Complex.I_mul_I] <;>
      exact hs.symm

theorem pauli_sigma2_selfAdjoint :
    σ2ᴴ = σ2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ2, Matrix.conjTranspose]

theorem pauli_number_operator_selfAdjoint :
    pauliNumberOperatorᴴ = pauliNumberOperator := by
  rw [pauli_number_operator_eq_one_add_sigma2,
    Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    pauli_sigma2_selfAdjoint]

theorem pauli_number_operator_quadratic :
    pauliNumberOperator * pauliNumberOperator =
      (2 : ℂ) • pauliNumberOperator := by
  rw [pauli_number_operator_eq_one_add_sigma2]
  simp [add_mul, mul_add, pauli_sigma2_sq, smul_add, add_smul,
    two_smul, add_assoc, add_left_comm, add_comm]

end CausalVortex
