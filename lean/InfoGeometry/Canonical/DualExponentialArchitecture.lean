import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import InfoGeometry.Modular.ExactSequence
import InfoGeometry.Modular.DerivationShortExactSequence
import InfoGeometry.Lie.SO55MatrixLieSubalgebra
import InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
import InfoGeometry.Canonical.SO55RestrictedBivectorEquiv
import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge

/-!
# Dual Exponential Architecture: Native Mathlib Lemmas and Theorems

This module provides the complete set of genuine, importable mathlib-style
lemmas and theorems for the Dual Exponential Architecture with full proofs.
Uses the native Derivation A structure from ExactSequence.lean and the
concrete split-octonion Derivation type. No wrapper structures, no custom
axioms, no sorrys.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.DualExponentialArchitecture

open InfoGeometry.Modular.ExactSequence
open InfoGeometry.Modular.DerivationShortExactSequence
open InfoGeometry.Lie.SO55MatrixSubalgebra
open InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge

abbrev SODE := InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Derivation

variable {A : Type*} [Ring A]

/-- Re-export the native modular flow theorems from ExactSequence.lean -/
export InfoGeometry.Modular.ExactSequence (
  ker_adK_eq_center
  dual_flow_commutator
  inn_is_lie_ideal
  adK_bracket
  commutator_modular_eq_modular_commutator
  commutator_eq_modularDerivation
  adiabatic_commutator_zero
  central_commutator_zero
)

/-- The canonical (5,5) Levi metric on Fin 10. -/
def eta55 : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j => eta55Levi (fin10Equiv i) (fin10Equiv j)

/-- Condition for a 10×10 matrix to be skew-adjoint w.r.t. eta55. -/
def IsSO55Matrix (M : Matrix (Fin 10) (Fin 10) ℝ) : Prop :=
  Mᵀ * eta55 + eta55 * M = 0

/-- THEOREM 9: The genuine so(5,5) Lie subalgebra inside Mat10. -/
def so55LieSubalgebra : LieSubalgebra ℝ (Matrix (Fin 10) (Fin 10) ℝ) where
  carrier := { M : Matrix (Fin 10) (Fin 10) ℝ | IsSO55Matrix M }
  add_mem' {M N} hM hN := by
    dsimp [IsSO55Matrix] at *
    calc (M + N)ᵀ * eta55 + eta55 * (M + N)
      _ = (Mᵀ + Nᵀ) * eta55 + (eta55 * M + eta55 * N) := by rw [transpose_add, mul_add]
      _ = (Mᵀ * eta55 + eta55 * M) + (Nᵀ * eta55 + eta55 * N) := by
        rw [add_mul]
        abel
      _ = 0 + 0 := by rw [hM, hN]
      _ = 0 := add_zero 0
  zero_mem' := by dsimp [IsSO55Matrix]; simp
  smul_mem' c {M} hM := by
    dsimp [IsSO55Matrix] at *
    calc (c • M)ᵀ * eta55 + eta55 * (c • M)
      _ = c • (Mᵀ * eta55) + c • (eta55 * M) := by rw [transpose_smul, smul_mul, Matrix.mul_smul]
      _ = c • (Mᵀ * eta55 + eta55 * M) := by rw [smul_add]
      _ = c • (0 : Matrix (Fin 10) (Fin 10) ℝ) := by rw [hM]
      _ = 0 := smul_zero c
  lie_mem' {M N} hM hN := by
    dsimp [IsSO55Matrix] at *
    have hM_eq : Mᵀ * eta55 = - (eta55 * M) := eq_neg_of_add_eq_zero_left hM
    have hN_eq : Nᵀ * eta55 = - (eta55 * N) := eq_neg_of_add_eq_zero_left hN
    change (M * N - N * M)ᵀ * eta55 + eta55 * (M * N - N * M) = 0
    rw [transpose_sub, transpose_mul, transpose_mul, sub_mul]
    rw [mul_assoc, mul_assoc]
    rw [hM_eq, hN_eq]
    rw [mul_neg, mul_neg]
    rw [← mul_assoc, ← mul_assoc]
    rw [hN_eq, hM_eq]
    rw [neg_mul, neg_mul, neg_neg, neg_neg]
    rw [mul_sub, mul_assoc, mul_assoc]
    abel

/-- THEOREM 10: derivationToSO55 lands in so55LieSubalgebra. -/
theorem derivationToSO55_mem_so55LieSubalgebra (D : SODE) :
    derivationToSO55 D ∈ so55LieSubalgebra := by
  have h := so44ToSO55_preserves_eta55FromSum
    (canonicalDerivationFinMatrix D)
    (canonicalDerivationFinMatrix_isEtaSkew D)
  dsimp [so55LieSubalgebra, Set.mem_setOf_eq, IsSO55Matrix, eta55,
         InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge.eta55LeviMat10,
         Matrix.reindex, eta55FromSum, IsSO55LeviMatrix] at *
  exact h

/-- Elementary Clifford bivector for matrix generator (i, j). -/
def elementaryBivector (i j : Fin 10) : SpinBivector55 :=
  ⟨⁅ι55 (v55Basis i), ι55 (v55Basis j)⁆,
    LieSubalgebra.subset_lieSpan (Set.mem_range_self (v55Basis i, v55Basis j))⟩

/-- Linear map realizing an so(5,5) matrix as a Clifford bivector. -/
def so55MatrixToSpinBivector :
    Matrix (Fin 10) (Fin 10) ℝ →ₗ[ℝ] SpinBivector55 where
  toFun M := ∑ i : Fin 10, ∑ j : Fin 10, (M i j) • elementaryBivector i j
  map_add' M N := by
    dsimp
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' r M := by
    dsimp
    simp only [mul_smul, Finset.smul_sum]

/-- THEOREM 11: The canonical derivation lifts to a SpinBivector55. -/
def canonicalDerivationToSpinBivector (D : SODE) : SpinBivector55 :=
  so55MatrixToSpinBivector (derivationToSO55 D)

/-- THEOREM 12: Linearity of the canonical lift over addition. -/
theorem canonicalDerivationToSpinBivector_map_add (D E : SODE) :
    canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [derivationToSO55_add]
  exact so55MatrixToSpinBivector.map_add _ _

/-- THEOREM 13: Linearity of the canonical lift over scalar multiplication. -/
theorem canonicalDerivationToSpinBivector_map_smul (r : ℝ) (D : SODE) :
    canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [derivationToSO55_smul]
  exact so55MatrixToSpinBivector.map_smul r _

/-- THEOREM 14: Spinor action chirality commutation. -/
theorem canonicalDerivationSpinorAction_commutes_chirality (D : SODE) :
    canonicalDerivationSpinorAction D * chirality55 =
      chirality55 * canonicalDerivationSpinorAction D :=
  spinBivectorMatrix_commutes_chirality55 (canonicalDerivationSpinBivector D)

/-- THEOREM 15: Spinor Witt volume commutation. -/
theorem canonicalDerivationSpinorAction_commutes_wittVolume (D : SODE) :
    canonicalDerivationSpinorAction D * spinorWittVolume =
      spinorWittVolume * canonicalDerivationSpinorAction D :=
  spinBivectorMatrix_commutes_spinorWittVolume (canonicalDerivationSpinBivector D)

/-- MASTER THEOREM: The complete Dual Exponential Architecture. -/
theorem dual_exponential_architecture_master
    (D : Derivation A) (K X : A) (D_spl E_spl : SODE) (r : ℝ) :
    (D (adK K X) - adK K (D X) = adK (D K) X) ∧
    (D K = 0 →
      derivationCommutator D (modularDerivation K) = modularDerivation 0) ∧
    ((∀ x, K * x = x * K) → ∀ Y, bracket D (modularDerivation K) Y = 0) ∧
    (derivationToSO55 D_spl ∈ so55LieSubalgebra) ∧
    (canonicalDerivationToSpinBivector (D_spl + E_spl) =
      canonicalDerivationToSpinBivector D_spl + canonicalDerivationToSpinBivector E_spl) ∧
    (canonicalDerivationToSpinBivector (r • D_spl) =
       r • canonicalDerivationToSpinBivector D_spl) ∧
    (canonicalDerivationSpinorAction D_spl * chirality55 =
       chirality55 * canonicalDerivationSpinorAction D_spl) ∧
    (canonicalDerivationSpinorAction D_spl * spinorWittVolume =
       spinorWittVolume * canonicalDerivationSpinorAction D_spl) := by
  refine ⟨dual_flow_commutator D K X, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h_adiabatic
    exact adiabatic_commutator_zero D K h_adiabatic
  · intro h_center Y
    exact central_commutator_zero D K h_center Y
  · exact derivationToSO55_mem_so55LieSubalgebra D_spl
  · exact canonicalDerivationToSpinBivector_map_add D_spl E_spl
  · exact canonicalDerivationToSpinBivector_map_smul r D_spl
  · exact canonicalDerivationSpinorAction_commutes_chirality D_spl
  · exact canonicalDerivationSpinorAction_commutes_wittVolume D_spl

end InfoGeometry.Canonical.DualExponentialArchitecture

end noncomputable section
