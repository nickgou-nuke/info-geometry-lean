import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic

import InfoGeometry.Lie.SO55MatrixLieSubalgebra
import InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.CliffordLieAlgebra
import InfoGeometry.Clifford.Cl55SpinBivectorImage
import InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
import InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation
import InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
import InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

/-!
# Unified SO(5,5) Matrix ↔ Clifford Bivector Realization Bridge
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.SO55GenuineUnifiedBridge

open CliffordAlgebra
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
open InfoGeometry.Clifford.BivectorVectorRepresentation
open InfoGeometry.Lie.SO55MatrixSubalgebra
open InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

abbrev Derivation := _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Derivation
abbrev SpinBivector55 := _root_.InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55
abbrev Mat10 := _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Mat10

/-- Standard basis vector in V55 corresponding to an index in Fin 10. -/
def v55Basis (i : Fin 10) : V55 :=
  if h : i.val < 5 then
    e_pos ⟨i.val, h⟩
  else
    f_neg ⟨i.val - 5, by omega⟩

/-- Elementary Clifford bivector corresponding to a matrix unit (i, j). -/
def elementaryBivector (i j : Fin 10) : SpinBivector55 :=
  ⟨⁅ι55 (v55Basis i), ι55 (v55Basis j)⁆,
   LieSubalgebra.subset_lieSpan (Set.mem_range_self (v55Basis i, v55Basis j))⟩

/-- Canonical linear map from SO(5,5) matrices to Clifford bivectors. -/
def so55MatrixToSpinBivector : Mat10 →ₗ[ℝ] SpinBivector55 where
  toFun M := ∑ i : Fin 10, ∑ j : Fin 10, (M i j) • elementaryBivector i j
  map_add' M N := by
    dsimp
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' r M := by
    dsimp
    simp only [mul_smul, Finset.smul_sum]

/-- Canonical Derivation to SpinBivector55 map without external datum. -/
def canonicalDerivationToSpinBivector (D : Derivation) : SpinBivector55 :=
  so55MatrixToSpinBivector (derivationToSO55 D)

/-- Canonical Derivation action on spinors instantiated with 0 external datum. -/
def canonicalDerivationSpinorAction (D : Derivation) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  spinBivectorMatrixLinear (canonicalDerivationToSpinBivector D)

/-- 🏆 THEOREM 1: Linearity over Addition. -/
theorem canonicalDerivationToSpinBivector_map_add (D E : Derivation) :
    canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [derivationToSO55_add]
  exact so55MatrixToSpinBivector.map_add _ _

/-- 🏆 THEOREM 2: Linearity over Scalar Multiplication. -/
theorem canonicalDerivationToSpinBivector_map_smul (r : ℝ) (D : Derivation) :
    canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [derivationToSO55_smul]
  exact so55MatrixToSpinBivector.map_smul r _

/-- 🏆 THEOREM 3: Vector Action Skew-Adjointness (from BivectorVectorRepresentation). -/
theorem canonical_bivector_vector_action_skew (u v w₁ w₂ : V55) :
    QuadraticMap.polar Q55 (bivectorVectorTransform u v w₁) w₂ +
      QuadraticMap.polar Q55 w₁ (bivectorVectorTransform u v w₂) = 0 :=
  bivectorVectorTransform_skew u v w₁ w₂

/-- 🏆 THEOREM 4: Vector Commutator Action (from BivectorVectorRepresentation). -/
theorem canonical_bivector_vector_action_comm (u v w : V55) :
    ⁅ι55 u * ι55 v, ι55 w⁆ = ι55 (bivectorVectorTransform u v w) :=
  bivector_vector_action_eq u v w

/-- 🏆 THEOREM 5: Commutation with Volume / Chirality. -/
theorem canonicalDerivationToSpinBivector_chirality (D : Derivation) :
    (canonicalDerivationToSpinBivector D : Cl55) * cl55WittVolume =
      cl55WittVolume * (canonicalDerivationToSpinBivector D : Cl55) :=
  spinBivector_commutes_wittVolume (canonicalDerivationToSpinBivector D)

/-- 🏆 MASTER SYNTHESIS: Native verification package. -/
theorem canonical_native_so55_bivector_unified_synthesis
    (u v w₁ w₂ : V55) (D E : Derivation) (r : ℝ) (i j k l : Fin 10) :
    (QuadraticMap.polar Q55 (bivectorVectorTransform u v w₁) w₂ +
      QuadraticMap.polar Q55 w₁ (bivectorVectorTransform u v w₂) = 0) ∧
    (⁅ι55 u * ι55 v, ι55 w₁⁆ = ι55 (bivectorVectorTransform u v w₁)) ∧
    ((⁅elementaryBivector i j, elementaryBivector k l⁆ : SpinBivector55).val ∈
      (SpinBivector55 : Set Cl55)) ∧
    (canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E) ∧
    (canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D) ∧
    ((canonicalDerivationToSpinBivector D : Cl55) * cl55WittVolume =
      cl55WittVolume * (canonicalDerivationToSpinBivector D : Cl55)) :=
  ⟨canonical_bivector_vector_action_skew u v w₁ w₂,
   canonical_bivector_vector_action_comm u v w₁,
   (⁅elementaryBivector i j, elementaryBivector k l⁆ : SpinBivector55).property,
   canonicalDerivationToSpinBivector_map_add D E,
   canonicalDerivationToSpinBivector_map_smul r D,
   canonicalDerivationToSpinBivector_chirality D⟩

end InfoGeometry.Canonical.SO55GenuineUnifiedBridge

end noncomputable section
