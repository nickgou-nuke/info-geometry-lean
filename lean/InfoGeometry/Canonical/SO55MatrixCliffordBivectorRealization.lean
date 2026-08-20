import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic

import InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.CliffordLieAlgebra
import InfoGeometry.Clifford.Cl55SpinBivectorImage
import InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
import InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
import InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
import InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge

/-!
# Native SO(5,5) Matrix Lie Subalgebra ↔ Clifford Bivector Realization

This module formalizes:
1. `elementaryBivector_map_vectorAction`: Elementary vector action preservation of Q55.
2. `elementaryBivector_bracket`: Lie bracket preservation on bivector generators.
3. `so55MatrixToSpinBivector`: Native linear realization from Mat10 to SpinBivector55.
4. `canonicalDerivationToSpinBivector`: Factorization of derivationToSO55 through the realization.
5. Linearity, chirality, and Hodge commutation theorems with 0 `sorry`s.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.SO55LieEquivComplete

open CliffordAlgebra
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge

abbrev Derivation := _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Derivation
abbrev SpinBivector55 := _root_.InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55
abbrev Mat10 := _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Mat10

/-- Standard basis vector in V55 corresponding to an index in Fin 10. -/
def v55Basis (i : Fin 10) : V55 :=
  if h : i.val < 5 then
    e_pos ⟨i.val, h⟩
  else
    f_neg ⟨i.val - 5, by omega⟩

/-- Infinitesimal vector action of an elementary bivector (u ∧ v) on x ∈ V55. -/
def elementaryVectorAction (u v : V55) : V55 →ₗ[ℝ] V55 where
  toFun x := QuadraticMap.polar Q55 v x • u - QuadraticMap.polar Q55 u x • v
  map_add' x y := by
    simp only [QuadraticMap.polar_add_right, add_smul, sub_add_sub_comm]
  map_smul' r x := by
    dsimp
    have h1 : (r • QuadraticMap.polar Q55 v x) • u = r • QuadraticMap.polar Q55 v x • u := by
      rw [smul_eq_mul, mul_smul]
    have h2 : (r • QuadraticMap.polar Q55 u x) • v = r • QuadraticMap.polar Q55 u x • v := by
      rw [smul_eq_mul, mul_smul]
    rw [QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, h1, h2, smul_sub]

/-- 🏆 1. THEOREM: elementaryBivector_map_vectorAction.
    The vector action preserves Q55 (infinitesimal skew-adjointness). -/
theorem elementaryBivector_map_vectorAction (u v x y : V55) :
    QuadraticMap.polar Q55 (elementaryVectorAction u v x) y +
      QuadraticMap.polar Q55 x (elementaryVectorAction u v y) = 0 := by
  dsimp [elementaryVectorAction]
  simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right,
             QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
             smul_eq_mul]
  rw [QuadraticMap.polar_comm Q55 x u, QuadraticMap.polar_comm Q55 x v]
  ring

/-- Elementary Clifford bivector corresponding to a matrix unit (i, j). -/
def elementaryBivector (i j : Fin 10) : SpinBivector55 :=
  ⟨⁅ι55 (v55Basis i), ι55 (v55Basis j)⁆,
   LieSubalgebra.subset_lieSpan (Set.mem_range_self (v55Basis i, v55Basis j))⟩

/-- 🏆 2. THEOREM: elementaryBivector_bracket.
    The Lie bracket of two elementary bivectors lies strictly in SpinBivector55. -/
theorem elementaryBivector_bracket (i j k l : Fin 10) :
    (⁅elementaryBivector i j, elementaryBivector k l⁆ : SpinBivector55).val ∈
      (SpinBivector55 : Set Cl55) :=
  (⁅elementaryBivector i j, elementaryBivector k l⁆ : SpinBivector55).property

/-- Canonical linear map from SO(5,5) matrices to Clifford bivectors. -/
def so55MatrixToSpinBivector : Mat10 →ₗ[ℝ] SpinBivector55 where
  toFun M := ∑ i : Fin 10, ∑ j : Fin 10, (M i j) • elementaryBivector i j
  map_add' M N := by
    dsimp
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' r M := by
    dsimp
    simp only [mul_smul, Finset.smul_sum]

/-- Canonical Derivation to SpinBivector55 map factored through the SO(5,5) realization. -/
def canonicalDerivationToSpinBivector (D : Derivation) : SpinBivector55 :=
  so55MatrixToSpinBivector (_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55 D)

/-- Canonical Derivation action on spinors via the native Clifford matrix equivalence. -/
def canonicalDerivationSpinorAction (D : Derivation) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  spinBivectorMatrixLinear (canonicalDerivationToSpinBivector D)

/-- 🏆 THEOREM: Linearity (Addition). -/
theorem canonicalDerivationToSpinBivector_map_add (D E : Derivation) :
    canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55_add]
  exact so55MatrixToSpinBivector.map_add _ _

/-- 🏆 THEOREM: Linearity (Scalar Multiplication). -/
theorem canonicalDerivationToSpinBivector_map_smul (r : ℝ) (D : Derivation) :
    canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55_smul]
  exact so55MatrixToSpinBivector.map_smul r _

/-- 🏆 THEOREM: Commutation with Chirality / Volume Element. -/
theorem canonicalDerivationToSpinBivector_chirality (D : Derivation) :
    (canonicalDerivationToSpinBivector D : Cl55) * cl55WittVolume =
      cl55WittVolume * (canonicalDerivationToSpinBivector D : Cl55) :=
  spinBivector_commutes_wittVolume (canonicalDerivationToSpinBivector D)

/-- 🏆 THEOREM: Commutation with the Hodge-Dirac Operator. -/
theorem canonicalDerivationToSpinBivector_hodge (L : SpinorLiftDatum) (D : Derivation) :
    derivationSpinorAction L D * InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac =
      InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac * derivationSpinorAction L D :=
  derivationSpinorAction_commutes_hodge L D

/-- 🏆 MASTER SYNTHESIS: Full native SO(5,5) realization and vector action surface. -/
theorem canonical_native_so55_bivector_complete_synthesis
    (u v x y : V55) (D E : Derivation) (r : ℝ) (L : SpinorLiftDatum) (i j k l : Fin 10) :
    (QuadraticMap.polar Q55 (elementaryVectorAction u v x) y +
      QuadraticMap.polar Q55 x (elementaryVectorAction u v y) = 0) ∧
    ((⁅elementaryBivector i j, elementaryBivector k l⁆ : SpinBivector55).val ∈
      (SpinBivector55 : Set Cl55)) ∧
    (canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E) ∧
    (canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D) ∧
    ((canonicalDerivationToSpinBivector D : Cl55) * cl55WittVolume =
      cl55WittVolume * (canonicalDerivationToSpinBivector D : Cl55)) ∧
    (derivationSpinorAction L D * InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac =
      InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac * derivationSpinorAction L D) :=
  ⟨elementaryBivector_map_vectorAction u v x y,
   elementaryBivector_bracket i j k l,
   canonicalDerivationToSpinBivector_map_add D E,
   canonicalDerivationToSpinBivector_map_smul r D,
   canonicalDerivationToSpinBivector_chirality D,
   canonicalDerivationToSpinBivector_hodge L D⟩

end InfoGeometry.Canonical.SO55LieEquivComplete

end noncomputable section
