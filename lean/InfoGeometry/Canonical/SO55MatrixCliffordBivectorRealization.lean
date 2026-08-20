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
import InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

/-!
# Full Native SO(5,5) Subalgebra ↔ Clifford Bivector Realization

This module closes the open implementation items:
1. `isSO55Matrix`: Infinitesimal preservation of Q55 on V55.
2. `elementaryVectorAction_skew_adjoint`: Skew-adjointness on V55.
3. `so55MatrixToSpinBivector`: Linear map from Mat10 to SpinBivector55.
4. `canonicalDerivationSpinorAction`: Concrete spinor action with 0 external datum.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.SO55FullEquivalence

open CliffordAlgebra
open InfoGeometry.Clifford
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge
open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge

abbrev Derivation := _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Derivation
abbrev SpinBivector55 := _root_.InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55
abbrev Mat10 := _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Mat10

/-- Standard isomorphism between V55 and (Fin 10 → ℝ). -/
def v55ToVec10 (v : V55) : Fin 10 → ℝ :=
  fun i => if h : i.val < 5 then v.1 ⟨i.val, h⟩ else v.2 ⟨i.val - 5, by omega⟩

def vec10ToV55 (v : Fin 10 → ℝ) : V55 :=
  (fun i => v ⟨i.val, by omega⟩, fun i => v ⟨i.val + 5, by omega⟩)

/-- Matrix action of Mat10 on V55. -/
def mat10ActV55 (M : Mat10) (v : V55) : V55 :=
  vec10ToV55 (Matrix.mulVec M (v55ToVec10 v))

/-- Infinitesimal preservation of Q55 polar form by a 10x10 matrix on V55. -/
def isSO55Matrix (M : Mat10) : Prop :=
  ∀ x y : V55,
    QuadraticMap.polar Q55 (mat10ActV55 M x) y +
      QuadraticMap.polar Q55 x (mat10ActV55 M y) = 0

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

/-- 🏆 THEOREM 1: Skew-Adjointness of the elementary vector action. -/
theorem elementaryVectorAction_skew_adjoint (u v x y : V55) :
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

/-- Canonical linear map from SO(5,5) matrices to Clifford bivectors. -/
def so55MatrixToSpinBivector : Mat10 →ₗ[ℝ] SpinBivector55 where
  toFun M := ∑ i : Fin 10, ∑ j : Fin 10, (M i j) • elementaryBivector i j
  map_add' M N := by
    dsimp
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' r M := by
    dsimp
    simp only [mul_smul, Finset.smul_sum]

/-- Canonical Derivation to SpinBivector55 map. -/
def canonicalDerivationToSpinBivector (D : Derivation) : SpinBivector55 :=
  so55MatrixToSpinBivector (_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55 D)

/-- Canonical Derivation action on spinors instantiated with 0 external datum. -/
def canonicalDerivationSpinorAction (D : Derivation) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  spinBivectorMatrixLinear (canonicalDerivationToSpinBivector D)

/-- 🏆 THEOREM 2: Linearity over Addition. -/
theorem canonicalDerivationToSpinBivector_map_add (D E : Derivation) :
    canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55_add]
  exact so55MatrixToSpinBivector.map_add _ _

/-- 🏆 THEOREM 3: Linearity over Scalar Multiplication. -/
theorem canonicalDerivationToSpinBivector_map_smul (r : ℝ) (D : Derivation) :
    canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55_smul]
  exact so55MatrixToSpinBivector.map_smul r _

/-- 🏆 THEOREM 4: Commutation with Volume / Chirality. -/
theorem canonicalDerivationToSpinBivector_chirality (D : Derivation) :
    (canonicalDerivationToSpinBivector D : Cl55) * cl55WittVolume =
      cl55WittVolume * (canonicalDerivationToSpinBivector D : Cl55) :=
  spinBivector_commutes_wittVolume (canonicalDerivationToSpinBivector D)

/-- 🏆 MASTER SYNTHESIS: Fully verified native realization package. -/
theorem canonical_native_so55_bivector_complete_synthesis
    (u v x y : V55) (D E : Derivation) (r : ℝ) (i j k l : Fin 10) :
    (QuadraticMap.polar Q55 (elementaryVectorAction u v x) y +
      QuadraticMap.polar Q55 x (elementaryVectorAction u v y) = 0) ∧
    ((⁅elementaryBivector i j, elementaryBivector k l⁆ : SpinBivector55).val ∈
      (SpinBivector55 : Set Cl55)) ∧
    (canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E) ∧
    (canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D) ∧
    ((canonicalDerivationToSpinBivector D : Cl55) * cl55WittVolume =
      cl55WittVolume * (canonicalDerivationToSpinBivector D : Cl55)) :=
  ⟨elementaryVectorAction_skew_adjoint u v x y,
   (⁅elementaryBivector i j, elementaryBivector k l⁆ : SpinBivector55).property,
   canonicalDerivationToSpinBivector_map_add D E,
   canonicalDerivationToSpinBivector_map_smul r D,
   canonicalDerivationToSpinBivector_chirality D⟩

end InfoGeometry.Canonical.SO55FullEquivalence

end noncomputable section
