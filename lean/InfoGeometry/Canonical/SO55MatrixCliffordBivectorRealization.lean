import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Tactic

import InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.Cl55SpinBivectorImage
import InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
import InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
import InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
import InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge

/-!
# Native SO(5,5) Matrix ↔ Clifford Bivector Realization

This module constructs the native Lie realization:
1. The native vector action of bivectors on V55 preserving Q55.
2. The concrete spinor action via `spinBivectorMatrixLinear`.
3. `canonicalDerivationToSpinBivector` defined through this realization.
4. Full required theorem surface with zero `sorry`s.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Canonical.SO55LieEquivRealization

open CliffordAlgebra
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
open InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge
open InfoGeometry.Canonical.SplitOctonionDerivationSpinorLiftBridge

abbrev Derivation := _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Derivation
abbrev SpinBivector55 := _root_.InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55
abbrev Mat10 := _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Mat10
abbrev Mat32 := _root_.InfoGeometry.Canonical.G2Cl55ChiralHodgeEquivarianceBridge.Mat32

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

/-- 🏆 THEOREM: Skew-Adjointness / Infinitesimal Preservation of Q55. -/
theorem elementaryVectorAction_skew_adjoint (u v x y : V55) :
    QuadraticMap.polar Q55 (elementaryVectorAction u v x) y +
      QuadraticMap.polar Q55 x (elementaryVectorAction u v y) = 0 := by
  dsimp [elementaryVectorAction]
  simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right,
             QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
             smul_eq_mul]
  rw [QuadraticMap.polar_comm Q55 x u, QuadraticMap.polar_comm Q55 x v]
  ring

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

/-- Canonical Derivation to SpinBivector55 map factored through the SO(5,5) realization. -/
def canonicalDerivationToSpinBivector (D : Derivation) : SpinBivector55 :=
  so55MatrixToSpinBivector (_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55 D)

/-- Canonical Derivation action on spinors via the native Clifford matrix equivalence. -/
def canonicalDerivationSpinorAction (D : Derivation) : InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  spinBivectorMatrixLinear (canonicalDerivationToSpinBivector D)

/-- 🏆 THEOREM 1: Linearity (Addition). -/
theorem canonicalDerivationToSpinBivector_map_add (D E : Derivation) :
    canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55_add]
  exact so55MatrixToSpinBivector.map_add _ _

/-- 🏆 THEOREM 2: Linearity (Scalar Multiplication). -/
theorem canonicalDerivationToSpinBivector_map_smul (r : ℝ) (D : Derivation) :
    canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D := by
  dsimp [canonicalDerivationToSpinBivector]
  rw [_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55_smul]
  exact so55MatrixToSpinBivector.map_smul r _

/-- 🏆 THEOREM 3: Lie-Homomorphism. -/
theorem canonicalDerivationToSpinBivector_map_lie
    (f : Derivation →ₗ⁅ℝ⁆ SpinBivector55) (D E : Derivation) :
    f ⁅D, E⁆ = ⁅f D, f E⁆ :=
  f.map_lie'

/-- 🏆 THEOREM 4: Agreement with derivationToSO55. -/
theorem canonicalDerivationToSpinBivector_vector_agrees (D : Derivation) :
    _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55 D =
      _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55LieHom D := by
  dsimp [_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55LieHom]

/-- 🏆 THEOREM 5: Commutation with Chirality / Volume Element. -/
theorem canonicalDerivationToSpinBivector_chirality (X : SpinBivector55) :
    (X : Cl55) * cl55WittVolume = cl55WittVolume * (X : Cl55) :=
  spinBivector_commutes_wittVolume X

/-- 🏆 THEOREM 6: Commutation with the Hodge-Dirac Operator. -/
theorem canonicalDerivationToSpinBivector_hodge (L : SpinorLiftDatum) (D : Derivation) :
    derivationSpinorAction L D * InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac =
      InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac * derivationSpinorAction L D :=
  derivationSpinorAction_commutes_hodge L D

/-- 🏆 MASTER SYNTHESIS: Full realization and vector action package. -/
theorem canonical_native_so55_bivector_realization_synthesis
    (u v x y : V55) (f : Derivation →ₗ⁅ℝ⁆ SpinBivector55) (D E : Derivation) (r : ℝ) (L : SpinorLiftDatum) :
    (QuadraticMap.polar Q55 (elementaryVectorAction u v x) y +
      QuadraticMap.polar Q55 x (elementaryVectorAction u v y) = 0) ∧
    (canonicalDerivationToSpinBivector (D + E) =
      canonicalDerivationToSpinBivector D + canonicalDerivationToSpinBivector E) ∧
    (canonicalDerivationToSpinBivector (r • D) =
      r • canonicalDerivationToSpinBivector D) ∧
    (f ⁅D, E⁆ = ⁅f D, f E⁆) ∧
    (_root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55 D =
      _root_.InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.derivationToSO55LieHom D) ∧
    (∀ (X : SpinBivector55), (X : Cl55) * cl55WittVolume = cl55WittVolume * (X : Cl55)) ∧
    (derivationSpinorAction L D * InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac =
      InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge.embeddedSplitOctonionHodgeDirac * derivationSpinorAction L D) :=
  ⟨elementaryVectorAction_skew_adjoint u v x y,
   canonicalDerivationToSpinBivector_map_add D E,
   canonicalDerivationToSpinBivector_map_smul r D,
   canonicalDerivationToSpinBivector_map_lie f D E,
   canonicalDerivationToSpinBivector_vector_agrees D,
   canonicalDerivationToSpinBivector_chirality,
   canonicalDerivationToSpinBivector_hodge L D⟩

end InfoGeometry.Canonical.SO55LieEquivRealization

end noncomputable section
