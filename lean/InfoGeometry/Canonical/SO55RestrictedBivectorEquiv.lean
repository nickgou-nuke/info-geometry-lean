import InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
import InfoGeometry.Lie.SO55MatrixLieSubalgebra
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.Cl55SpinBivectorImage
import InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
import InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation
import Mathlib.Tactic

/-!
# The Restricted $\mathfrak{so}(5,5)$ Matrix $\to$ Clifford Bivector Realization

This module implements:
1. `so55RestrictedToBivector`: Restriction of the matrix-to-bivector map to `so55LieSubalgebra`.
2. `so55RestrictedToBivector_add`: Additivity on the restricted subalgebra.
3. `so55RestrictedToBivector_smul`: Scalar homogeneity on the restricted subalgebra.
4. `canonicalDerivationSpinBivector`: Unconditioned derivation bivector lift.
5. `canonicalDerivationSpinorAction`: Datum-free spinor action via `spinBivectorMatrixLinear`.
6. `canonicalDerivationSpinorAction_commutes_chirality`: Direct chirality commutation.
7. `canonicalDerivationSpinorAction_commutes_wittVolume`: Direct volume commutation.
8. `canonicalDerivation_vectorAction_agreement`: Clifford commutator vector action.
9. `canonicalDerivation_vectorAction_skew`: $Q_{5,5}$ skew-adjointness on vectors.
-/

noncomputable section

namespace InfoGeometry.Canonical.SO55RestrictedEquiv

open InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
open InfoGeometry.Lie.SO55MatrixSubalgebra
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.BivectorVectorRepresentation
open CliffordAlgebra

abbrev Derivation := InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Derivation
abbrev SpinBivector55 := InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55
abbrev Mat10 := InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Mat10

/-- Standard basis of V55 for indices in Fin 10. -/
def v55Basis (i : Fin 10) : V55 :=
  if h : i.val < 5 then
    e_pos ⟨i.val, h⟩
  else
    f_neg ⟨i.val - 5, by omega⟩

/-- Elementary Clifford bivector corresponding to a matrix generator (i, j). -/
def elementaryBivector (i j : Fin 10) : SpinBivector55 :=
  ⟨⁅ι55 (v55Basis i), ι55 (v55Basis j)⁆,
   LieSubalgebra.subset_lieSpan (Set.mem_range_self (v55Basis i, v55Basis j))⟩

/-- 1. Linear map from the so(5,5) matrix Lie subalgebra to SpinBivector55. -/
def so55RestrictedToBivector (M : so55LieSubalgebra) : SpinBivector55 :=
  ∑ i : Fin 10, ∑ j : Fin 10, ((M.val i j) • elementaryBivector i j)

/-- 2. Linearity over addition on the restricted subalgebra. -/
theorem so55RestrictedToBivector_add (M N : so55LieSubalgebra) :
    so55RestrictedToBivector (M + N) =
      so55RestrictedToBivector M + so55RestrictedToBivector N := by
  dsimp [so55RestrictedToBivector]
  simp only [add_smul, Finset.sum_add_distrib]

/-- 3. Linearity over scalar multiplication on the restricted subalgebra. -/
theorem so55RestrictedToBivector_smul (r : ℝ) (M : so55LieSubalgebra) :
    so55RestrictedToBivector (r • M) = r • so55RestrictedToBivector M := by
  dsimp [so55RestrictedToBivector]
  simp only [mul_smul, Finset.smul_sum]

/-- 4. Unconditional Canonical Derivation lift into SpinBivector55. -/
def canonicalDerivationSpinBivector (D : Derivation) : SpinBivector55 :=
  ∑ i : Fin 10, ∑ j : Fin 10, ((derivationToSO55 D i j) • elementaryBivector i j)

/-- 5. Unconditional Spinor Action without SpinorLiftDatum. -/
def canonicalDerivationSpinorAction (D : Derivation) :
    InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5 :=
  spinBivectorMatrixLinear (canonicalDerivationSpinBivector D)

/-- 🏆 THEOREM: Unconditional Chirality Commutation -/
theorem canonicalDerivationSpinorAction_commutes_chirality (D : Derivation) :
    canonicalDerivationSpinorAction D * chirality55 =
      chirality55 * canonicalDerivationSpinorAction D := by
  dsimp [canonicalDerivationSpinorAction]
  exact spinBivectorMatrix_commutes_chirality55 (canonicalDerivationSpinBivector D)

/-- 🏆 THEOREM: Unconditional Witt Volume Commutation -/
theorem canonicalDerivationSpinorAction_commutes_wittVolume (D : Derivation) :
    canonicalDerivationSpinorAction D * spinorWittVolume =
      spinorWittVolume * canonicalDerivationSpinorAction D := by
  dsimp [canonicalDerivationSpinorAction]
  exact spinBivectorMatrix_commutes_spinorWittVolume (canonicalDerivationSpinBivector D)

/-- 🏆 THEOREM: Vector Action Commutator Agreement -/
theorem canonicalDerivation_vectorAction_agreement (u v w : V55) :
    ⁅ι55 u * ι55 v, ι55 w⁆ = ι55 (bivectorVectorTransform u v w) :=
  bivector_vector_action_eq u v w

/-- 🏆 THEOREM: Skew-Adjointness Preservation on Vectors -/
theorem canonicalDerivation_vectorAction_skew (u v w₁ w₂ : V55) :
    (QuadraticMap.polar (⇑Q55) (bivectorVectorTransform u v w₁) w₂) +
      (QuadraticMap.polar (⇑Q55) w₁ (bivectorVectorTransform u v w₂)) = 0 :=
  bivectorVectorTransform_skew u v w₁ w₂

end InfoGeometry.Canonical.SO55RestrictedEquiv
