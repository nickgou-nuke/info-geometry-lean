import InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SO55MatrixLieSubalgebra
import InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge
import InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.Cl55SpinBivectorImage
import InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
import InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Clifford.Cl55BivectorVectorRepresentation
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

/-!
# Proved Native SO(5,5) Linear Maps, Levi Metric Preservation, and Vector Commutator Action
File: `lean/InfoGeometry/Canonical/SO55RestrictedBivectorEquiv.lean`
-/

noncomputable section

namespace InfoGeometry.Canonical.SO55RestrictedLemmas

open InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge
open InfoGeometry.Lie.SplitOctonionDerivationWittBlockRealization
open InfoGeometry.Lie.SO55MatrixSubalgebra
open InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge
open InfoGeometry.Lie.G2SO44SO55LieInclusionBridge
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorImage
open InfoGeometry.Clifford.Cl55SpinBivectorLieBridge
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.BivectorVectorRepresentation
open CliffordAlgebra
open Matrix

abbrev Derivation := InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Derivation
abbrev SpinBivector55 := InfoGeometry.Clifford.Cl55SpinBivectorImage.SpinBivector55
abbrev Mat8 := InfoGeometry.Algebra.FiniteSpin.Mat8R
abbrev Mat10 := InfoGeometry.Lie.SplitOctonionDerivationSO55Bridge.Mat10
abbrev Mat10Sum := Matrix (Fin 8 ⊕ Fin 2) (Fin 8 ⊕ Fin 2) ℝ

/-- The exact (5,5) Levi metric transported to Fin 10 via the canonical coordinate bijection. -/
def eta55FromSum : Mat10 :=
  fun i j => eta55Levi (fin10Equiv i) (fin10Equiv j)

/-- Condition for a Mat10 to be skew-adjoint with respect to eta55FromSum. -/
def IsSO55LeviMatrix (M : Mat10) : Prop :=
  Mᵀ * eta55FromSum + eta55FromSum * M = 0

theorem isSO55Levi_zero : IsSO55LeviMatrix (0 : Mat10) := by
  dsimp [IsSO55LeviMatrix]
  simp

theorem isSO55Levi_add {M N : Mat10} (hM : IsSO55LeviMatrix M) (hN : IsSO55LeviMatrix N) :
    IsSO55LeviMatrix (M + N) := by
  dsimp [IsSO55LeviMatrix] at *
  calc (M + N)ᵀ * eta55FromSum + eta55FromSum * (M + N)
    _ = (Mᵀ + Nᵀ) * eta55FromSum + (eta55FromSum * M + eta55FromSum * N) := by rw [transpose_add, mul_add]
    _ = (Mᵀ * eta55FromSum + eta55FromSum * M) + (Nᵀ * eta55FromSum + eta55FromSum * N) := by
      rw [add_mul]
      abel
    _ = 0 + 0 := by rw [hM, hN]
    _ = 0 := add_zero 0

theorem isSO55Levi_smul (c : ℝ) {M : Mat10} (hM : IsSO55LeviMatrix M) :
    IsSO55LeviMatrix (c • M) := by
  dsimp [IsSO55LeviMatrix] at *
  calc (c • M)ᵀ * eta55FromSum + eta55FromSum * (c • M)
    _ = c • (Mᵀ * eta55FromSum) + c • (eta55FromSum * M) := by rw [transpose_smul, smul_mul, Matrix.mul_smul]
    _ = c • (Mᵀ * eta55FromSum + eta55FromSum * M) := by rw [smul_add]
    _ = c • (0 : Mat10) := by rw [hM]
    _ = 0 := smul_zero c

theorem isSO55Levi_bracket {M N : Mat10} (hM : IsSO55LeviMatrix M) (hN : IsSO55LeviMatrix N) :
    IsSO55LeviMatrix (⁅M, N⁆ : Mat10) := by
  dsimp [IsSO55LeviMatrix] at *
  have hM_eq : Mᵀ * eta55FromSum = - (eta55FromSum * M) := eq_neg_of_add_eq_zero_left hM
  have hN_eq : Nᵀ * eta55FromSum = - (eta55FromSum * N) := eq_neg_of_add_eq_zero_left hN
  change (M * N - N * M)ᵀ * eta55FromSum + eta55FromSum * (M * N - N * M) = 0
  rw [transpose_sub, transpose_mul, transpose_mul, sub_mul]
  rw [mul_assoc, mul_assoc]
  rw [hM_eq, hN_eq]
  rw [mul_neg, mul_neg]
  rw [← mul_assoc, ← mul_assoc]
  rw [hN_eq, hM_eq]
  rw [neg_mul, neg_mul, neg_neg, neg_neg]
  rw [mul_sub, mul_assoc, mul_assoc]
  abel

/-- The native $\mathfrak{so}(5,5)$ Levi matrix Lie subalgebra on Fin 10. -/
abbrev so55LeviLieSubalgebra : LieSubalgebra ℝ Mat10 := so55LieSubalgebra

theorem so44ToSO55_apply (M : Mat8) (i j : Fin 10) :
    so44ToSO55 M i j = so44ToSO55Sum M (fin10Equiv i) (fin10Equiv j) := by
  dsimp [so44ToSO55, so44ToSO55Sum]
  rcases fin10Equiv i with a | a <;> rcases fin10Equiv j with b | b <;> rfl

/-- 🏆 THEOREM: so44ToSO55 of any skew-symmetric 8x8 matrix preserves eta55FromSum on Fin 10. -/
theorem so44ToSO55_preserves_eta55FromSum (M : Mat8) (hM : IsEtaSkew eta44 M) :
    IsSO55LeviMatrix (so44ToSO55 M) := by
  dsimp [IsSO55LeviMatrix]
  ext i j
  dsimp [transpose, Matrix.mul_apply, eta55FromSum]
  have h1 : (∑ k : Fin 10, so44ToSO55 M k i * eta55Levi (fin10Equiv k) (fin10Equiv j)) =
      ∑ s : Fin 8 ⊕ Fin 2, so44ToSO55Sum M s (fin10Equiv i) * eta55Levi s (fin10Equiv j) := by
    rw [← fin10Equiv.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [so44ToSO55_apply]
    simp
  have h2 : (∑ k : Fin 10, eta55Levi (fin10Equiv i) (fin10Equiv k) * so44ToSO55 M k j) =
      ∑ s : Fin 8 ⊕ Fin 2, eta55Levi (fin10Equiv i) s * so44ToSO55Sum M s (fin10Equiv j) := by
    rw [← fin10Equiv.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro k _
    rw [so44ToSO55_apply]
    simp
  rw [h1, h2]
  have hskew : (so44ToSO55Sum M)ᵀ * eta55Levi + eta55Levi * (so44ToSO55Sum M) = 0 :=
    so44ToSO55Sum_preserves_etaSkew M hM
  have hij := congrFun (congrFun hskew (fin10Equiv i)) (fin10Equiv j)
  dsimp [transpose, Matrix.mul_apply] at hij
  exact hij

/-- 🏆 THEOREM: Any so(4,4) matrix embedded into 10x10 strictly lands in so55LeviLieSubalgebra -/
theorem so44ToSO55_mem_so55LeviSubalgebra (M : Mat8) (hM : IsEtaSkew eta44 M) :
    so44ToSO55 M ∈ so55LeviLieSubalgebra :=
  so44ToSO55_preserves_eta55FromSum M hM

theorem derivationToSO55_mem_so55LeviSubalgebra (D : Derivation) :
    derivationToSO55 D ∈ so55LeviLieSubalgebra := by
  exact so44ToSO55_mem_so55LeviSubalgebra
    (canonicalDerivationFinMatrix D)
    (canonicalDerivationFinMatrix_isEtaSkew D)

/-- 🏆 THEOREM: Derivation to SO(5,5) matrix strictly lands in the authoritative so55LieSubalgebra -/
theorem derivationToSO55_mem_so55LieSubalgebra (D : Derivation) :
    derivationToSO55 D ∈ so55LieSubalgebra := by
  have h := so44ToSO55_preserves_eta55FromSum
    (canonicalDerivationFinMatrix D)
    (canonicalDerivationFinMatrix_isEtaSkew D)
  dsimp [so55LieSubalgebra, Set.mem_setOf_eq, IsSO55Matrix, eta55,
         InfoGeometry.Lie.SplitOctonionSO44SO55OrthogonalBridge.eta55LeviMat10,
         Matrix.reindex, eta55FromSum, IsSO55LeviMatrix] at *
  exact h

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

/-- Linear map from the so(5,5) matrix Lie subalgebra to SpinBivector55. -/
def so55RestrictedToBivector (M : so55LeviLieSubalgebra) : SpinBivector55 :=
  ∑ i : Fin 10, ∑ j : Fin 10, ((M.val i j) • elementaryBivector i j)

/-- 1. Linearity over addition on the restricted subalgebra. -/
theorem so55RestrictedToBivector_add (M N : so55LeviLieSubalgebra) :
    so55RestrictedToBivector (M + N) =
      so55RestrictedToBivector M + so55RestrictedToBivector N := by
  dsimp [so55RestrictedToBivector]
  simp only [add_smul, Finset.sum_add_distrib]

/-- 2. Linearity over scalar multiplication on the restricted subalgebra. -/
theorem so55RestrictedToBivector_smul (r : ℝ) (M : so55LeviLieSubalgebra) :
    so55RestrictedToBivector (r • M) = r • so55RestrictedToBivector M := by
  dsimp [so55RestrictedToBivector]
  simp only [Finset.smul_sum, smul_smul]

/-- 3. Bundled LinearMap from so55LeviLieSubalgebra to SpinBivector55. -/
def so55RestrictedToBivectorLinear : so55LeviLieSubalgebra →ₗ[ℝ] SpinBivector55 where
  toFun := so55RestrictedToBivector
  map_add' := so55RestrictedToBivector_add
  map_smul' := so55RestrictedToBivector_smul

/-- 4. Unconditional Canonical Derivation lift into SpinBivector55. -/
def canonicalDerivationSpinBivector (D : Derivation) : SpinBivector55 :=
  ∑ i : Fin 10, ∑ j : Fin 10, ((derivationToSO55 D i j) • elementaryBivector i j)

/-- 5. Bundled LinearMap for canonicalDerivationSpinBivector. -/
def canonicalDerivationSpinBivectorLinear : Derivation →ₗ[ℝ] SpinBivector55 where
  toFun := canonicalDerivationSpinBivector
  map_add' D E := by
    dsimp [canonicalDerivationSpinBivector]
    simp only [derivationToSO55_add, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r D := by
    dsimp [canonicalDerivationSpinBivector]
    simp only [derivationToSO55_smul, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

/-- 6. Unconditional Spinor Action without SpinorLiftDatum. -/
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

/-- 🏆 THEOREM: Commutator of Vector Actions matches Bivector Lie Bracket -/
theorem canonicalDerivation_bracket_vector_action (u₁ v₁ u₂ v₂ w : V55) :
    ⁅⁅ι55 u₁ * ι55 v₁, ι55 u₂ * ι55 v₂⁆, ι55 w⁆ =
      ι55 (bivectorVectorTransform u₁ v₁ (bivectorVectorTransform u₂ v₂ w) -
           bivectorVectorTransform u₂ v₂ (bivectorVectorTransform u₁ v₁ w)) :=
  bivector_bracket_vector_action u₁ v₁ u₂ v₂ w

end InfoGeometry.Canonical.SO55RestrictedLemmas

end noncomputable section
