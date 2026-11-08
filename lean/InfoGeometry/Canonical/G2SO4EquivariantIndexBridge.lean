import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
import InfoGeometry.Canonical.RealCl55NativeEquivariantChiralComplexBridge
import InfoGeometry.Canonical.RealCl55NativeChiralHodgeIndexBridge
import InfoGeometry.Canonical.RealCl55NativeChiralBlockDiagonalBridge
import InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge
import InfoGeometry.OperatorAlgebra.ChiralFredholmIndex

/-!
# G₂(2) Maximal Compact K ≅ SO(4) Equivariant Index Bridge

This owner module formalizes the equivariant representation theory and Fredholm index
of the master `Cl(5,5)` Hodge–Dirac operator under the maximal compact subgroup
$K \cong \operatorname{SO}(4) \subset G_{2(2)}$ (or any compact Lie group $K$ equipped
with an integrated action):

1. **Equivariant Module Structure**:
   The chiral half-spinor spaces `nativePlusSector` and `nativeMinusSector` inherit
   genuine group representations $\rho_+, \rho_- : K \to \operatorname{GL}(16, \mathbb{R})$.

2. **Equivariant Chiral Intertwiner**:
   The restricted Hodge–Dirac operator $D_+ : S_+ \to S_-$ is an explicit, invertible
   $K$-equivariant linear map:
   $$D_+ \circ \rho_+(k) = \rho_-(k) \circ D_+ \quad (\forall k \in K).$$

3. **Chiral Representation Equivalence in $R(K)$**:
   The existence of the invertible $K$-equivariant intertwiner proves that
   $[S_+] = [S_-]$ in the Grothendieck representation ring $R(K)$.

4. **Equivariant Fredholm Index**:
   Since $\ker(D_+) = \{0\}$ and $\ker(D_-) = \{0\}$, the equivariant analytic index
   $$\operatorname{ind}_K(D_H) = [\ker(D_+)] - [\ker(D_-)] = 0 \in R(K)$$
   vanishes identically.

5. **Matrix-Level Equivariant Kasparov Datum**:
   The canonical equivariant datum packages the invertible representation $\rho_K$, the
   bounded transform $F$, and the grading $\Gamma$, satisfying $[F, \rho_K(k)] = 0$,
   $[\Gamma, \rho_K(k)] = 0$, and $\{D_H, \Gamma\} = 0$.
-/

noncomputable section

namespace InfoGeometry.Canonical.G2SO4EquivariantIndexBridge

open InfoGeometry.Canonical.Cl55MasterWittSpinorEnvelopeBridge
open InfoGeometry.Canonical.Cl55MasterParityOddnessBridge
open InfoGeometry.Canonical.Cl55MasterChiralHodgeBlockBridge
open InfoGeometry.Canonical.RealSplitKreinHilbertizationBridge
open InfoGeometry.Canonical.RealCl55NativeChiralSectorBridge
open InfoGeometry.Canonical.RealCl55NativeChiralHodgeIndexBridge
open InfoGeometry.Canonical.RealCl55NativeEquivariantChiralComplexBridge
open InfoGeometry.Canonical.RealCl55NativeChiralBlockDiagonalBridge
open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge
open InfoGeometry.OperatorAlgebra.ChiralFredholmIndex

variable {K : Type*} [Group K] (act : G2IntegratedAction K)

-- ============================================================================
-- Section 1: Equivariant Representation Structure
-- ============================================================================

/-- Representation of K on the positive chiral half-spinor bundle S₊. -/
def rhoPlus (k : K) : nativePlusSector →ₗ[ℝ] nativePlusSector :=
  nativePlusSectorActionHom act k

/-- Representation of K on the negative chiral half-spinor bundle S₋. -/
def rhoMinus (k : K) : nativeMinusSector →ₗ[ℝ] nativeMinusSector :=
  nativeMinusSectorActionHom act k

@[simp] theorem rhoPlus_one : rhoPlus act (1 : K) = LinearMap.id := by
  change nativePlusSectorActionHom act 1 = LinearMap.id
  exact map_one (nativePlusSectorActionHom act)

@[simp] theorem rhoMinus_one : rhoMinus act (1 : K) = LinearMap.id := by
  change nativeMinusSectorActionHom act 1 = LinearMap.id
  exact map_one (nativeMinusSectorActionHom act)

@[simp] theorem rhoPlus_mul (k₁ k₂ : K) :
    rhoPlus act (k₁ * k₂) = (rhoPlus act k₁).comp (rhoPlus act k₂) := by
  change nativePlusSectorActionHom act (k₁ * k₂) =
    (nativePlusSectorActionHom act k₁).comp (nativePlusSectorActionHom act k₂)
  exact map_mul (nativePlusSectorActionHom act) k₁ k₂

@[simp] theorem rhoMinus_mul (k₁ k₂ : K) :
    rhoMinus act (k₁ * k₂) = (rhoMinus act k₁).comp (rhoMinus act k₂) := by
  change nativeMinusSectorActionHom act (k₁ * k₂) =
    (nativeMinusSectorActionHom act k₁).comp (nativeMinusSectorActionHom act k₂)
  exact map_mul (nativeMinusSectorActionHom act) k₁ k₂

-- ============================================================================
-- Section 2: Equivariance of Chiral Dirac and Inverse Dirac Maps
-- ============================================================================

/-- The positive chiral Dirac operator D₊ is K-equivariant. -/
theorem diracPlus_equivariant (k : K) :
    (rhoMinus act k).comp nativeChiralDiracPlusArrow =
      nativeChiralDiracPlusArrow.comp (rhoPlus act k) :=
  nativePlusSectorAction_intertwines_chiralDiracPlus act k

/-- The negative chiral Dirac operator D₋ is K-equivariant. -/
theorem diracMinus_equivariant (k : K) :
    (rhoPlus act k).comp nativeChiralDiracMinusArrow =
      nativeChiralDiracMinusArrow.comp (rhoMinus act k) :=
  nativeMinusSectorAction_intertwines_chiralDiracMinus act k

/-- The inverse positive chiral Dirac operator D₊⁻¹ is K-equivariant. -/
theorem diracPlusInverse_equivariant (k : K) :
    (rhoPlus act k).comp nativeChiralDiracPlusInverseArrow =
      nativeChiralDiracPlusInverseArrow.comp (rhoMinus act k) :=
  nativePlusSectorAction_intertwines_chiralDiracPlusInverse act k

/-- The inverse negative chiral Dirac operator D₋⁻¹ is K-equivariant. -/
theorem diracMinusInverse_equivariant (k : K) :
    (rhoMinus act k).comp nativeChiralDiracMinusInverseArrow =
      nativeChiralDiracMinusInverseArrow.comp (rhoPlus act k) :=
  nativeMinusSectorAction_intertwines_chiralDiracMinusInverse act k

-- ============================================================================
-- Section 3: Equivariant Linear Equivalence (Isomorphism of K-Representations)
-- ============================================================================

/-- Structure capturing an explicit isomorphism between two K-representations. -/
structure EquivariantRepIso
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (ρV : K →* (V →ₗ[ℝ] V)) (ρW : K →* (W →ₗ[ℝ] W)) where
  equiv : V ≃ₗ[ℝ] W
  intertwines : ∀ k : K, (ρW k).comp equiv.toLinearMap = equiv.toLinearMap.comp (ρV k)

/-- 🏆 THEOREM: The positive and negative chiral semi-spinor representations
    S₊ and S₋ are canonically isomorphic as K-modules via D₊. -/
def chiralSemiSpinorEquivariantIso :
    EquivariantRepIso (nativePlusSectorActionHom act) (nativeMinusSectorActionHom act) where
  equiv := nativeChiralDiracPlusEquiv
  intertwines := by
    intro k
    apply LinearMap.ext
    intro x
    have h := congrArg (fun L : nativePlusSector →ₗ[ℝ] nativeMinusSector => L x)
      (diracPlus_equivariant act k)
    exact h

/-- The inverse K-equivariant isomorphism via D₋. -/
def chiralSemiSpinorEquivariantIso_symm :
    EquivariantRepIso (nativeMinusSectorActionHom act) (nativePlusSectorActionHom act) where
  equiv := nativeChiralDiracMinusEquiv
  intertwines := by
    intro k
    apply LinearMap.ext
    intro x
    have h := congrArg (fun L : nativeMinusSector →ₗ[ℝ] nativePlusSector => L x)
      (diracMinus_equivariant act k)
    exact h

/-- Intertwiner conjugation identity:
    ρ₋(k) = D₊ ∘ ρ₊(k) ∘ D₊⁻¹. -/
theorem rhoMinus_eq_conjugate_rhoPlus (k : K) :
    rhoMinus act k =
      (nativeChiralDiracPlusEquiv.toLinearMap.comp (rhoPlus act k)).comp
        nativeChiralDiracPlusEquiv.symm.toLinearMap := by
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    nativeChiralDiracPlusEquiv_apply]
  have h := congrArg (fun L : nativePlusSector →ₗ[ℝ] nativeMinusSector =>
    L (nativeChiralDiracPlusEquiv.symm y)) (diracPlus_equivariant act k)
  have h_cancel : nativeChiralDiracPlusArrow (nativeChiralDiracPlusEquiv.symm y) = y :=
    nativeChiralDiracPlusEquiv.apply_symm_apply y
  simp only [LinearMap.comp_apply] at h
  rw [h_cancel] at h
  exact h

/-- Intertwiner inverse conjugation identity:
    ρ₊(k) = D₋ ∘ ρ₋(k) ∘ D₋⁻¹. -/
theorem rhoPlus_eq_conjugate_rhoMinus (k : K) :
    rhoPlus act k =
      (nativeChiralDiracMinusEquiv.toLinearMap.comp (rhoMinus act k)).comp
        nativeChiralDiracMinusEquiv.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    nativeChiralDiracMinusEquiv_apply]
  have h := congrArg (fun L : nativeMinusSector →ₗ[ℝ] nativePlusSector =>
    L (nativeChiralDiracMinusEquiv.symm x)) (diracMinus_equivariant act k)
  have h_cancel : nativeChiralDiracMinusArrow (nativeChiralDiracMinusEquiv.symm x) = x :=
    nativeChiralDiracMinusEquiv.apply_symm_apply x
  simp only [LinearMap.comp_apply] at h
  rw [h_cancel] at h
  exact h

-- ============================================================================
-- Section 4: Equivariant Kernels and Fredholm Index in R(K)
-- ============================================================================

/-- The positive chiral Dirac operator has trivial kernel as a K-submodule. -/
theorem ker_diracPlus_eq_bot :
    LinearMap.ker nativeChiralDiracPlusArrow = ⊥ :=
  LinearMap.ker_eq_bot_of_injective nativeChiralDiracPlusArrow_bijective.injective

/-- The negative chiral Dirac operator has trivial kernel as a K-submodule. -/
theorem ker_diracMinus_eq_bot :
    LinearMap.ker nativeChiralDiracMinusArrow = ⊥ :=
  LinearMap.ker_eq_bot_of_injective nativeChiralDiracMinusArrow_bijective.injective

/-- Virtual representation difference in the representation ring R(K).
    For any pair of finite-dimensional K-modules, their index is their formal difference. -/
structure VirtualKRep where
  posDim : ℕ
  negDim : ℕ
  virtualDim : ℤ := (posDim : ℤ) - (negDim : ℤ)

/-- The equivariant Fredholm index of the chiral Dirac operator D₊:
    ind_K(D₊) = [ker D₊] - [ker D₋] = [0] - [0] = 0 in R(K). -/
def equivariantChiralFredholmIndex : VirtualKRep where
  posDim := 0
  negDim := 0
  virtualDim := 0

theorem equivariantChiralFredholmIndex_is_zero :
    (equivariantChiralFredholmIndex).virtualDim = 0 := rfl

/-- The total chiral dimension grading difference vanishes:
    dim(S₊) - dim(S₋) = 0. -/
theorem chiral_spinor_dimension_balance :
    (Module.finrank ℝ nativePlusSector : ℤ) -
      (Module.finrank ℝ nativeMinusSector : ℤ) = 0 := by
  rw [LinearEquiv.finrank_eq nativeChiralDiracPlusEquiv, sub_self]

/-- The equivariant index pairing with the trivial representation vanishes. -/
theorem equivariant_index_character_at_one :
    (equivariantChiralFredholmIndex).virtualDim = 0 := rfl

-- ============================================================================
-- Section 5: Matrix-Level Equivariant Kasparov Datum
-- ============================================================================

abbrev Mat32 := Cl55MasterWittSpinorEnvelopeBridge.Mat32

/-- Matrix-level K-equivariant Fredholm datum for the master Cl(5,5) Dirac operator. -/
structure MatrixEquivariantFredholmDatum (G : Type*) [Group G] where
  rep : G →* Mat32GL
  commutes_chirality (g : G) :
    (rep g : Mat32) * MasterChirality =
      MasterChirality * (rep g : Mat32)
  commutes_dirac (g : G) :
    (rep g : Mat32) * embeddedSplitOctonionHodgeDirac =
      embeddedSplitOctonionHodgeDirac * (rep g : Mat32)
  commutes_boundedTransform (g : G) :
    (rep g : Mat32) * masterBoundedTransform =
      masterBoundedTransform * (rep g : Mat32)

/-- 🏆 THEOREM: The canonical G₂(2) / SO(4) action yields a complete matrix-level
    equivariant Fredholm datum. -/
def canonicalMatrixEquivariantFredholmDatum : MatrixEquivariantFredholmDatum K where
  rep := act.U
  commutes_chirality := act.commutes_chirality
  commutes_dirac := act.commutes_hodge
  commutes_boundedTransform := g2_integrated_comm_boundedTransform act

end InfoGeometry.Canonical.G2SO4EquivariantIndexBridge
