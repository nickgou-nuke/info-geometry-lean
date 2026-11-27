/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.RieffelVanDaeleBoundedTomita
import InfoGeometry.Canonical.FilteredGNSTomitaFriedrichsResolvent
import InfoGeometry.Modular.TwistedCrossedProductAlgebra
import InfoGeometry.Modular.PowersModularSpectrum
import InfoGeometry.Modular.ComplexRelativeModularRN
import InfoGeometry.Analysis.LpSpectralMultiplicationModel
import InfoGeometry.Modular.TomitaRegularCommutantAndKMSBridge
import InfoGeometry.Canonical.FiniteSeedGibbsTomitaClosability
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# End-to-End Test Suite for the Tomita Frontiers Roadmap (`TT-F1`–`TT-F5`)

Comprehensive kernel-checked test suite covering Features `F1`–`F14` across
Tiers 1–4 plus an in-file `CollectAxioms` self-audit:

- **Tier 1 (`t1_f*`, 70 tests):** Isolated feature coverage (`5` checks per
  feature `F1`–`F14`).
- **Tier 2 (`t2_f*`, 70 tests):** Boundary, corner, negative, and adversarial
  counterexample tests (`5` checks per feature `F1`–`F14`), including:
  - `n = 2` single-operator commutant counterexample `{L_A}' ≠ {R_B}`,
  - explicit `2×2` noncommuting complex densities `ρ_ψ * ρ_φ ≠ ρ_φ * ρ_ψ`
    and non-scalar Connes cocycle `u_{π/2}`,
  - Powers spectrum separation `0 ∉ powersPointSpec lam` vs
    `0 ∈ closure (powersPointSpec lam) = insert 0 (powersPointSpec lam)`
    and finite-stage non-Type-III boundaries,
  - real `FiniteMatrixTomitaPolar` vs complex `M_n(ℂ)` separation and
    `TT-F1A` vs `TT-F1B` route separation.
- **Tier 3 (`t3_*`, 15 tests):** Pairwise cross-feature bridges across
  `TT-F1A`, `TT-F1B`, `TT-F2`, `TT-F3a`, `TT-F3b`, `TT-F4`, and `TT-F5`.
- **Tier 4 (`S1_Scenario`–`S7_Scenario`, 7 end-to-end scenarios):** Full
  multi-feature operator-algebraic workflows.
- **Tier 5 (`Tier5_Adversarial`):** Adversarial concrete non-orthogonal,
  off-diagonal `CStarMatrixStage` / `cfc`, `covariantLift_unique` & `dualActionHom ≠ 1`,
  `UHFStage` eigenvector & `1`-boundary, `u_π ≠ u_{π/2}^2` & 3-density RN,
  infinite-measure `L²(ℝ, volume)`, and negative `¬(A†(K) ⊆ K)` / non-diagonal KMS
  hardening across `M1`–`M6`.
- **Self-Audit (`run_cmd do`):** Verifies every local declaration uses only
  `[propext, Classical.choice, Quot.sound]` with zero `unsafe`/`partial`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped InnerProductSpace BigOperators ENNReal
open Matrix Function
open InfoGeometry.Canonical.RealTomitaStandardSubspace
open InfoGeometry.Canonical.TomitaTakesakiRealStandardForm
open InfoGeometry.Modular
open InfoGeometry.Modular.RieffelVanDaeleBoundedTomita
open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaCore
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator
open CStarStateColimit.Native.FilteredGNSTomitaModularForm
open CStarStateColimit.Native.FilteredGNSTomitaModularHilbertCompletion
open CStarStateColimit.Native.FilteredGNSTomitaFriedrichsResolvent
open InfoGeometry.Modular.TwistedCrossedProductAlgebra
open InfoGeometry.Modular.TwistedCrossedProductAlgebra.TwistedCrossedProduct
open InfoGeometry.Algebra.UHFColimitCStarCompletion
open InfoGeometry.Canonical.JaynesianTomitaBisognanoColimit
open InfoGeometry.Modular.PowersModularSpectrum
open InfoGeometry.Modular.ComplexMatrixTomitaDuality
open InfoGeometry.Modular.TomitaCommutantDuality
open InfoGeometry.Modular.TomitaChiralJ
open InfoGeometry.Modular.ComplexRelativeModularRN
open InfoGeometry.Analysis.LpSpectralMultiplicationModel
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.L2Multiplier
open InfoGeometry.Modular.TomitaRegularCommutantAndKMSBridge
open InfoGeometry.Canonical
open MeasureTheory Filter Topology

namespace InfoGeometry.Tests.TomitaFrontiersRoadmap

/-! ## OpenGauss T16 Noncommutativity Witnesses -/

theorem t16_mat2_complex_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  InfoGeometry.Modular.ComplexMatrixTomitaDuality.mat2_complex_noncomm_witness

/-! ## Tier 1: Isolated Feature Coverage (`F1`–`F14`, 5 Checks Each = 70) -/

section Tier1_F1_F3

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem t1_f1_01 (r : ℝ) (x y : H) :
    IMapCLM H (r • x + y) = r • IMapCLM H x + IMapCLM H y ∧
      ‖IMapCLM H x‖ = ‖x‖ :=
  ⟨by rw [map_add, map_smul], IMapCLM_norm x⟩

theorem t1_f1_02 :
    Isometry (IMapCLM H) ∧ ∀ x : H, ‖IMap H x‖ = ‖x‖ :=
  ⟨IMapCLM_isometry, IMap_norm⟩

theorem t1_f1_03 [CompleteSpace H] :
    (IMapCLM H).comp (IMapCLM H) = -ContinuousLinearMap.id ℝ H ∧
      letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
      (IMapCLM H).adjoint = -(IMapCLM H) :=
  ⟨IMapCLM_sq, IMapCLM_adjoint⟩

theorem t1_f1_04 (K : Submodule ℝ H) (hK : IsClosed (K : Set H)) [CompleteSpace K] :
    IsClosed (ImaginarySubmodule (H := H) K : Set H) ∧
      CompleteSpace (ImaginarySubmodule (H := H) K) :=
  ⟨isClosed_imaginarySubmodule hK, completeSpace_imaginarySubmodule K⟩

theorem t1_f1_05 (x y : H) :
    (⟪IMap H x, IMap H y⟫_ℂ).re = (⟪x, y⟫_ℂ).re ∧
      (⟪IMap H x, y⟫_ℂ).re = -(⟪x, IMap H y⟫_ℂ).re :=
  ⟨IMap_inner_re x y, IMap_inner_left_re x y⟩

theorem t1_f2_01 (K : Submodule ℝ H) [CompleteSpace K] (x : H) :
    projK (H := H) K x ∈ K ∧ (projK (H := H) K x = x ↔ x ∈ K) :=
  ⟨projK_apply_mem K x, projK_eq_self_iff K x⟩

theorem t1_f2_02 [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K] :
    (projK (H := H) K).comp (projK (H := H) K) = projK (H := H) K ∧
      letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
      IsSelfAdjoint (projK (H := H) K) :=
  ⟨projK_comp_self K, projK_isSelfAdjoint K⟩

theorem t1_f2_03 [CompleteSpace H] (K : Submodule ℝ H)
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    projIK (H := H) K x ∈ ImaginarySubmodule (H := H) K ∧
      (projIK (H := H) K).comp (projIK (H := H) K) = projIK (H := H) K ∧
      letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
      IsSelfAdjoint (projIK (H := H) K) :=
  ⟨projIK_apply_mem K x, projIK_comp_self K, projIK_isSelfAdjoint K⟩

theorem t1_f2_04 (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    (0 ≤ (⟪x, projK (H := H) K x⟫_ℂ).re ∧
        (⟪x, projK (H := H) K x⟫_ℂ).re ≤ ‖x‖ ^ 2) ∧
      (0 ≤ (⟪x, projIK (H := H) K x⟫_ℂ).re ∧
        (⟪x, projIK (H := H) K x⟫_ℂ).re ≤ ‖x‖ ^ 2) := by
  have hk1 : (⟪x, projK (H := H) K x⟫_ℂ).re = ‖projK (H := H) K x‖ ^ 2 :=
    projK_inner_re_eq K x
  have hk2 : (⟪x, projIK (H := H) K x⟫_ℂ).re = ‖projIK (H := H) K x‖ ^ 2 :=
    projIK_inner_re_eq K x
  have hb1 : ‖projK (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_projK_apply_le K x) 2
  have hb2 : ‖projIK (H := H) K x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_projIK_apply_le K x) 2
  exact ⟨⟨hk1 ▸ sq_nonneg _, hk1 ▸ hb1⟩, ⟨hk2 ▸ sq_nonneg _, hk2 ▸ hb2⟩⟩

theorem t1_f2_05 (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (IMapCLM H).comp (projK (H := H) K) = (projIK (H := H) K).comp (IMapCLM H) ∧
      (IMapCLM H).comp (projIK (H := H) K) = (projK (H := H) K).comp (IMapCLM H) :=
  ⟨IMapCLM_comp_projK K, IMapCLM_comp_projIK K⟩

theorem t1_f3_01 [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    rvdR (H := H) K = projK (H := H) K + projIK (H := H) K ∧
      letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
      IsSelfAdjoint (rvdR (H := H) K) ∧ (rvdR (H := H) K).IsPositive :=
  ⟨rfl, rvdR_isSelfAdjoint K, rvdR_isPositive K⟩

theorem t1_f3_02 (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    0 ≤ (⟪x, rvdR (H := H) K x⟫_ℂ).re ∧
      (⟪x, rvdR (H := H) K x⟫_ℂ).re ≤ 2 * ‖x‖ ^ 2 ∧
      ‖rvdR (H := H) K‖ ≤ 2 :=
  ⟨(rvdR_inner_re_bounds K x).1, (rvdR_inner_re_bounds K x).2, rvdR_norm_le K⟩

theorem t1_f3_03 [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    (IMapCLM H).comp (rvdT (H := H) K) = -((rvdT (H := H) K).comp (IMapCLM H)) ∧
      ‖rvdT (H := H) K‖ ≤ 1 ∧
      letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
      IsSelfAdjoint (rvdT (H := H) K) :=
  ⟨IMapCLM_comp_rvdT K, rvdT_norm_le K, rvdT_isSelfAdjoint K⟩

theorem t1_f3_04 (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    rvdT (H := H) K * rvdT (H := H) K =
        rvdR (H := H) K * ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) ∧
      (1 - rvdR (H := H) K) * (1 - rvdR (H := H) K) + rvdT (H := H) K * rvdT (H := H) K = 1 :=
  ⟨rvdT_sq_eq K, one_sub_rvdR_sq_add_rvdT_sq K⟩

theorem t1_f3_05 [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (J : H ≃ₗᵢ[ℝ] H)
    (hJ_sq : ∀ x : H, J (J x) = x)
    (hJ_anti : ∀ x : H, J ((Complex.I : ℂ) • x) = -(Complex.I : ℂ) • J x)
    (hJK : K.map (J.toLinearEquiv : H →ₗ[ℝ] H) = symplCompSubmodule (H := H) K) :
    (IMapCLM H).comp (rvdT (H := H) K * rvdT (H := H) K) =
        (rvdT (H := H) K * rvdT (H := H) K).comp (IMapCLM H) ∧
      (J.toContinuousLinearEquiv : H →L[ℝ] H) * rvdR (H := H) K *
          (J.toContinuousLinearEquiv : H →L[ℝ] H) =
        (2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K ∧
      (J.toContinuousLinearEquiv : H →L[ℝ] H) * rvdT (H := H) K *
          (J.toContinuousLinearEquiv : H →L[ℝ] H) =
        rvdT (H := H) K :=
  ⟨IMapCLM_commutes_rvdT_sq K,
    j_conj_rvdR K J hJ_sq hJ_anti hJK,
    j_conj_rvdT K J hJ_sq hJ_anti hJK⟩

end Tier1_F1_F3

section Tier1_F4_F5

universe u

theorem t1_f4_01 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) :
    Set.range (tomitaFormResolventCLM ω hclos) ⊆
      (closedTomitaDomain ω : Set ω.functional.GNS) :=
  tomitaFormResolvent_range_subset_domain ω hclos

theorem t1_f4_02 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) :
    DenseRange (tomitaFormResolventCLM ω hclos) :=
  tomitaFormResolvent_denseRange ω hclos

theorem t1_f4_03 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) :
    Dense (closedTomitaDomain ω : Set ω.functional.GNS) :=
  dense_closedTomitaDomain ω hclos

theorem t1_f4_04 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) (ξ : ω.functional.GNS) :
    ‖tomitaSCompResolventRLM ω hclos‖ ≤ 1 ∧
      ‖tomitaSCompResolventRLM ω hclos ξ‖ ≤ ‖ξ‖ :=
  ⟨tomitaSCompResolventRLM_norm_le ω hclos,
    tomitaSCompResolventRLM_norm_apply_le ω hclos ξ⟩

theorem t1_f4_05 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) (ξ : ω.functional.GNS) :
    IsSelfAdjoint (tomitaFormComplementaryResolventCLM ω hclos) ∧
      0 ≤ (inner ℂ ξ (tomitaFormComplementaryResolventCLM ω hclos ξ)).re ∧
      (inner ℂ ξ (tomitaFormComplementaryResolventCLM ω hclos ξ)).re ≤ ‖ξ‖ ^ 2 ∧
      ‖tomitaFormComplementaryResolventCLM ω hclos‖ ≤ 1 :=
  ⟨tomitaFormComplementaryResolventCLM_isSelfAdjoint ω hclos,
    (tomitaFormComplementaryResolventCLM_inner_bounds ω hclos ξ).1,
    (tomitaFormComplementaryResolventCLM_inner_bounds ω hclos ξ).2,
    tomitaFormComplementaryResolventCLM_opNorm_le ω hclos⟩

theorem t1_f5_01 {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    (x y : TomitaGraphDom (ω.state i) (hclos i)) :
    inner ℂ x y =
      inner ℂ (x.val : (ω.state i).functional.GNS) (y.val : (ω.state i).functional.GNS) +
        closedTomitaModularForm Stage sys ω hclos i x.val y.val :=
  tomitaGraphInner_eq_inner_add_modularForm Stage sys ω hclos i x y

theorem t1_f5_02 {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    (ξ : (ω.state i).functional.GNS) (y : closedTomitaDomain (ω.state i)) :
    inner ℂ (tomitaFormResolventCLM (ω.state i) (hclos i) ξ)
        (y : (ω.state i).functional.GNS) +
      closedTomitaModularForm Stage sys ω hclos i
        (tomitaFormResolventDomCLM (ω.state i) (hclos i) ξ).val y =
      inner ℂ ξ (y : (ω.state i).functional.GNS) :=
  tomitaFormResolvent_modularForm_variational Stage sys ω hclos i ξ y

theorem t1_f5_03 {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    ‖tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i‖ ≤ 1 ∧
      ‖tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i x‖ ^ 2 =
        (closedTomitaModularForm Stage sys ω hclos i x.val x.val).re :=
  ⟨tomitaGraphDom_to_modularHilbertCompletion_norm_le Stage sys ω hclos i,
    tomitaGraphDom_to_modularHilbertCompletion_apply_norm_sq Stage sys ω hclos i x⟩

theorem t1_f5_04 {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    (ξ : (ω.state i).functional.GNS) :
    ‖gns_to_modularHilbertCompletion_via_resolvent Stage sys ω hclos i‖ ≤ 1 ∧
      ‖gns_to_modularHilbertCompletion_via_resolvent Stage sys ω hclos i ξ‖ ≤ ‖ξ‖ :=
  ⟨gns_to_modularHilbertCompletion_via_resolvent_norm_le Stage sys ω hclos i,
    gns_to_modularHilbertCompletion_via_resolvent_apply_norm_le Stage sys ω hclos i ξ⟩

theorem t1_f5_05 {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) {i j : I} (hij : i ≤ j)
    (x : TomitaGraphDom (ω.state i) (hclos i)) (ξ : (ω.state i).functional.GNS) :
    ‖filteredTomitaGraphDomMap Stage sys ω hclos hij x‖ = ‖x‖ ∧
      graphDomInclCLM (ω.state j) (hclos j)
          (filteredTomitaGraphDomMap Stage sys ω hclos hij x) =
        filteredGNSLinearIsometry Stage sys ω hij
          (graphDomInclCLM (ω.state i) (hclos i) x) ∧
      (inner ℂ ξ (tomitaFormResolventCLM (ω.state i) (hclos i) ξ)).re ≤
        (inner ℂ (filteredGNSLinearIsometry Stage sys ω hij ξ)
          (tomitaFormResolventCLM (ω.state j) (hclos j)
            (filteredGNSLinearIsometry Stage sys ω hij ξ))).re :=
  ⟨(filteredTomitaGraphDomMap Stage sys ω hclos hij).norm_map x,
    graphDomInclCLM_filteredTomitaGraphDomMap Stage sys ω hclos hij x,
    filteredTomitaFormResolvent_monotone Stage sys ω hclos hij ξ⟩

end Tier1_F4_F5

section Tier1_F6_F7

variable {G : Type*} [Group G]
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {θ : G →* (A ≃⋆ₐ[ℂ] A)}

theorem t1_f6_01 (f g h : TwistedCrossedProduct G A θ) (t : G) :
    (f * g) * h = f * (g * h) ∧
      (f * (g + h)) = f * g + f * h ∧
      (f * g).toFinsupp t =
        ∑ s ∈ f.toFinsupp.support, f.toFinsupp s * θ s (g.toFinsupp (s⁻¹ * t)) :=
  ⟨mul_assoc f g h, mul_add f g h, coeff_mul f g t⟩

theorem t1_f6_02 (f g : TwistedCrossedProduct G A θ) (t : G) :
    star (f * g) = star g * star f ∧
      star (star f) = f ∧
      (star f).toFinsupp t = θ t (star (f.toFinsupp t⁻¹)) :=
  ⟨star_mul f g, star_star f, coeff_star f t⟩

theorem t1_f6_03 (c : ℂ) (f g : TwistedCrossedProduct G A θ) :
    star (c • f) = star c • star f ∧
      (c • f) * g = c • (f * g) ∧
      f * (c • g) = c • (f * g) :=
  ⟨star_smul c f, smul_mul_assoc c f g, mul_smul_comm c f g⟩

theorem t1_f6_04 (a b : A) (c : ℂ) :
    embedAlg (θ := θ) 1 = 1 ∧
      embedAlg (θ := θ) (a * b) = embedAlg a * embedAlg b ∧
      embedAlg (θ := θ) (c • a) = c • embedAlg a ∧
      embedAlg (θ := θ) (star a) = star (embedAlg a) :=
  ⟨map_one _, map_mul _ a b, map_smul _ c a, map_star _ a⟩

theorem t1_f6_05 (g h : G) :
    embedGroup (θ := θ) (g * h) = embedGroup g * embedGroup h ∧
      star (embedGroup (θ := θ) g) = embedGroup g⁻¹ ∧
      embedGroup (θ := θ) g * star (embedGroup g) = 1 ∧
      star (embedGroup (θ := θ) g) * embedGroup g = 1 :=
  ⟨embedGroup_mul g h, embedGroup_star g,
    embedGroup_unitary_right g, embedGroup_unitary_left g⟩

theorem t1_f7_01 (g : G) (a : A) :
    embedGroup (θ := θ) g * embedAlg a * star (embedGroup g) = embedAlg (θ g a) :=
  covariant_relation g a

theorem t1_f7_02 {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a))
    (x y : TwistedCrossedProduct G A θ) :
    covariantLift (θ := θ) π U hcov (x * y) =
      covariantLift π U hcov x * covariantLift π U hcov y ∧
      covariantLift (θ := θ) π U hcov (star x) = star (covariantLift π U hcov x) :=
  ⟨map_mul _ x y, map_star _ x⟩

theorem t1_f7_03 {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a))
    (a : A) (g : G) :
    covariantLift (θ := θ) π U hcov (embedAlg a) = π a ∧
      covariantLift (θ := θ) π U hcov (embedGroup g) = (U g : B) :=
  ⟨covariantLift_embedAlg π U hcov a, covariantLift_embedGroup π U hcov g⟩

theorem t1_f7_04 {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a))
    (Φ : TwistedCrossedProduct G A θ →⋆ₐ[ℂ] B)
    (hA : ∀ a : A, Φ (embedAlg a) = π a)
    (hG : ∀ g : G, Φ (embedGroup g) = (U g : B)) :
    Φ = covariantLift π U hcov :=
  covariantLift_unique π U hcov Φ hA hG

theorem t1_f7_05 (χ₁ χ₂ : G →* unitary ℂ) (a : A) (g : G) :
    dualAction (θ := θ) χ₁ (embedAlg a) = embedAlg a ∧
      dualAction (θ := θ) χ₁ (embedGroup g) = (χ₁ g : ℂ) • embedGroup g ∧
      (dualAction (G := G) (A := A) (θ := θ) χ₁).comp (dualAction χ₂) =
        dualAction (χ₁ * χ₂) :=
  ⟨dualAction_embedAlg χ₁ a, dualAction_embedGroup χ₁ g, dualAction_comp χ₁ χ₂⟩

end Tier1_F6_F7

section Tier1_F8

theorem t1_f8_01 (lam : ℝ) (k : ℤ) :
    (1 : ℝ) ∈ powersPointSpec lam ∧ lam ^ k ∈ powersPointSpec lam :=
  ⟨⟨0, zpow_zero lam⟩, zpow_mem_powersPointSpec lam k⟩

theorem t1_f8_02 {lam : ℝ} (hlam : 0 < lam) (m : ℤ) :
    ∃ E : UHFStage m.natAbs,
      E ≠ 0 ∧ powersModularOp lam m.natAbs E = ((lam ^ m : ℝ) : ℂ) • E :=
  powersModularOp_point_spectrum hlam m

theorem t1_f8_03 {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    StrictAnti (fun k : ℤ => lam ^ k) ∧
      Function.Injective (fun k : ℤ => lam ^ k) :=
  ⟨powersPointSpec_strictAnti hlam0 hlam1, powersPointSpec_injective hlam0 hlam1⟩

theorem t1_f8_04 {lam : ℝ} (hlam : 0 < lam) :
    (0 : ℝ) ∉ powersPointSpec lam :=
  zero_notMem_powersPointSpec hlam

theorem t1_f8_05 {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    closure (powersPointSpec lam) = insert (0 : ℝ) (powersPointSpec lam) :=
  closure_powersPointSpec_eq_insert_zero hlam0 hlam1

end Tier1_F8

section Tier1_F9_F10

theorem t1_f9_01 {n : ℕ} (F_ψ F_φ : PositiveComplexDensityFactor n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_ψ F_φ (A * F_φ.r) = Aᴴ * F_ψ.r ∧
      relTomitaOp F_ψ F_φ F_φ.r = F_ψ.r :=
  ⟨relTomitaOp_on_cyclic F_ψ F_φ A, relTomitaOp_cyclic F_ψ F_φ⟩

theorem t1_f9_02 {n : ℕ} (F_ψ F_φ : PositiveComplexDensityFactor n)
    (c : ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    relModularOp F_ψ F_φ (c • X + Y) =
      c • relModularOp F_ψ F_φ X + relModularOp F_ψ F_φ Y := by
  change relModularOpLinear F_ψ F_φ (c • X + Y) =
    c • relModularOpLinear F_ψ F_φ X + relModularOpLinear F_ψ F_φ Y
  rw [map_add, map_smul]

theorem t1_f9_03 {n : ℕ} (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relModularSqrt F_ψ F_φ (relModularSqrt F_ψ F_φ X) = relModularOp F_ψ F_φ X :=
  relModularSqrt_comp_self F_ψ F_φ X

theorem t1_f9_04 {n : ℕ} (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_ψ F_φ X = matrixJ n (relModularSqrt F_ψ F_φ X) :=
  relTomitaOp_polar F_ψ F_φ X

theorem t1_f9_05 {n : ℕ} (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaAdjOp F_ψ F_φ (relTomitaOp F_ψ F_φ X) = relModularOp F_ψ F_φ X ∧
      hsInner n (relTomitaOp F_ψ F_φ X) (relTomitaOp F_ψ F_φ Y) =
        hsInner n Y (relModularOp F_ψ F_φ X) ∧
      state F_φ (X * relModularOp F_ψ F_φ Y) = state F_ψ (Y * X) :=
  ⟨relModularOp_eq_adj_comp_relTomita F_ψ F_φ X,
    hsInner_relTomitaOp_quadratic F_ψ F_φ X Y,
    relModularOp_kms_identity F_ψ F_φ X Y⟩

theorem t1_f10_01 {n : ℕ} (E_ψ E_φ : ExpDensityFactor n) (t : ℝ) :
    relConnesCocycle E_ψ E_φ t * (relConnesCocycle E_ψ E_φ t)ᴴ = 1 ∧
      (relConnesCocycle E_ψ E_φ t)ᴴ * relConnesCocycle E_ψ E_φ t = 1 :=
  ⟨relConnesCocycle_unitary_left E_ψ E_φ t, relConnesCocycle_unitary_right E_ψ E_φ t⟩

theorem t1_f10_02 {n : ℕ} (E_ψ E_φ : ExpDensityFactor n) :
    relConnesCocycle E_ψ E_φ 0 = 1 :=
  relConnesCocycle_zero E_ψ E_φ

theorem t1_f10_03 {n : ℕ} (E_χ E_ψ E_φ : ExpDensityFactor n) (s t : ℝ) :
    relConnesCocycle E_ψ E_φ (s + t) =
        relConnesCocycle E_ψ E_φ s * E_φ.modularFlow s (relConnesCocycle E_ψ E_φ t) ∧
      relConnesCocycle E_χ E_φ t =
        relConnesCocycle E_χ E_ψ t * relConnesCocycle E_ψ E_φ t :=
  ⟨relConnesCocycle_cocycle_id E_ψ E_φ s t, relConnesCocycle_chain_rule E_χ E_ψ E_φ t⟩

theorem t1_f10_04 {n : ℕ} (E_ψ E_φ : ExpDensityFactor n) (t : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    E_ψ.modularFlow t A =
      relConnesCocycle E_ψ E_φ t * E_φ.modularFlow t A * (relConnesCocycle E_ψ E_φ t)ᴴ :=
  relConnesCocycle_intertwines E_ψ E_φ t A

theorem t1_f10_05 :
    witnessRhoPsi * witnessRhoPhi ≠ witnessRhoPhi * witnessRhoPsi ∧
      witnessRhoPsi * witnessRhoPhi - witnessRhoPhi * witnessRhoPsi ≠ 0 :=
  ⟨witnessRhoPsi_mul_witnessRhoPhi_ne, witnessRhoPsi_commutator_ne_zero⟩

end Tier1_F9_F10

section Tier1_F11_F12

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem t1_f11_01 (f : α → ℂ) (hf : AEStronglyMeasurable f μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) (ψ : L2c α μ) :
    ⇑(lpMulOpOfBound (α := α) (μ := μ) f hf C hC ψ) =ᵐ[μ] fun x => f x * ψ x :=
  lpMulOpOfBound_apply_ae f hf C hC ψ

theorem t1_f11_02 (h1 : AEStronglyMeasurable (1 : α → ℂ) μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖(1 : α → ℂ) x‖ ≤ C) :
    lpMulOpOfBound (α := α) (μ := μ) (1 : α → ℂ) h1 C hC = 1 :=
  lpMulOpOfBound_one h1 C hC

theorem t1_f11_03 (f g : α → ℂ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (C₁ C₂ : ℝ) (hC₁ : ∀ᵐ x ∂μ, ‖f x‖ ≤ C₁) (hC₂ : ∀ᵐ x ∂μ, ‖g x‖ ≤ C₂)
    (hfg : AEStronglyMeasurable (f * g) μ) (C₁₂ : ℝ)
    (hC₁₂ : ∀ᵐ x ∂μ, ‖(f * g) x‖ ≤ C₁₂) :
    lpMulOpOfBound (α := α) (μ := μ) (f * g) hfg C₁₂ hC₁₂ =
      lpMulOpOfBound f hf C₁ hC₁ ∘L lpMulOpOfBound g hg C₂ hC₂ :=
  lpMulOpOfBound_mul f g hf hg C₁ C₂ hC₁ hC₂ hfg C₁₂ hC₁₂

theorem t1_f11_04 (f : α → ℂ)
    (hf : AEStronglyMeasurable f μ) (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)
    (hf_star : AEStronglyMeasurable (star ∘ f) μ) (C_star : ℝ)
    (hC_star : ∀ᵐ x ∂μ, ‖(star ∘ f) x‖ ≤ C_star) :
    (lpMulOpOfBound (α := α) (μ := μ) f hf C hC).adjoint =
      lpMulOpOfBound (star ∘ f) hf_star C_star hC_star :=
  lpMulOpOfBound_adjoint f hf C hC hf_star C_star hC_star

theorem t1_f11_05 (f : α → ℂ) (hf : AEStronglyMeasurable f μ)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ‖lpMulOpOfBound (α := α) (μ := μ) f hf C hC‖ ≤ C :=
  norm_lpMulOpOfBound_le f hf hC_nonneg hC

theorem t1_f12_01 (S : Set α) (hS : MeasurableSet S) :
    IsSelfAdjoint (pvmProj (α := α) (μ := μ) S hS) :=
  pvmProj_isSelfAdjoint S hS

theorem t1_f12_02 (S : Set α) (hS : MeasurableSet S) :
    IsIdempotentElem (pvmProj (α := α) (μ := μ) S hS) ∧
      IsStarProjection (pvmProj (α := α) (μ := μ) S hS) :=
  ⟨pvmProj_isIdempotent S hS, pvmProj_isStarProjection S hS⟩

theorem t1_f12_03 {S T : Set α} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hdisj : Disjoint S T) :
    pvmProj (α := α) (μ := μ) S hS ∘L pvmProj (α := α) (μ := μ) T hT = 0 :=
  pvmProj_disjoint_comp hS hT hdisj

theorem t1_f12_04 (S : ℕ → Set α) (hS : ∀ n, MeasurableSet (S n))
    (hdisj : Pairwise (Disjoint on S)) (ψ : L2c α μ) :
    Tendsto
      (fun N => ∑ n ∈ Finset.range N, pvmProj (α := α) (μ := μ) (S n) (hS n) ψ)
      atTop
      (𝓝 (pvmProj (α := α) (μ := μ) (⋃ n, S n) (MeasurableSet.iUnion hS) ψ)) :=
  pvmProj_countable_add S hS hdisj ψ

theorem t1_f12_05 (h : α → ℝ) (hh : Measurable h) (s t : ℝ) (ψ : L2c α μ) :
    stoneMulGroup (α := α) (μ := μ) h hh 0 = 1 ∧
      stoneMulGroup (α := α) (μ := μ) h hh (s + t) =
        stoneMulGroup h hh s ∘L stoneMulGroup h hh t ∧
      stoneMulGroup (α := α) (μ := μ) h hh t ∈ unitary (L2c α μ →L[ℂ] L2c α μ) ∧
      Isometry (stoneMulGroup (α := α) (μ := μ) h hh t) ∧
      Continuous (fun r : ℝ => stoneMulGroup (α := α) (μ := μ) h hh r ψ) :=
  ⟨stoneMulGroup_zero h hh, stoneMulGroup_add h hh s t, stoneMulGroup_unitary h hh t,
    stoneMulGroup_isometry h hh t, stoneMulGroup_continuous h hh ψ⟩

end Tier1_F11_F12

section Tier1_F13_F14

theorem t1_f13_01 (n : ℕ) (T : Module.End ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.leftRegSet n =
        ComplexMatrixTomitaDuality.leftRegSet n ∧
      InfoGeometry.Canonical.ComplexMatrixTomitaCommutantDuality.rightRegSet n =
        ComplexMatrixTomitaDuality.rightRegSet n ∧
      ((T : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) ∈
          commutant (ComplexMatrixTomitaDuality.leftRegSet n) ↔
        ∃ B : Matrix (Fin n) (Fin n) ℂ,
          T = InfoGeometry.Algebra.AssociativeRegularCommutant.rightRegular (R := ℂ) B) :=
  ⟨compat_leftRegSet n, compat_rightRegSet n,
    linearMap_mem_commutant_leftRegSet_iff_rightRegular n T⟩

theorem t1_f13_02 (n : ℕ) :
    commutant (ComplexMatrixTomitaDuality.leftRegSet n) =
        ComplexMatrixTomitaDuality.rightRegSet n ∧
      commutant (ComplexMatrixTomitaDuality.rightRegSet n) =
        ComplexMatrixTomitaDuality.leftRegSet n ∧
      commutant (ComplexMatrixTomitaDuality.leftRegSet n) =
        JConjugateSet (ComplexMatrixTomitaDuality.matrixJ n)
          (ComplexMatrixTomitaDuality.leftRegSet n) :=
  ⟨fullLeftReg_commutant_eq_rightReg n,
    fullRightReg_commutant_eq_leftReg n,
    fullLeftReg_commutant_eq_JConjugate n⟩

theorem t1_f13_03 (n : ℕ) :
    commutant (commutant (ComplexMatrixTomitaDuality.leftRegSet n)) =
      ComplexMatrixTomitaDuality.leftRegSet n :=
  fullLeftReg_bicommutant_eq_self n

theorem t1_f13_04 (X Y : CuntzMatrixTowerInstantiation.MatrixStage 1) :
    InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS.seedFunctional
        diagPauliZStage1 diagPauliZStage1_isHermitian 1 0
        (InfoGeometry.Canonical.FiniteSeedRepresentedRealTime.seedStageHom
          diagPauliZStage1 diagPauliZStage1_isHermitian 1
          (X * ComplexMatrixTomitaDuality.modularOp
            (gibbsDensityFactor diagPauliZStage1 diagPauliZStage1_isHermitian 1) Y)) =
      InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS.seedFunctional
        diagPauliZStage1 diagPauliZStage1_isHermitian 1 0
        (InfoGeometry.Canonical.FiniteSeedRepresentedRealTime.seedStageHom
          diagPauliZStage1 diagPauliZStage1_isHermitian 1 (Y * X)) ∧
      stage1DiagTomitaAndKMSBridge.kmsState.state 1 = 1 :=
  ⟨seedFunctional_stage_modularOp_kms diagPauliZStage1 diagPauliZStage1_isHermitian 1 0 X Y,
    stage1DiagTomitaAndKMSBridge.kmsState.state_one⟩

theorem t1_f13_05 :
    commutant {ComplexMatrixTomitaDuality.leftMul 2 witnessE01} ≠
      ComplexMatrixTomitaDuality.rightRegSet 2 :=
  single_leftMul_commutant_ne_rightRegSet

theorem t1_f14_01 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    (A : H →L[ℂ] H) (hAK : ∀ x ∈ K, A x ∈ K) (hAdjK : ∀ x ∈ K, A.adjoint x ∈ K) :
    (A.restrictScalars ℝ).comp (projK (H := H) K) =
      (projK (H := H) K).comp (A.restrictScalars ℝ) :=
  commutes_projK_of_preserves_subspace K A hAK hAdjK

theorem t1_f14_02 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : Submodule ℝ H)
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (A : H →L[ℂ] H) (hAK : ∀ x ∈ K, A x ∈ K) (hAdjK : ∀ x ∈ K, A.adjoint x ∈ K) :
    (∀ x ∈ ImaginarySubmodule (H := H) K, A x ∈ ImaginarySubmodule (H := H) K) ∧
      (A.restrictScalars ℝ).comp (projIK (H := H) K) =
        (projIK (H := H) K).comp (A.restrictScalars ℝ) :=
  ⟨preserves_imaginarySubmodule_of_clm A hAK,
    commutes_projIK_of_preserves_subspace K A hAK hAdjK⟩

theorem t1_f14_03 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (A : H →L[ℂ] H) (hAK : ∀ x ∈ K, A x ∈ K) (hAdjK : ∀ x ∈ K, A.adjoint x ∈ K) :
    (A.restrictScalars ℝ).comp (rvdR (H := H) K) =
        (rvdR (H := H) K).comp (A.restrictScalars ℝ) ∧
      A.comp (rvdRComplexCLM (H := H) K) = (rvdRComplexCLM (H := H) K).comp A :=
  ⟨(bounded_commutant_criterion_of_preserves_subspace K A hAK hAdjK).2.2.1,
    commutes_rvdRComplexCLM_of_preserves_subspace K A hAK hAdjK⟩

theorem t1_f14_04 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (A : H →L[ℂ] H) :
    ((A.restrictScalars ℝ).comp (rvdR (H := H) K) =
          (rvdR (H := H) K).comp (A.restrictScalars ℝ) ∧
        (A.restrictScalars ℝ).comp (rvdT (H := H) K) =
          (rvdT (H := H) K).comp (A.restrictScalars ℝ)) ↔
      ((∀ x ∈ K, A x ∈ K) ∧ (∀ x ∈ K, A.adjoint x ∈ K)) :=
  commutes_rvdR_and_rvdT_iff_preserves_subspace K A

theorem t1_f14_05 {n : ℕ} (F : ComplexMatrixTomitaDuality.PositiveComplexDensityFactor n)
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * F.rInv = F.rInv * U) :
    ((conjByCLM U).restrictScalars ℝ).comp
          (rvdR (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)) =
        (rvdR (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)).comp
          ((conjByCLM U).restrictScalars ℝ) ∧
      ((conjByCLM U).restrictScalars ℝ).comp
          (rvdT (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)) =
        (rvdT (H := EuclideanSpace ℂ (Fin n × Fin n)) (tomitaRealSubspace F)).comp
          ((conjByCLM U).restrictScalars ℝ) :=
  ⟨(conjByCLM_commutes_rvd F U hU).2.2.1, (conjByCLM_commutes_rvd F U hU).2.2.2⟩

end Tier1_F13_F14

/-! ## Tier 2: Boundary, Corner, Negative & Counterexample Cases (`F1`–`F14`, 70) -/

section Tier2_F1_F3

theorem t2_f1_01 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    ImaginarySubmodule (H := H) ⊥ = ⊥ ∧
      ImaginarySubmodule (H := H) ⊤ = ⊤ := by
  constructor
  · ext x
    rw [mem_imaginarySubmodule_iff, Submodule.mem_bot, Submodule.mem_bot]
    constructor
    · intro hx
      have h := congrArg (fun y : H => (Complex.I : ℂ) • y) hx
      simp only [smul_zero] at h
      rwa [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] at h
    · rintro rfl
      simp
  · ext x
    simp [mem_imaginarySubmodule_iff]

theorem t2_f1_02 :
    IsStandardSubspace (H := ℂ) realAxisSubmodule ∧
      IsClosed (realAxisSubmodule : Set ℂ) :=
  ⟨realAxisSubmodule_isStandard, isClosed_realAxisSubmodule⟩

theorem t2_f1_03 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    IMapCLM H 0 = 0 :=
  map_zero (IMapCLM H)

theorem t2_f1_04 :
    IMapCLM ℂ 1 ≠ 0 ∧ IMapCLM ℂ 1 ∉ realAxisSubmodule := by
  refine ⟨?_, ?_⟩
  · change (Complex.I : ℂ) • (1 : ℂ) ≠ 0
    simp [Complex.I_ne_zero]
  · rw [mem_realAxisSubmodule_iff]
    change ((Complex.I : ℂ) • (1 : ℂ)).im ≠ 0
    simp

theorem t2_f1_05 :
    ¬ IsStandardSubspace (H := ℂ) (⊤ : Submodule ℝ ℂ) := by
  intro hStd
  have hmem : (1 : ℂ) ∈ (⊤ : Submodule ℝ ℂ) ⊓
      ImaginarySubmodule (H := ℂ) (⊤ : Submodule ℝ ℂ) := by
    refine ⟨Submodule.mem_top, ?_⟩
    exact (mem_imaginarySubmodule_iff (H := ℂ) (⊤ : Submodule ℝ ℂ) 1).mpr Submodule.mem_top
  rw [hStd.2, Submodule.mem_bot] at hmem
  exact one_ne_zero hmem

theorem t2_f2_01 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :
    letI : CompleteSpace (⊥ : Submodule ℝ H) :=
      (isClosed_singleton (x := (0 : H))).completeSpace_coe
    projK (H := H) ⊥ = 0 := by
  let : CompleteSpace (⊥ : Submodule ℝ H) :=
    (isClosed_singleton (x := (0 : H))).completeSpace_coe
  ext x
  have hx : projK (H := H) ⊥ x ∈ (⊥ : Submodule ℝ H) := projK_apply_mem ⊥ x
  simpa using hx

theorem t2_f2_02 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :
    letI : CompleteSpace (⊤ : Submodule ℝ H) := isClosed_univ.completeSpace_coe
    projK (H := H) ⊤ = 1 := by
  let : CompleteSpace (⊤ : Submodule ℝ H) := isClosed_univ.completeSpace_coe
  ext x
  exact (projK_eq_self_iff ⊤ x).mpr Submodule.mem_top

theorem t2_f2_03 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : Submodule ℝ H) [CompleteSpace K] {x : H} (hx : x ∈ K) :
    projK (H := H) K x = x :=
  (projK_eq_self_iff K x).mpr hx

theorem t2_f2_04 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : Submodule ℝ H) [CompleteSpace K] (x : H) :
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    projK (H := H) K x = 0 ↔ x ∈ Kᗮ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  exact K.starProjection_apply_eq_zero_iff

theorem t2_f2_05 :
    (projK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
        (tomitaRealSubspace diag2DensityFactor)).comp
      (projIK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
        (tomitaRealSubspace diag2DensityFactor)) ≠ 0 := by
  intro hzero
  let B1 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 1], ![1, 0]]
  let B2 : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, Complex.I], ![-Complex.I, 0]]
  let v1 := toHS 2 (B1 * diag2DensityFactor.r)
  let v2 := (Complex.I : ℂ) • toHS 2 (B2 * diag2DensityFactor.r)
  have hv1 : v1 ∈ tomitaRealSubspace diag2DensityFactor := by
    rw [mem_tomitaRealSubspace_iff]
    have hs : (toHS 2).symm v1 = B1 * diag2DensityFactor.r := (toHS 2).symm_apply_apply _
    rw [hs, Matrix.mul_assoc, diag2DensityFactor.r_mul_rInv, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B1, Matrix.conjTranspose_apply]
  have hv2 : v2 ∈ ImaginarySubmodule (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) := by
    rw [mem_imaginarySubmodule_iff]
    have hinv : (-Complex.I : ℂ) • v2 = toHS 2 (B2 * diag2DensityFactor.r) := by
      dsimp [v2]
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    rw [hinv, mem_tomitaRealSubspace_iff]
    have hs : (toHS 2).symm (toHS 2 (B2 * diag2DensityFactor.r)) =
        B2 * diag2DensityFactor.r := (toHS 2).symm_apply_apply _
    rw [hs, Matrix.mul_assoc, diag2DensityFactor.r_mul_rInv, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B2, Matrix.conjTranspose_apply]
  have hpv1 : projK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) v1 = v1 :=
    (projK_eq_self_iff (tomitaRealSubspace diag2DensityFactor) v1).mpr hv1
  have hpv2 : projIK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) v2 = v2 :=
    (projIK_eq_self_iff (tomitaRealSubspace diag2DensityFactor) v2).mpr hv2
  have hcomp : projK (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
      (tomitaRealSubspace diag2DensityFactor) v2 = 0 := by
    have hz := congrArg (fun f => f v2) hzero
    simpa [ContinuousLinearMap.comp_apply, hpv2] using hz
  have hinner : (⟪v1, v2⟫_ℂ).re = 0 := by
    have hre := projK_inner_re_left_eq_right (tomitaRealSubspace diag2DensityFactor) v1 v2
    rw [hpv1, hcomp, inner_zero_right, Complex.zero_re] at hre
    exact hre
  have hM1 : B1 * diag2DensityFactor.r = Matrix.of ![![(0 : ℂ), 1], ![2, 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B1, diag2DensityFactor, Matrix.mul_apply, Fin.sum_univ_two]
  have hM2 : B2 * diag2DensityFactor.r = Matrix.of ![![(0 : ℂ), Complex.I], ![-2 * Complex.I, 0]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [B2, diag2DensityFactor, Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  have hcalc : (⟪v1, v2⟫_ℂ).re = (3 : ℝ) := by
    change (⟪toHS 2 (B1 * diag2DensityFactor.r),
      toHS 2 (Complex.I • (B2 * diag2DensityFactor.r))⟫_ℂ).re = 3
    rw [toHS_inner, hM1, hM2]
    unfold ComplexMatrixTomitaDuality.hsInner
    simp [Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
    norm_num
  rw [hcalc] at hinner
  norm_num at hinner

theorem t2_f3_01 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K) :
    Function.Injective (rvdR (H := H) K) ∧
      Function.Injective ((2 : ℝ) • (1 : H →L[ℝ] H) - rvdR (H := H) K) ∧
      Function.Injective (rvdT (H := H) K) :=
  ⟨rvdR_injective K hK, two_sub_rvdR_injective K hK, rvdT_injective K hK⟩

theorem t2_f3_02 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :
    letI : CompleteSpace (⊥ : Submodule ℝ H) :=
      (isClosed_singleton (x := (0 : H))).completeSpace_coe
    letI : CompleteSpace (ImaginarySubmodule (H := H) ⊥) :=
      completeSpace_imaginarySubmodule (H := H) ⊥
    rvdR (H := H) ⊥ = 0 ∧ rvdT (H := H) ⊥ = 0 := by
  let : CompleteSpace (⊥ : Submodule ℝ H) :=
    (isClosed_singleton (x := (0 : H))).completeSpace_coe
  let : CompleteSpace (ImaginarySubmodule (H := H) ⊥) :=
    completeSpace_imaginarySubmodule (H := H) ⊥
  have him : ImaginarySubmodule (H := H) ⊥ = ⊥ := (t2_f1_01 (H := H)).1
  have hPK : projK (H := H) ⊥ = 0 := t2_f2_01
  have hPIK : projIK (H := H) ⊥ = 0 := by
    ext x
    have hx := projIK_apply_mem (H := H) ⊥ x
    rw [him, Submodule.mem_bot] at hx
    exact hx
  exact ⟨by rw [rvdR, hPK, hPIK, add_zero], by rw [rvdT, hPK, hPIK, sub_zero]⟩

theorem t2_f3_03 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :
    letI : CompleteSpace (⊤ : Submodule ℝ H) := isClosed_univ.completeSpace_coe
    letI : CompleteSpace (ImaginarySubmodule (H := H) ⊤) :=
      completeSpace_imaginarySubmodule (H := H) ⊤
    rvdR (H := H) ⊤ = (2 : ℝ) • (1 : H →L[ℝ] H) ∧ rvdT (H := H) ⊤ = 0 := by
  let : CompleteSpace (⊤ : Submodule ℝ H) := isClosed_univ.completeSpace_coe
  let : CompleteSpace (ImaginarySubmodule (H := H) ⊤) :=
    completeSpace_imaginarySubmodule (H := H) ⊤
  have him : ImaginarySubmodule (H := H) ⊤ = ⊤ := (t2_f1_01 (H := H)).2
  have hPK : projK (H := H) ⊤ = 1 := t2_f2_02
  have hPIK : projIK (H := H) ⊤ = 1 := by
    ext x
    exact (projIK_eq_self_iff (H := H) ⊤ x).mpr (him.symm ▸ Submodule.mem_top)
  refine ⟨?_, ?_⟩
  · rw [rvdR, hPK, hPIK, two_smul]
  · rw [rvdT, hPK, hPIK, sub_self]

theorem t2_f3_04 :
    rvdR (H := ℂ) realAxisSubmodule = 1 ∧
      rvdT (H := ℂ) realAxisSubmodule = (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∧
      rvdT (H := ℂ) realAxisSubmodule Complex.I = -Complex.I := by
  refine ⟨rvdR_realAxisSubmodule, rvdT_realAxisSubmodule, ?_⟩
  rw [rvdT_realAxisSubmodule]
  simp

theorem t2_f3_05 [CompleteSpace ℂ] :
    letI : CompleteSpace (⊥ : Submodule ℝ ℂ) :=
      (isClosed_singleton (x := (0 : ℂ))).completeSpace_coe
    letI : CompleteSpace (ImaginarySubmodule (H := ℂ) ⊥) :=
      completeSpace_imaginarySubmodule (H := ℂ) ⊥
    letI : CompleteSpace (⊤ : Submodule ℝ ℂ) := isClosed_univ.completeSpace_coe
    letI : CompleteSpace (ImaginarySubmodule (H := ℂ) ⊤) :=
      completeSpace_imaginarySubmodule (H := ℂ) ⊤
    ¬ Function.Injective (rvdR (H := ℂ) ⊥) ∧
      ¬ Function.Injective ((2 : ℝ) • (1 : ℂ →L[ℝ] ℂ) - rvdR (H := ℂ) ⊤) := by
  let : CompleteSpace (⊥ : Submodule ℝ ℂ) :=
    (isClosed_singleton (x := (0 : ℂ))).completeSpace_coe
  let : CompleteSpace (ImaginarySubmodule (H := ℂ) ⊥) :=
    completeSpace_imaginarySubmodule (H := ℂ) ⊥
  let : CompleteSpace (⊤ : Submodule ℝ ℂ) := isClosed_univ.completeSpace_coe
  let : CompleteSpace (ImaginarySubmodule (H := ℂ) ⊤) :=
    completeSpace_imaginarySubmodule (H := ℂ) ⊤
  refine ⟨?_, ?_⟩
  · intro hinj
    have h0 : rvdR (H := ℂ) ⊥ (1 : ℂ) = rvdR (H := ℂ) ⊥ 0 := by
      rw [(t2_f3_02 (H := ℂ)).1]
      simp
    exact one_ne_zero (hinj h0)
  · intro hinj
    have h0 : ((2 : ℝ) • (1 : ℂ →L[ℝ] ℂ) - rvdR (H := ℂ) ⊤) (1 : ℂ) =
        ((2 : ℝ) • (1 : ℂ →L[ℝ] ℂ) - rvdR (H := ℂ) ⊤) 0 := by
      rw [(t2_f3_03 (H := ℂ)).1, sub_self]
      simp
    exact one_ne_zero (hinj h0)

end Tier2_F1_F3

section Tier2_F4_F5

universe u

theorem t2_f4_01 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) :
    tomitaFormResolventCLM ω hclos 0 = 0 ∧
      tomitaSCompResolventRLM ω hclos 0 = 0 ∧
      tomitaFormComplementaryResolventCLM ω hclos 0 = 0 :=
  ⟨map_zero _, map_zero _, map_zero _⟩

theorem t2_f4_02 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) (ξ : ω.functional.GNS) :
    (tomitaFormResolventCLM ω hclos ξ = 0 ↔ ξ = 0) :=
  ⟨tomitaFormResolvent_eq_zero ω hclos ξ, fun h => by rw [h, map_zero]⟩

theorem t2_f4_03 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) (ξ : ω.functional.GNS) :
    ‖tomitaFormResolventCLM ω hclos ξ‖ ≤ ‖ξ‖ ∧
      ‖tomitaFormComplementaryResolventCLM ω hclos ξ‖ ≤ ‖ξ‖ :=
  ⟨tomitaFormResolvent_norm_le ω hclos ξ,
    tomitaFormComplementaryResolventCLM_norm_le ω hclos ξ⟩

theorem t2_f4_04 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) (ξ : ω.functional.GNS) :
    ‖tomitaFormResolventCLM ω hclos ξ‖ ^ 2 +
        ‖tomitaSCompResolventRLM ω hclos ξ‖ ^ 2 =
      (inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ)).re :=
  tomitaFormResolvent_energy ω hclos ξ

theorem t2_f4_05 {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) :
    tomitaFormResolventCLM ω hclos + tomitaFormComplementaryResolventCLM ω hclos =
      ContinuousLinearMap.id ℂ ω.functional.GNS := by
  ext ξ
  simp [tomitaFormComplementaryResolventCLM]

theorem t2_f5_01 {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    filteredTomitaGraphDomMap Stage sys ω hclos (le_refl i) x = x :=
  filteredTomitaGraphDomMap_id Stage sys ω hclos i x

theorem t2_f5_02 {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I) :
    tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i 0 = 0 ∧
      ‖(0 : ModularHilbertCompletion Stage sys ω hclos)‖ = 0 := by
  have h0 : ‖(0 : ModularHilbertCompletion Stage sys ω hclos)‖ = 0 := norm_zero
  exact ⟨map_zero _, h0⟩

theorem t2_f5_03 {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    ‖tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i x‖ ≤ ‖x‖ :=
  tomitaGraphDom_to_modularHilbertCompletion_apply_norm_le Stage sys ω hclos i x

theorem t2_f5_04 {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k)
    (x : TomitaGraphDom (ω.state i) (hclos i)) :
    filteredTomitaGraphDomMap Stage sys ω hclos (le_trans hij hjk) x =
      filteredTomitaGraphDomMap Stage sys ω hclos hjk
        (filteredTomitaGraphDomMap Stage sys ω hclos hij x) :=
  filteredTomitaGraphDomMap_comp Stage sys ω hclos hij hjk x

theorem t2_f5_05 {I : Type u} [Preorder I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    (y : closedTomitaDomain (ω.state i)) :
    closedTomitaModularForm Stage sys ω hclos i 0 y = 0 := by
  rw [closedTomitaModularForm_apply, map_zero, inner_zero_right]

end Tier2_F4_F5

section Tier2_F6_F7

theorem t2_f6_01 :
    embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) *
        embedGroup (θ := dihedral4Action) (DihedralGroup.sr 0) ≠
      embedGroup (θ := dihedral4Action) (DihedralGroup.sr 0) *
        embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) :=
  witness_group_noncommute

theorem t2_f6_02 {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (θ : PUnit →* (A ≃⋆ₐ[ℂ] A)) (g : PUnit) (a : A) :
    embedGroup (θ := θ) g = 1 ∧ single (θ := θ) g a = embedAlg a := by
  cases g
  change embedGroup (θ := θ) 1 = 1 ∧ single (θ := θ) 1 a = embedAlg a
  exact ⟨embedGroup_one, rfl⟩

theorem t2_f6_03 {G : Type*} [Group G]
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (g : G) (a : A) :
    embedGroup (θ := (1 : G →* (A ≃⋆ₐ[ℂ] A))) g * embedAlg a =
      embedAlg a * embedGroup (θ := (1 : G →* (A ≃⋆ₐ[ℂ] A))) g := by
  rw [embedGroup_mul_embedAlg]
  simp

theorem t2_f6_04 {G : Type*} [Group G]
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {θ : G →* (A ≃⋆ₐ[ℂ] A)} :
    star (0 : TwistedCrossedProduct G A θ) = 0 ∧
      embedAlg (θ := θ) 0 = 0 :=
  ⟨star_zero _, map_zero _⟩

theorem t2_f6_05 {G : Type*} [Group G]
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {θ : G →* (A ≃⋆ₐ[ℂ] A)} :
    embedAlg (θ := θ) (1 : A) = 1 ∧ embedGroup (θ := θ) (1 : G) = 1 :=
  ⟨map_one _, embedGroup_one⟩

theorem t2_f7_01 :
    embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) * embedAlg witnessE01 ≠
        embedAlg witnessE01 * embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) ∨
      embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) *
          embedAlg (Matrix.of ![![1, 0], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) ≠
        embedAlg (Matrix.of ![![1, 0], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) *
          embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) :=
  Or.inr witness_twist_noncommute

theorem t2_f7_02 {G : Type*} [Group G]
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {θ : G →* (A ≃⋆ₐ[ℂ] A)} {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (π : A →⋆ₐ[ℂ] B) (U : G →* unitary B)
    (hcov : ∀ (g : G) (a : A), (U g : B) * π a * star (U g : B) = π (θ g a)) :
    covariantLift (θ := θ) π U hcov (embedAlg 0) = 0 ∧
      covariantLift (θ := θ) π U hcov (embedGroup 1) = 1 := by
  simp

theorem t2_f7_03 :
    witnessCovariantLift (embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) *
        embedAlg (Matrix.of ![![1, 0], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ)) ≠
      witnessCovariantLift (embedAlg (Matrix.of ![![1, 0], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℂ) *
        embedGroup (θ := dihedral4Action) (DihedralGroup.r 1)) :=
  witness_covariantLift_nontrivial.2.2

theorem t2_f7_04 {G : Type*} [Group G]
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {θ : G →* (A ≃⋆ₐ[ℂ] A)} (f : TwistedCrossedProduct G A θ) :
    dualAction (θ := θ) 1 f = f := by
  rw [dualAction_one]
  rfl

theorem t2_f7_05 {G : Type*} [Group G]
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {θ : G →* (A ≃⋆ₐ[ℂ] A)} (χ : G →* unitary ℂ) (f : TwistedCrossedProduct G A θ) :
    dualActionAut (θ := θ) χ⁻¹ (dualActionAut (θ := θ) χ f) = f ∧
      dualActionHom (θ := θ) χ⁻¹ * dualActionHom (θ := θ) χ = 1 := by
  have h1 : dualActionAut (θ := θ) χ⁻¹ (dualActionAut (θ := θ) χ f) = f :=
    (dualActionAut (θ := θ) χ).symm_apply_apply f
  have h2 : dualActionHom (θ := θ) χ⁻¹ * dualActionHom (θ := θ) χ = 1 := by
    have hmul : χ⁻¹ * χ = 1 := by
      ext g
      simp
    rw [← (dualActionHom (θ := θ)).map_mul, hmul, map_one]
  exact ⟨h1, h2⟩

end Tier2_F6_F7

section Tier2_F8

theorem t2_f8_01 :
    ((1 / 2 : ℝ) ^ (1 : ℤ) < (1 / 2 : ℝ) ^ (0 : ℤ)) ∧
      ((1 / 2 : ℝ) ^ (0 : ℤ) < (1 / 2 : ℝ) ^ (-1 : ℤ)) :=
  ⟨powersPointSpec_strictAnti (by norm_num) (by norm_num) (by decide : (0 : ℤ) < 1),
    powersPointSpec_strictAnti (by norm_num) (by norm_num) (by decide : (-1 : ℤ) < 0)⟩

theorem t2_f8_02 {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (-1 : ℝ) ∉ powersPointSpec lam ∧
      ((1 + lam) / 2) ∉ powersPointSpec lam := by
  refine ⟨?_, ?_⟩
  · rintro ⟨k, hk⟩
    have hpos := zpow_pos hlam0 k
    linarith
  · rintro ⟨k, hk⟩
    by_cases hk0 : k ≤ 0
    · have hge : (1 : ℝ) ≤ lam ^ k := by
        have hanti := (powersPointSpec_strictAnti hlam0 hlam1).antitone hk0
        simpa using hanti
      linarith
    · have hk1 : (1 : ℤ) ≤ k := by omega
      have hle : lam ^ k ≤ lam := by
        have hanti := (powersPointSpec_strictAnti hlam0 hlam1).antitone hk1
        simpa using hanti
      linarith

theorem t2_f8_03 {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (0 : ℝ) ∉ powersPointSpec lam ∧ (0 : ℝ) ∈ closure (powersPointSpec lam) :=
  ⟨zero_notMem_powersPointSpec hlam0, zero_mem_closure_powersPointSpec hlam0 hlam1⟩

theorem t2_f8_04 {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (k : ℕ) :
    ¬ ∃ E : UHFStage k, E ≠ 0 ∧
        powersModularOp lam k E = ((lam ^ (k + 1) : ℝ) : ℂ) • E :=
  next_power_not_stage_eigenvalue hlam0 hlam1 k

theorem t2_f8_05 (k m : ℕ) (hm : m ≠ 0) (A B : UHFStage k) (x y : RealBlockColimit m) :
    FiniteDimensional ℂ (UHFStage k) ∧
      uhfStageNormTrace k (A * B) = uhfStageNormTrace k (B * A) ∧
      realBlockColimitNormTrace m (x * y) = realBlockColimitNormTrace m (y * x) ∧
      (realBlockColimitNormTrace m (star x * x) = 0 ↔ x = 0) :=
  ⟨uhfStage_finiteDimensional k, uhfStageNormTrace_comm k A B,
    realBlockColimitNormTrace_mul_comm m x y,
    realBlockColimitNormTrace_faithful hm x⟩

end Tier2_F8

section Tier2_F9_F10

theorem t2_f9_01 {n : ℕ} (F : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F F X = tomitaOp F X ∧
      relModularOp F F X = modularOp F X ∧
      relModularSqrt F F X = modularSqrt F X :=
  ⟨relTomitaOp_self F X, relModularOp_self F X, relModularSqrt_self F X⟩

theorem t2_f9_02 {n : ℕ} (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp F_φ F_ψ (relTomitaOp F_ψ F_φ X) = X ∧
      (relTomitaOp F_ψ F_φ X = 0 ↔ X = 0) := by
  refine ⟨relTomitaOp_swap_involutive F_ψ F_φ X, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hswap := relTomitaOp_swap_involutive F_ψ F_φ X
    rw [h] at hswap
    simpa [relTomitaOp] using hswap.symm
  · subst h
    simp [relTomitaOp]

theorem t2_f9_03 {n : ℕ} (F_ψ F_φ : PositiveComplexDensityFactor n) :
    relModularOp F_ψ F_φ 1 = F_ψ.rho * F_φ.rhoInv ∧
      relModularSqrt F_ψ F_φ 1 = F_ψ.r * F_φ.rInv := by
  simp [relModularOp, relModularSqrt]

theorem t2_f9_04 (a b c d : ℂ) :
    Matrix.diagonal ![a, b] * Matrix.diagonal ![c, d] =
        Matrix.diagonal ![c, d] * Matrix.diagonal ![a, b] ∧
      witnessRhoPsi * witnessRhoPhi ≠ witnessRhoPhi * witnessRhoPsi := by
  refine ⟨?_, witnessRhoPsi_mul_witnessRhoPhi_ne⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem t2_f9_05 {n : ℕ} (F_ψ F_φ : PositiveComplexDensityFactor n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ (hsInner n X (relModularOp F_ψ F_φ X)).re ∧
      (hsInner n X (relModularOp F_ψ F_φ X) = 0 ↔ X = 0) :=
  ⟨relModularOp_hsPos_re_nonneg F_ψ F_φ X, relModularOp_hsPos_eq_zero_iff F_ψ F_φ X⟩

theorem t2_f10_01 {n : ℕ} (E : ExpDensityFactor n) (t : ℝ) :
    relConnesCocycle E E t = 1 := by
  unfold relConnesCocycle
  exact E.unitary_mul_neg t

theorem t2_f10_02 {n : ℕ} (E_ψ E_φ : ExpDensityFactor n) (s : ℝ) :
    relConnesCocycle E_ψ E_φ (-s) =
      E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s)ᴴ := by
  have hc := relConnesCocycle_cocycle_id E_ψ E_φ (-s) s
  rw [neg_add_cancel, relConnesCocycle_zero] at hc
  have hunit : E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s) *
      (E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s))ᴴ = 1 := by
    rw [E_φ.modularFlow_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      E_φ.unitary_conjTranspose, E_φ.unitary_conjTranspose, neg_neg]
    calc
      (E_φ.unitary (-s) * relConnesCocycle E_ψ E_φ s * E_φ.unitary s) *
          (E_φ.unitary (-s) * ((relConnesCocycle E_ψ E_φ s)ᴴ * E_φ.unitary s))
          = E_φ.unitary (-s) * relConnesCocycle E_ψ E_φ s *
              (E_φ.unitary s * E_φ.unitary (-s)) *
              (relConnesCocycle E_ψ E_φ s)ᴴ * E_φ.unitary s := by
            simp only [Matrix.mul_assoc]
      _ = E_φ.unitary (-s) *
            (relConnesCocycle E_ψ E_φ s * (relConnesCocycle E_ψ E_φ s)ᴴ) *
            E_φ.unitary s := by
          rw [E_φ.unitary_mul_neg, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [relConnesCocycle_unitary_left, Matrix.mul_one, E_φ.unitary_neg_mul]
  have hadj : (E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s))ᴴ =
      E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s)ᴴ := by
    rw [E_φ.modularFlow_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      E_φ.unitary_conjTranspose, E_φ.unitary_conjTranspose, neg_neg, E_φ.modularFlow_apply,
      neg_neg, Matrix.mul_assoc]
  calc
    relConnesCocycle E_ψ E_φ (-s)
        = relConnesCocycle E_ψ E_φ (-s) *
            (E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s) *
              (E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s))ᴴ) := by
          rw [hunit, Matrix.mul_one]
    _ = (relConnesCocycle E_ψ E_φ (-s) *
            E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s)) *
          (E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s))ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = 1 * (E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s))ᴴ := by rw [← hc]
    _ = E_φ.modularFlow (-s) (relConnesCocycle E_ψ E_φ s)ᴴ := by rw [Matrix.one_mul, hadj]

theorem t2_f10_03 :
    relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2) ≠ 1 ∧
      ∀ c : ℂ, relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2) ≠
        c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, witnessCocycle_nonscalar⟩
  simpa using witnessCocycle_nonscalar 1

theorem t2_f10_04 :
    let u := relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2)
    let P : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(1 : ℂ), (0 : ℂ)]
    u * P ≠ P * u :=
  witnessCocycle_noncomm_diag

theorem t2_f10_05 :
    witnessRhoPsi * witnessRhoPhi ≠ witnessRhoPhi * witnessRhoPsi ∧
      relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2) 0 1 = (24 / 25 : ℂ) :=
  ⟨witnessRhoPsi_mul_witnessRhoPhi_ne, witnessCocycle_at_pi_div_two_01⟩

end Tier2_F9_F10

section Tier2_F11_F12

theorem t2_f11_01 {α : Type*} [MeasurableSpace α] {μ : Measure α} :
    lpMulOpOfBound (α := α) (μ := μ) (0 : α → ℂ) aestronglyMeasurable_zero 0
      (Eventually.of_forall fun _ => by simp) = 0 := by
  refine ContinuousLinearMap.ext fun ψ => MeasureTheory.Lp.ext ?_
  filter_upwards [lpMulOpOfBound_apply_ae (0 : α → ℂ) aestronglyMeasurable_zero 0
      (Eventually.of_forall fun _ => by simp) ψ,
    MeasureTheory.Lp.coeFn_zero ℂ 2 μ] with x h1 hz
  change ⇑(lpMulOpOfBound (α := α) (μ := μ) (0 : α → ℂ) aestronglyMeasurable_zero 0 _ ψ) x =
    ⇑(0 : L2c α μ) x
  rw [h1, hz]
  simp

theorem t2_f11_02 {α : Type*} [MeasurableSpace α] {μ : Measure α} (c : ℂ) :
    lpMulOpOfBound (α := α) (μ := μ) (fun _ => c) aestronglyMeasurable_const ‖c‖
      (Eventually.of_forall fun _ => le_rfl) = c • (1 : L2c α μ →L[ℂ] L2c α μ) := by
  refine ContinuousLinearMap.ext fun ψ => MeasureTheory.Lp.ext ?_
  filter_upwards [lpMulOpOfBound_apply_ae (fun _ => c) aestronglyMeasurable_const ‖c‖
      (Eventually.of_forall fun _ => le_rfl) ψ,
    MeasureTheory.Lp.coeFn_smul c ψ] with x h1 hs
  change ⇑(lpMulOpOfBound (α := α) (μ := μ) (fun _ => c) aestronglyMeasurable_const ‖c‖ _ ψ) x =
    ⇑(c • ψ) x
  rw [h1, hs]
  rfl

theorem t2_f11_03 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Set α) (hS : MeasurableSet S) :
    ‖pvmProj (α := α) (μ := μ) S hS‖ ≤ 1 :=
  norm_lpMulOpOfBound_le _ (aestronglyMeasurable_const.indicator hS) zero_le_one
    (Eventually.of_forall fun x => by by_cases hx : x ∈ S <;> simp [hx])

theorem t2_f11_04 :
    let μ : Measure Bool := Measure.count
    let f : Bool → ℂ := fun b => if b then 2 else 3
    ‖lpMulOpOfBound (α := Bool) (μ := μ) f (measurable_of_finite f).aestronglyMeasurable 3
        (Eventually.of_forall fun b => by cases b <;> norm_num [f])‖ ≤ 3 :=
  norm_lpMulOpOfBound_le _ (measurable_of_finite _).aestronglyMeasurable (by norm_num)
    (Eventually.of_forall fun b => by cases b <;> norm_num)

theorem t2_f11_05 {α : Type*} [MeasurableSpace α]
    (f : α → ℂ) (hf : AEStronglyMeasurable f (0 : Measure α))
    (C : ℝ) (hC : ∀ᵐ x ∂(0 : Measure α), ‖f x‖ ≤ C) :
    lpMulOpOfBound (α := α) (μ := (0 : Measure α)) f hf C hC = 0 := by
  refine ContinuousLinearMap.ext fun ψ => MeasureTheory.Lp.ext ?_
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  simp

theorem t2_f12_01 {α : Type*} [MeasurableSpace α] {μ : Measure α} :
    pvmProj (α := α) (μ := μ) ∅ MeasurableSet.empty = 0 ∧
      pvmProj (α := α) (μ := μ) Set.univ MeasurableSet.univ = 1 :=
  ⟨pvmProj_empty, pvmProj_univ⟩

theorem t2_f12_02 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Set α) (hS : MeasurableSet S) :
    pvmProj (α := α) (μ := μ) Sᶜ hS.compl = 1 - pvmProj (α := α) (μ := μ) S hS := by
  refine ContinuousLinearMap.ext fun ψ => MeasureTheory.Lp.ext ?_
  filter_upwards [pvmProj_apply_ae Sᶜ hS.compl ψ, pvmProj_apply_ae S hS ψ,
    MeasureTheory.Lp.coeFn_sub ψ (pvmProj (α := α) (μ := μ) S hS ψ)] with x hSc hS' hsub
  change ⇑(pvmProj (α := α) (μ := μ) Sᶜ hS.compl ψ) x =
    ⇑(ψ - pvmProj (α := α) (μ := μ) S hS ψ) x
  rw [hsub, Pi.sub_apply, hSc, hS']
  by_cases hx : x ∈ S <;> simp [hx]

theorem t2_f12_03 {α : Type*} [MeasurableSpace α] {μ : Measure α} (t : ℝ) :
    stoneMulGroup (α := α) (μ := μ) (fun _ => (0 : ℝ)) measurable_const t = 1 := by
  refine ContinuousLinearMap.ext fun ψ => MeasureTheory.Lp.ext ?_
  filter_upwards [stoneMulGroup_apply_ae (fun _ => (0 : ℝ)) measurable_const t ψ] with x hx
  simp [hx]

theorem t2_f12_04 {α : Type*} [MeasurableSpace α] {μ : Measure α} (c t : ℝ) :
    stoneMulGroup (α := α) (μ := μ) (fun _ => c) measurable_const t =
      Complex.exp (Complex.I * (t : ℂ) * (c : ℂ)) • (1 : L2c α μ →L[ℂ] L2c α μ) := by
  refine ContinuousLinearMap.ext fun ψ => MeasureTheory.Lp.ext ?_
  filter_upwards [stoneMulGroup_apply_ae (fun _ => c) measurable_const t ψ,
    MeasureTheory.Lp.coeFn_smul (Complex.exp (Complex.I * (t : ℂ) * (c : ℂ))) ψ] with x h1 hs
  change ⇑(stoneMulGroup (α := α) (μ := μ) (fun _ => c) measurable_const t ψ) x =
    ⇑(Complex.exp (Complex.I * (t : ℂ) * (c : ℂ)) • ψ) x
  rw [h1, hs]
  rfl

theorem t2_f12_05 :
    stoneMulGroup (α := Bool) (μ := Measure.count) (fun b => if b then (1 : ℝ) else 0)
        (measurable_of_finite _) Real.pi ≠ 1 := by
  intro hEq
  let ψ : L2c Bool Measure.count :=
    MeasureTheory.indicatorConstLp 2 (measurableSet_singleton true) (by simp) (1 : ℂ)
  have hψ := congrArg (fun T : L2c Bool Measure.count →L[ℂ] L2c Bool Measure.count => T ψ) hEq
  have hae : ⇑(stoneMulGroup (α := Bool) (μ := Measure.count)
      (fun b => if b then (1 : ℝ) else 0) (measurable_of_finite _) Real.pi ψ) =ᵐ[Measure.count]
      ⇑ψ :=
    MeasureTheory.Lp.ext_iff.mp hψ
  have htrue : (⇑(stoneMulGroup (α := Bool) (μ := Measure.count)
      (fun b => if b then (1 : ℝ) else 0) (measurable_of_finite _) Real.pi ψ)) true =
      (⇑ψ) true :=
    (Measure.ae_count_iff.mp hae) true
  have h1 : (⇑(stoneMulGroup (α := Bool) (μ := Measure.count)
      (fun b => if b then (1 : ℝ) else 0) (measurable_of_finite _) Real.pi ψ)) true =
      Complex.exp (Complex.I * (Real.pi : ℂ) * (1 : ℂ)) * (⇑ψ) true := by
    have ha := stoneMulGroup_apply_ae (α := Bool) (μ := Measure.count)
      (fun b => if b then (1 : ℝ) else 0) (measurable_of_finite _) Real.pi ψ
    simpa using (Measure.ae_count_iff.mp ha) true
  have hψt : (⇑ψ) true = (1 : ℂ) := by
    have hind : (⇑ψ) =ᵐ[Measure.count] ({true} : Set Bool).indicator (fun _ => (1 : ℂ)) :=
      MeasureTheory.indicatorConstLp_coeFn
    have ht := (Measure.ae_count_iff.mp hind) true
    simpa using ht
  rw [h1, hψt, mul_one, mul_one, mul_comm Complex.I _, Complex.exp_pi_mul_I] at htrue
  norm_num at htrue

end Tier2_F11_F12

section Tier2_F13_F14

theorem t2_f13_01 :
    (∀ A B : Matrix (Fin 0) (Fin 0) ℂ, A = B) ∧
      witnessE01 * witnessE10 ≠ witnessE10 * witnessE01 := by
  refine ⟨fun A B => ?_, witnessE01_mul_witnessE10_ne⟩
  ext i
  exact Fin.elim0 i

theorem t2_f13_02 :
    commutant {ComplexMatrixTomitaDuality.leftMul 2 witnessE01} ≠
        ComplexMatrixTomitaDuality.rightRegSet 2 ∧
      commutant {ComplexMatrixTomitaDuality.leftMul 2 (1 : Matrix (Fin 2) (Fin 2) ℂ)} ≠
        ComplexMatrixTomitaDuality.rightRegSet 2 :=
  ⟨single_leftMul_commutant_ne_rightRegSet, single_leftMul_one_commutant_ne_rightRegSet⟩

theorem t2_f13_03 :
    (0 : ℝ) < 1 ∧ stage1DiagTomitaAndKMSBridge.kmsState.state 1 = 1 :=
  ⟨stage1DiagTomitaAndKMSBridge.kmsState.beta_pos,
    stage1DiagTomitaAndKMSBridge.kmsState.state_one⟩

theorem t2_f13_04 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ComplexMatrixTomitaDuality.matrixJ 2 (Complex.I • X) = -Complex.I • Xᴴ ∧
      (∀ (Y : Matrix (Fin 2) (Fin 2) ℝ),
        InfoGeometry.Canonical.FiniteMatrixTomitaPolar.hsInner Y Y ≥ 0) := by
  refine ⟨?_, fun Y => InfoGeometry.Canonical.FiniteMatrixTomitaPolar.hsInner_self_nonneg Y⟩
  rw [matrixJ_apply, Matrix.conjTranspose_smul]
  simp

theorem t2_f13_05 :
    ComplexMatrixTomitaDuality.leftMul 2 witnessE01 ∘
        ComplexMatrixTomitaDuality.leftMul 2 witnessE10 ≠
      ComplexMatrixTomitaDuality.leftMul 2 witnessE10 ∘
        ComplexMatrixTomitaDuality.leftMul 2 witnessE01 := by
  intro h
  have h1 := congrArg (fun f => f 1) h
  simp only [Function.comp_apply, ComplexMatrixTomitaDuality.leftMul, Matrix.mul_one] at h1
  exact witnessE01_mul_witnessE10_ne h1

theorem t2_f14_01 :
    ((IMapCLM ℂ).comp (projK (H := ℂ) realAxisSubmodule) ≠
        (projK (H := ℂ) realAxisSubmodule).comp (IMapCLM ℂ)) ∧
      ((IMapCLM ℂ).comp (rvdT (H := ℂ) realAxisSubmodule) ≠
        (rvdT (H := ℂ) realAxisSubmodule).comp (IMapCLM ℂ)) := by
  have hIM : IMapCLM ℂ 1 = Complex.I := by
    simp [IMapCLM_apply, IMap]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := congrArg (fun f : ℂ →L[ℝ] ℂ => f 1) h
    have hp1 : projK (H := ℂ) realAxisSubmodule 1 = 1 := by
      simp [projK_realAxisSubmodule]
    have hpI : projK (H := ℂ) realAxisSubmodule Complex.I = 0 := by
      simp [projK_realAxisSubmodule]
    simp only [ContinuousLinearMap.comp_apply, hp1, hIM, hpI] at h1
    exact Complex.I_ne_zero h1
  · intro h
    have h1 := congrArg (fun f : ℂ →L[ℝ] ℂ => f 1) h
    have h1' : Complex.I * star (1 : ℂ) = star (Complex.I * (1 : ℂ)) := by
      simpa [IMapCLM_apply, IMap, rvdT_realAxisSubmodule] using h1
    simp only [star_one, mul_one, Complex.star_def, Complex.conj_I] at h1'
    have him := congrArg Complex.im h1'
    simp only [Complex.I_im, Complex.neg_im] at him
    norm_num at him

theorem t2_f14_02 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] :
    ((0 : H →L[ℂ] H).restrictScalars ℝ).comp (rvdR (H := H) K) =
        (rvdR (H := H) K).comp ((0 : H →L[ℂ] H).restrictScalars ℝ) ∧
      ((1 : H →L[ℂ] H).restrictScalars ℝ).comp (rvdT (H := H) K) =
        (rvdT (H := H) K).comp ((1 : H →L[ℂ] H).restrictScalars ℝ) := by
  have h0 := bounded_commutant_criterion_of_preserves_subspace K (0 : H →L[ℂ] H)
    (fun _ _ => K.zero_mem) (fun _ _ => by simp)
  have h1 := bounded_commutant_criterion_of_preserves_subspace K (1 : H →L[ℂ] H)
    (fun _ hx => hx) (fun _ hx => by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
      exact hx)
  exact ⟨h0.2.2.1, h1.2.2.2⟩

theorem t2_f14_03 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (A : H →L[ℂ] H) (hSA : IsSelfAdjoint A) (hAK : ∀ x ∈ K, A x ∈ K) :
    (A.restrictScalars ℝ).comp (rvdR (H := H) K) =
        (rvdR (H := H) K).comp (A.restrictScalars ℝ) ∧
      (A.restrictScalars ℝ).comp (rvdT (H := H) K) =
        (rvdT (H := H) K).comp (A.restrictScalars ℝ) := by
  have hAdj : ∀ x ∈ K, A.adjoint x ∈ K := by
    intro x hx
    have ha : A.adjoint = A := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact hSA.star_eq
    rw [ha]
    exact hAK x hx
  exact ⟨(bounded_commutant_criterion_of_preserves_subspace K A hAK hAdj).2.2.1,
    (bounded_commutant_criterion_of_preserves_subspace K A hAK hAdj).2.2.2⟩

theorem t2_f14_04 :
    realVecE01CLM.comp realVecE10CLM ≠ realVecE10CLM.comp realVecE01CLM ∧
      ((realVecE01CLM.restrictScalars ℝ).comp
          (rvdR (H := EuclideanSpace ℂ (Fin 2)) (realVecSubmodule 2)) =
        (rvdR (H := EuclideanSpace ℂ (Fin 2)) (realVecSubmodule 2)).comp
          (realVecE01CLM.restrictScalars ℝ)) :=
  ⟨realVecE01CLM_comp_realVecE10CLM_ne,
    (realMatrixToEuclideanCLM_commutes_rvd (Matrix.of ![![0, (1 : ℝ)], ![0, 0]])).2.2.1⟩

theorem t2_f14_05 :
    rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2)) (tomitaRealSubspace diag2DensityFactor) ≠ 1 ∧
      ((conjByCLM diag2CentralizerU).restrictScalars ℝ).comp
          (rvdT (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
            (tomitaRealSubspace diag2DensityFactor)) =
        (rvdT (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor)).comp
          ((conjByCLM diag2CentralizerU).restrictScalars ℝ) :=
  ⟨diag2DensityFactor_rvdR_ne_one, diag2_centralizer_commutes_rvd.2.2.2⟩

end Tier2_F13_F14

/-! ## Tier 3: Cross-Feature Pairwise Interactions (15 Theorems) -/

section Tier3_CrossFeature

theorem t3_01_f1_f2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    ‖IMapCLM H (projK (H := H) K x)‖ = ‖projK (H := H) K x‖ ∧
      IMapCLM H (projK (H := H) K x) = projIK (H := H) K (IMapCLM H x) :=
  ⟨IMapCLM_norm _, congrArg (fun f : H →L[ℝ] H => f x) (IMapCLM_comp_projK K)⟩

theorem t3_02_f2_f3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)] (x : H) :
    ‖(1 - rvdR (H := H) K) x‖ ^ 2 + ‖rvdT (H := H) K x‖ ^ 2 = ‖x‖ ^ 2 ∧
      rvdR (H := H) K x = projK (H := H) K x + projIK (H := H) K x ∧
      rvdT (H := H) K x = projK (H := H) K x - projIK (H := H) K x :=
  ⟨one_sub_rvdR_norm_sq_add_rvdT_norm_sq K x, rfl, rfl⟩

theorem t3_03_f1_f14 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    (hK : IsStandardSubspace (H := H) K)
    (A : H →L[ℂ] H) (hAK : ∀ x ∈ K, A x ∈ K) (hAdjK : ∀ x ∈ K, A.adjoint x ∈ K) :
    Function.Injective (rvdR (H := H) K) ∧
      (A.restrictScalars ℝ).comp (projK (H := H) K) =
        (projK (H := H) K).comp (A.restrictScalars ℝ) ∧
      (A.restrictScalars ℝ).comp (rvdT (H := H) K) =
        (rvdT (H := H) K).comp (A.restrictScalars ℝ) :=
  ⟨rvdR_injective K hK,
    (bounded_commutant_criterion_of_preserves_subspace K A hAK hAdjK).1,
    (bounded_commutant_criterion_of_preserves_subspace K A hAK hAdjK).2.2.2⟩

theorem t3_04_f4_f5 {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type _) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I) :
    DenseRange (tomitaFormResolventCLM (ω.state i) (hclos i)) ∧
      ‖gns_to_modularHilbertCompletion_via_resolvent Stage sys ω hclos i‖ ≤ 1 :=
  ⟨tomitaFormResolvent_denseRange (ω.state i) (hclos i),
    gns_to_modularHilbertCompletion_via_resolvent_norm_le Stage sys ω hclos i⟩

theorem t3_05_f3_f4_separation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : Submodule ℝ H) [CompleteSpace K]
    [CompleteSpace (ImaginarySubmodule (H := H) K)]
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (ω : State A) (hclos : IsClosableTomitaCore ω) (x : H) (ξ : ω.functional.GNS) :
    (0 ≤ (⟪x, rvdR (H := H) K x⟫_ℂ).re ∧ (⟪x, rvdR (H := H) K x⟫_ℂ).re ≤ 2 * ‖x‖ ^ 2) ∧
      (0 ≤ (inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ)).re ∧
        (inner ℂ ξ (tomitaFormResolventCLM ω hclos ξ)).re ≤ ‖ξ‖ ^ 2) ∧
      rvdR (H := ℂ) realAxisSubmodule = 1 :=
  ⟨rvdR_inner_re_bounds K x, tomitaFormResolvent_pos_le_one ω hclos ξ, rvdR_realAxisSubmodule⟩

theorem t3_06_f6_f7 :
    witnessCovariantLift (embedAlg (Matrix.of ![![1, 0], ![0, 0]])) =
        Matrix.of ![![1, 0], ![0, 0]] ∧
      witnessCovariantLift (embedGroup (DihedralGroup.r 1)) =
        (dihedral4UnitaryHom (DihedralGroup.r 1) : Matrix (Fin 2) (Fin 2) ℂ) ∧
      dualAction (θ := dihedral4Action) (1 : DihedralGroup 4 →* unitary ℂ) =
        StarAlgHom.id ℂ _ :=
  ⟨covariantLift_embedAlg _ _ _ _, covariantLift_embedGroup _ _ _ _, dualAction_one⟩

theorem t3_07_f6_f8 (k : ℕ) (g : DihedralGroup 4) (a : UHFStage 1) :
    embedGroup (θ := dihedral4Action) g * embedAlg a * star (embedGroup g) =
        embedAlg (dihedral4Action g a) ∧
      uhfStageNormTrace k 1 = 1 ∧
      (0 : ℝ) ∉ powersPointSpec (1 / 2 : ℝ) :=
  ⟨covariant_relation g a, uhfStageNormTrace_one k, zero_notMem_powersPointSpec (by norm_num)⟩

theorem t3_08_f8_f13 (k : ℕ) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (A B : UHFStage k) :
    powersState lam k (A * powersModularOp lam k B) = powersState lam k (B * A) ∧
      commutant (ComplexMatrixTomitaDuality.leftRegSet (2 ^ k)) =
        ComplexMatrixTomitaDuality.rightRegSet (2 ^ k) ∧
      closure (powersPointSpec lam) = insert (0 : ℝ) (powersPointSpec lam) :=
  ⟨powersState_kms hlam0 k A B,
    fullLeftReg_commutant_eq_rightReg (2 ^ k),
    closure_powersPointSpec_eq_insert_zero hlam0 hlam1⟩

theorem t3_09_f9_f10 {n : ℕ} (E_ψ E_φ : ExpDensityFactor n) (t : ℝ)
    (A X : Matrix (Fin n) (Fin n) ℂ) :
    relTomitaOp E_ψ.toPositiveComplexDensityFactor E_φ.toPositiveComplexDensityFactor X =
        matrixJ n (relModularSqrt E_ψ.toPositiveComplexDensityFactor
          E_φ.toPositiveComplexDensityFactor X) ∧
      E_ψ.modularFlow t A =
        relConnesCocycle E_ψ E_φ t * E_φ.modularFlow t A * (relConnesCocycle E_ψ E_φ t)ᴴ ∧
      relModularUnitary E_ψ E_φ t 1 = relConnesCocycle E_ψ E_φ t :=
  ⟨relTomitaOp_polar _ _ X, relConnesCocycle_intertwines E_ψ E_φ t A,
    relModularUnitary_one_eq_cocycle E_ψ E_φ t⟩

theorem t3_10_f10_f13 (t : ℝ) :
    commutant (ComplexMatrixTomitaDuality.leftRegSet 2) =
        ComplexMatrixTomitaDuality.rightRegSet 2 ∧
      witnessRhoPsi * witnessRhoPhi ≠ witnessRhoPhi * witnessRhoPsi ∧
      relConnesCocycle witnessExpPsi witnessExpPhi t *
        (relConnesCocycle witnessExpPsi witnessExpPhi t)ᴴ = 1 :=
  ⟨fullLeftReg_commutant_eq_rightReg 2, witnessRhoPsi_mul_witnessRhoPhi_ne,
    relConnesCocycle_unitary_left witnessExpPsi witnessExpPhi t⟩

theorem t3_11_f11_f12 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (S : Set α) (hS : MeasurableSet S) (h : α → ℝ) (hh : Measurable h) (t : ℝ) :
    IsStarProjection (pvmProj (α := α) (μ := μ) S hS) ∧
      stoneMulGroup (α := α) (μ := μ) h hh t ∘L stoneMulGroup h hh (-t) = 1 :=
  ⟨pvmProj_isStarProjection S hS, stoneMulGroup_comp_neg h hh t⟩

theorem t3_12_f11_f12_commute {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℂ) (hf : AEStronglyMeasurable f μ) (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C)
    (S : Set α) (hS : MeasurableSet S) (h : α → ℝ) (hh : Measurable h) (t : ℝ) :
    lpMulOpOfBound (α := α) (μ := μ) f hf C hC ∘L pvmProj S hS =
        pvmProj S hS ∘L lpMulOpOfBound f hf C hC ∧
      lpMulOpOfBound (α := α) (μ := μ) f hf C hC ∘L stoneMulGroup h hh t =
        stoneMulGroup h hh t ∘L lpMulOpOfBound f hf C hC := by
  constructor
  · refine ContinuousLinearMap.ext fun ψ => MeasureTheory.Lp.ext ?_
    filter_upwards [lpMulOpOfBound_apply_ae f hf C hC (pvmProj S hS ψ),
      pvmProj_apply_ae S hS ψ,
      pvmProj_apply_ae S hS (lpMulOpOfBound f hf C hC ψ),
      lpMulOpOfBound_apply_ae f hf C hC ψ] with x h1 h2 h3 h4
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, h3, h4]
    exact mul_left_comm (f x) (S.indicator (fun _ => (1 : ℂ)) x) (ψ x)
  · refine ContinuousLinearMap.ext fun ψ => MeasureTheory.Lp.ext ?_
    filter_upwards [lpMulOpOfBound_apply_ae f hf C hC (stoneMulGroup h hh t ψ),
      stoneMulGroup_apply_ae h hh t ψ,
      stoneMulGroup_apply_ae h hh t (lpMulOpOfBound f hf C hC ψ),
      lpMulOpOfBound_apply_ae f hf C hC ψ] with x h1 h2 h3 h4
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, h3, h4]
    exact mul_left_comm (f x) (Complex.exp (Complex.I * (t : ℂ) * (h x : ℂ))) (ψ x)

theorem t3_13_f12_f10 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : α → ℝ) (hh : Measurable h) (s t : ℝ)
    {n : ℕ} (E_ψ E_φ : ExpDensityFactor n) :
    stoneMulGroup (α := α) (μ := μ) h hh (s + t) =
        stoneMulGroup h hh s ∘L stoneMulGroup h hh t ∧
      relConnesCocycle E_ψ E_φ (s + t) =
        relConnesCocycle E_ψ E_φ s * E_φ.modularFlow s (relConnesCocycle E_ψ E_φ t) :=
  ⟨stoneMulGroup_add h hh s t, relConnesCocycle_cocycle_id E_ψ E_φ s t⟩

theorem t3_14_f13_f14 :
    commutant (ComplexMatrixTomitaDuality.leftRegSet 2) =
        ComplexMatrixTomitaDuality.rightRegSet 2 ∧
      stage1DiagTomitaAndKMSBridge.kmsState.state 1 = 1 ∧
      ((conjByCLM diag2CentralizerU).restrictScalars ℝ).comp
          (rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
            (tomitaRealSubspace diag2DensityFactor)) =
        (rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor)).comp
          ((conjByCLM diag2CentralizerU).restrictScalars ℝ) :=
  ⟨fullLeftReg_commutant_eq_rightReg 2, stage1DiagTomitaAndKMSBridge.kmsState.state_one,
    diag2_centralizer_commutes_rvd.2.2.1⟩

theorem t3_15_f5_f12 {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type _) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : α → ℝ) (hh : Measurable h) (ψ : L2c α μ) :
    ‖tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i‖ ≤ 1 ∧
      Continuous (fun t : ℝ => stoneMulGroup (α := α) (μ := μ) h hh t ψ) :=
  ⟨tomitaGraphDom_to_modularHilbertCompletion_norm_le Stage sys ω hclos i,
    stoneMulGroup_continuous h hh ψ⟩

end Tier3_CrossFeature

/-! ## Tier 4: Real-World Operator-Algebraic E2E Scenarios (`S1`–`S7`) -/

section S1_Scenario

set_option maxHeartbeats 2500000 in
theorem s1_matrix_standard_form_commutant_rvd_e2e
    (x : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
    IsStandardSubspace (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
        (tomitaRealSubspace diag2DensityFactor) ∧
      (0 ≤ (⟪x, rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor) x⟫_ℂ).re ∧
        (⟪x, rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor) x⟫_ℂ).re ≤ 2 * ‖x‖ ^ 2) ∧
      commutant (ComplexMatrixTomitaDuality.leftRegSet 2) =
        ComplexMatrixTomitaDuality.rightRegSet 2 ∧
      commutant {ComplexMatrixTomitaDuality.leftMul 2 witnessE01} ≠
        ComplexMatrixTomitaDuality.rightRegSet 2 ∧
      ((conjByCLM diag2CentralizerU).restrictScalars ℝ).comp
          (rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
            (tomitaRealSubspace diag2DensityFactor)) =
        (rvdR (H := EuclideanSpace ℂ (Fin 2 × Fin 2))
          (tomitaRealSubspace diag2DensityFactor)).comp
          ((conjByCLM diag2CentralizerU).restrictScalars ℝ) := by
  have h1 := tomitaRealSubspace_isStandard diag2DensityFactor
  have h2 := rvdR_inner_re_bounds (tomitaRealSubspace diag2DensityFactor) x
  have h3 := fullLeftReg_commutant_eq_rightReg 2
  have h4 := single_leftMul_commutant_ne_rightRegSet
  have h5 := diag2_centralizer_commutes_rvd.2.2.1
  exact ⟨h1, h2, h3, h4, h5⟩

end S1_Scenario

section S2_Scenario

theorem s2_filtered_gns_friedrichs_completion_e2e
    {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type _) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) {i j : I} (hij : i ≤ j)
    (ξ : (ω.state i).functional.GNS) (x : TomitaGraphDom (ω.state i) (hclos i)) :
    DenseRange (tomitaFormResolventCLM (ω.state i) (hclos i)) ∧
      ‖tomitaSCompResolventRLM (ω.state i) (hclos i) ξ‖ ≤ ‖ξ‖ ∧
      ‖tomitaFormComplementaryResolventCLM (ω.state i) (hclos i) ξ‖ ≤ ‖ξ‖ ∧
      ‖gns_to_modularHilbertCompletion_via_resolvent Stage sys ω hclos i ξ‖ ≤ ‖ξ‖ ∧
      tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos j
          (filteredTomitaGraphDomMap Stage sys ω hclos hij x) =
        tomitaGraphDom_to_modularHilbertCompletion Stage sys ω hclos i x :=
  ⟨tomitaFormResolvent_denseRange (ω.state i) (hclos i),
    tomitaSCompResolventRLM_norm_apply_le (ω.state i) (hclos i) ξ,
    tomitaFormComplementaryResolventCLM_norm_le (ω.state i) (hclos i) ξ,
    gns_to_modularHilbertCompletion_via_resolvent_apply_norm_le Stage sys ω hclos i ξ,
    tomitaGraphDom_to_modularHilbertCompletion_compat Stage sys ω hclos hij x⟩

end S2_Scenario

section S3_Scenario

theorem s3_nonabelian_crossed_product_covariant_dual_e2e
    (a : Matrix (Fin 2) (Fin 2) ℂ) (g : DihedralGroup 4)
    (χ₁ χ₂ : DihedralGroup 4 →* unitary ℂ) :
    embedGroup (θ := dihedral4Action) g * embedAlg a * star (embedGroup g) =
        embedAlg (dihedral4Action g a) ∧
      witnessCovariantLift (embedAlg a) = a ∧
      witnessCovariantLift (embedGroup g) =
        (dihedral4UnitaryHom g : Matrix (Fin 2) (Fin 2) ℂ) ∧
      dualActionAut (θ := dihedral4Action) (χ₁ * χ₂) =
        dualActionAut χ₁ * dualActionAut χ₂ ∧
      (∃ x y : WitnessCrossedProduct, x * y ≠ y * x) :=
  ⟨covariant_relation g a,
    covariantLift_embedAlg _ _ _ a,
    covariantLift_embedGroup _ _ _ g,
    (dualActionHom (θ := dihedral4Action)).map_mul χ₁ χ₂,
    witness_noncommutative⟩

end S3_Scenario

section S4_Scenario

theorem s4_powers_one_third_spectrum_closure_boundary_e2e (k : ℕ) (A B : UHFStage k) :
    (0 : ℝ) ∉ powersPointSpec (1 / 3 : ℝ) ∧
      (0 : ℝ) ∈ closure (powersPointSpec (1 / 3 : ℝ)) ∧
      closure (powersPointSpec (1 / 3 : ℝ)) =
        insert (0 : ℝ) (powersPointSpec (1 / 3 : ℝ)) ∧
      powersState (1 / 3 : ℝ) k (A * powersModularOp (1 / 3 : ℝ) k B) =
        powersState (1 / 3 : ℝ) k (B * A) ∧
      uhfStageNormTrace k (A * B) = uhfStageNormTrace k (B * A) ∧
      commutant (ComplexMatrixTomitaDuality.leftRegSet (2 ^ k)) =
        ComplexMatrixTomitaDuality.rightRegSet (2 ^ k) :=
  ⟨zero_notMem_powersPointSpec (by norm_num),
    zero_mem_closure_powersPointSpec (by norm_num) (by norm_num),
    closure_powersPointSpec_eq_insert_zero (by norm_num) (by norm_num),
    powersState_kms (by norm_num) k A B,
    uhfStageNormTrace_comm k A B,
    fullLeftReg_commutant_eq_rightReg (2 ^ k)⟩

end S4_Scenario

section S5_Scenario

theorem s5_two_density_noncommuting_rn_intertwining_e2e (s t : ℝ)
    (A X : Matrix (Fin 2) (Fin 2) ℂ) :
    witnessRhoPsi * witnessRhoPhi ≠ witnessRhoPhi * witnessRhoPsi ∧
      relTomitaOp witnessExpPsi.toPositiveComplexDensityFactor
          witnessExpPhi.toPositiveComplexDensityFactor X =
        matrixJ 2 (relModularSqrt witnessExpPsi.toPositiveComplexDensityFactor
          witnessExpPhi.toPositiveComplexDensityFactor X) ∧
      relConnesCocycle witnessExpPsi witnessExpPhi (s + t) =
        relConnesCocycle witnessExpPsi witnessExpPhi s *
          witnessExpPhi.modularFlow s (relConnesCocycle witnessExpPsi witnessExpPhi t) ∧
      witnessExpPsi.modularFlow t A =
        relConnesCocycle witnessExpPsi witnessExpPhi t * witnessExpPhi.modularFlow t A *
          (relConnesCocycle witnessExpPsi witnessExpPhi t)ᴴ ∧
      commutant (ComplexMatrixTomitaDuality.leftRegSet 2) =
        JConjugateSet (ComplexMatrixTomitaDuality.matrixJ 2)
          (ComplexMatrixTomitaDuality.leftRegSet 2) :=
  ⟨witnessRhoPsi_mul_witnessRhoPhi_ne,
    relTomitaOp_polar _ _ X,
    relConnesCocycle_cocycle_id witnessExpPsi witnessExpPhi s t,
    relConnesCocycle_intertwines witnessExpPsi witnessExpPhi t A,
    fullLeftReg_commutant_eq_JConjugate 2⟩

end S5_Scenario

section S6_Scenario

theorem s6_l2_pvm_stone_spectral_evolution_e2e
    (S : ℕ → Set ℝ) (hS : ∀ n, MeasurableSet (S n)) (hdisj : Pairwise (Disjoint on S))
    (h : ℝ → ℝ) (hh : Measurable h) (t : ℝ) (ψ : L2c ℝ volume) :
    Tendsto
        (fun N => ∑ n ∈ Finset.range N,
          pvmProj (α := ℝ) (μ := volume) (S n) (hS n) ψ)
        atTop
        (𝓝 (pvmProj (α := ℝ) (μ := volume) (⋃ n, S n) (MeasurableSet.iUnion hS) ψ)) ∧
      stoneMulGroup (α := ℝ) (μ := volume) h hh t ∈
        unitary (L2c ℝ volume →L[ℂ] L2c ℝ volume) ∧
      Continuous (fun r : ℝ => stoneMulGroup (α := ℝ) (μ := volume) h hh r ψ) ∧
      pvmProj (α := ℝ) (μ := volume) (S 0) (hS 0) ∘L
          stoneMulGroup (α := ℝ) (μ := volume) h hh t =
        stoneMulGroup (α := ℝ) (μ := volume) h hh t ∘L
          pvmProj (α := ℝ) (μ := volume) (S 0) (hS 0) :=
  ⟨pvmProj_countable_add S hS hdisj ψ,
    stoneMulGroup_unitary h hh t,
    stoneMulGroup_continuous h hh ψ,
    (t3_12_f11_f12_commute _ (aestronglyMeasurable_const.indicator (hS 0)) 1
      (Eventually.of_forall fun x => by by_cases hx : x ∈ S 0 <;> simp [hx])
      (S 0) (hS 0) h hh t).2⟩

end S6_Scenario

section S7_Scenario

theorem s7_cross_frontier_kms_stone_connes_integration_e2e
    {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type _) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    (hclos : ∀ i, IsClosableTomitaCore (ω.state i)) (i : I)
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : α → ℝ) (hh : Measurable h) (t : ℝ) (ψ : L2c α μ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖gns_to_modularHilbertCompletion_via_resolvent Stage sys ω hclos i‖ ≤ 1 ∧
      stage1DiagTomitaAndKMSBridge.kmsState.state 1 = 1 ∧
      witnessExpPsi.modularFlow t A =
        relConnesCocycle witnessExpPsi witnessExpPhi t * witnessExpPhi.modularFlow t A *
          (relConnesCocycle witnessExpPsi witnessExpPhi t)ᴴ ∧
      stoneMulGroup (α := α) (μ := μ) h hh t ∈ unitary (L2c α μ →L[ℂ] L2c α μ) ∧
      Continuous (fun r : ℝ => stoneMulGroup (α := α) (μ := μ) h hh r ψ) :=
  ⟨gns_to_modularHilbertCompletion_via_resolvent_norm_le Stage sys ω hclos i,
    stage1DiagTomitaAndKMSBridge.kmsState.state_one,
    relConnesCocycle_intertwines witnessExpPsi witnessExpPhi t A,
    stoneMulGroup_unitary h hh t,
    stoneMulGroup_continuous h hh ψ⟩

end S7_Scenario

/-! ## Tier 5: Adversarial Coverage Hardening (`M1`–`M6`) -/

section Tier5_Adversarial

/-! ### `M1` (`RieffelVanDaeleBoundedTomita`): Concrete Non-Orthogonal `tiltedK` Witness -/

def tiltedK : Submodule ℝ (EuclideanSpace ℂ (Fin 2)) where
  carrier := {v | v 1 = (2 : ℂ) * star (v 0)}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy => by
    change x 1 + y 1 = (2 : ℂ) * star (x 0 + y 0)
    rw [hx, hy, star_add, mul_add]
  smul_mem' := fun c {x} hx => by
    change (c : ℂ) * x 1 = (2 : ℂ) * star ((c : ℂ) * x 0)
    rw [hx, star_mul', Complex.star_def, Complex.conj_ofReal]
    ring

theorem mem_tiltedK_iff (v : EuclideanSpace ℂ (Fin 2)) :
    v ∈ tiltedK ↔ v 1 = (2 : ℂ) * star (v 0) :=
  Iff.rfl

theorem isClosed_tiltedK : IsClosed (tiltedK : Set (EuclideanSpace ℂ (Fin 2))) :=
  Submodule.closed_of_finiteDimensional tiltedK

instance : CompleteSpace tiltedK :=
  isClosed_tiltedK.completeSpace_coe

instance : CompleteSpace (ImaginarySubmodule (H := EuclideanSpace ℂ (Fin 2)) tiltedK) :=
  completeSpace_imaginarySubmodule (H := EuclideanSpace ℂ (Fin 2)) tiltedK

theorem tiltedK_isStandard :
    IsStandardSubspace (H := EuclideanSpace ℂ (Fin 2)) tiltedK := by
  constructor
  · have htop :
        tiltedK ⊔ ImaginarySubmodule (H := EuclideanSpace ℂ (Fin 2)) tiltedK = ⊤ := by
      rw [eq_top_iff]
      intro v _
      let k0 : ℂ := (1 / 2 : ℂ) * (v 0 + (1 / 2 : ℂ) * star (v 1))
      let k'0 : ℂ := (-Complex.I / 2 : ℂ) * (v 0 - (1 / 2 : ℂ) * star (v 1))
      let k : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![k0, (2 : ℂ) * star k0]
      let k' : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![k'0, (2 : ℂ) * star k'0]
      have hk : k ∈ tiltedK := rfl
      have hk' : (Complex.I : ℂ) • k' ∈
          ImaginarySubmodule (H := EuclideanSpace ℂ (Fin 2)) tiltedK := by
        rw [mem_imaginarySubmodule_iff]
        have hinv : (-Complex.I : ℂ) • ((Complex.I : ℂ) • k') = k' := by
          rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
        rw [hinv]
        exact rfl
      have hsum : k + (Complex.I : ℂ) • k' = v := by
        ext i
        fin_cases i
        · change k0 + Complex.I * k'0 = v 0
          dsimp [k0, k'0]
          calc
            (1 / 2 : ℂ) * (v 0 + 1 / 2 * star (v 1)) +
                Complex.I * (-Complex.I / 2 * (v 0 - 1 / 2 * star (v 1)))
                = (1 / 2 : ℂ) * (v 0 + 1 / 2 * star (v 1)) -
                    (Complex.I * Complex.I) / 2 * (v 0 - 1 / 2 * star (v 1)) := by ring
            _ = (1 / 2 : ℂ) * (v 0 + 1 / 2 * star (v 1)) +
                    (1 / 2 : ℂ) * (v 0 - 1 / 2 * star (v 1)) := by
                  rw [Complex.I_mul_I]; ring
            _ = v 0 := by ring
        · change (2 : ℂ) * star k0 + Complex.I * ((2 : ℂ) * star k'0) = v 1
          dsimp [k0, k'0]
          simp only [map_mul, map_add, map_sub, map_div₀, map_neg, map_one, map_ofNat,
            Complex.conj_I, RingHomCompTriple.comp_apply, RingHom.id_apply]
          ring_nf
          rw [Complex.I_sq]
          ring
      rw [Submodule.mem_sup]
      exact ⟨k, hk, (Complex.I : ℂ) • k', hk', hsum⟩
    rw [htop]
    simp [dense_univ]
  · rw [eq_bot_iff]
    intro v hv
    rcases Submodule.mem_inf.mp hv with ⟨h1, h2⟩
    rw [mem_imaginarySubmodule_iff] at h2
    rw [mem_tiltedK_iff] at h1 h2
    have h2' : (-Complex.I : ℂ) * v 1 = (2 : ℂ) * star ((-Complex.I : ℂ) * v 0) := h2
    rw [h1] at h2'
    have hstar : star ((-Complex.I : ℂ) * v 0) = Complex.I * starRingEnd ℂ (v 0) := by
      rw [star_mul', Complex.star_def, map_neg, Complex.conj_I, neg_neg]
    rw [hstar] at h2'
    have h4 : (4 : ℂ) * Complex.I * starRingEnd ℂ (v 0) = 0 := by
      have : (-Complex.I : ℂ) * ((2 : ℂ) * star (v 0)) -
          (2 : ℂ) * (Complex.I * starRingEnd ℂ (v 0)) = 0 := sub_eq_zero.mpr h2'
      calc
        (4 : ℂ) * Complex.I * starRingEnd ℂ (v 0)
            = -((-Complex.I : ℂ) * ((2 : ℂ) * star (v 0)) -
                (2 : ℂ) * (Complex.I * starRingEnd ℂ (v 0))) := by
              change _ = -((-Complex.I : ℂ) * ((2 : ℂ) * starRingEnd ℂ (v 0)) -
                (2 : ℂ) * (Complex.I * starRingEnd ℂ (v 0)))
              ring
        _ = 0 := by rw [this, neg_zero]
    have h4I : (4 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
    have hv0 : v 0 = 0 := by
      have hs : starRingEnd ℂ (v 0) = 0 :=
        (mul_eq_zero.mp (by simpa [mul_assoc] using h4)).resolve_left h4I
      simpa using congrArg star hs
    have hv1 : v 1 = 0 := by simpa [hv0] using h1
    ext i
    fin_cases i
    · exact hv0
    · exact hv1

theorem projK_tiltedK_apply (v : EuclideanSpace ℂ (Fin 2)) :
    projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK v =
      let a := (1 / 5 : ℂ) * (v 0 + (2 : ℂ) * star (v 1))
      WithLp.toLp 2 ![a, (2 : ℂ) * star a] := by
  let : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin 2)) :=
    InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin 2))
  let a : ℂ := (1 / 5 : ℂ) * (v 0 + (2 : ℂ) * star (v 1))
  let w : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![a, (2 : ℂ) * star a]
  change tiltedK.starProjection v = w
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero rfl ?_
  intro y hy
  rw [mem_tiltedK_iff] at hy
  change (⟪v - w, y⟫_ℂ).re = 0
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, PiLp.sub_apply, w,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.star_def]
  rw [hy]
  change (y 0 * starRingEnd ℂ (v 0 - a) +
    (2 * starRingEnd ℂ (y 0)) * starRingEnd ℂ (v 1 - 2 * starRingEnd ℂ a)).re = 0
  rw [Complex.add_re]
  have h2' : ((2 * starRingEnd ℂ (y 0)) * starRingEnd ℂ (v 1 - 2 * starRingEnd ℂ a)).re =
      (y 0 * (2 * v 1 - 4 * starRingEnd ℂ a)).re := by
    rw [← Complex.conj_re
      ((2 * starRingEnd ℂ (y 0)) * starRingEnd ℂ (v 1 - 2 * starRingEnd ℂ a))]
    congr 1
    simp only [map_mul, map_sub, map_ofNat, Complex.conj_conj]
    ring
  rw [h2', ← Complex.add_re]
  have hzero : starRingEnd ℂ (v 0 - a) + (2 * v 1 - 4 * starRingEnd ℂ a) = 0 := by
    dsimp [a]
    simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat, map_add, Complex.conj_conj]
    ring
  have hprod : y 0 * starRingEnd ℂ (v 0 - a) + y 0 * (2 * v 1 - 4 * starRingEnd ℂ a) =
      y 0 * (starRingEnd ℂ (v 0 - a) + (2 * v 1 - 4 * starRingEnd ℂ a)) := by
    ring
  rw [hprod, hzero, mul_zero, Complex.zero_re]

theorem projIK_tiltedK_apply (v : EuclideanSpace ℂ (Fin 2)) :
    projIK (H := EuclideanSpace ℂ (Fin 2)) tiltedK v =
      (Complex.I : ℂ) • projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK ((-Complex.I : ℂ) • v) := by
  have h := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) =>
    f ((-Complex.I : ℂ) • v)) (IMapCLM_comp_projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK)
  have hinv : IMapCLM (EuclideanSpace ℂ (Fin 2)) ((-Complex.I : ℂ) • v) = v :=
    (IMapLIE (EuclideanSpace ℂ (Fin 2))).right_inv v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hinv] at h
  exact h.symm

def tiltedE0 : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(1 : ℂ), 0]

theorem tiltedK_rvdR_e0 :
    rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK tiltedE0 =
      WithLp.toLp 2 ![(2 / 5 : ℂ), 0] := by
  rw [rvdR_apply, projIK_tiltedK_apply, projK_tiltedK_apply, projK_tiltedK_apply]
  ext i
  fin_cases i <;> (simp [tiltedE0, PiLp.smul_apply]; ring_nf; rw [Complex.I_sq]; norm_num)

theorem tiltedK_rvdT_e0 :
    rvdT (H := EuclideanSpace ℂ (Fin 2)) tiltedK tiltedE0 =
      WithLp.toLp 2 ![0, (4 / 5 : ℂ)] := by
  rw [rvdT_apply, projIK_tiltedK_apply, projK_tiltedK_apply, projK_tiltedK_apply]
  ext i
  fin_cases i <;> (simp [tiltedE0, PiLp.smul_apply]; ring_nf; rw [Complex.I_sq]; norm_num)

def tiltedJ : EuclideanSpace ℂ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun v := WithLp.toLp 2 ![star (v 1), star (v 0)]
  invFun v := WithLp.toLp 2 ![star (v 1), star (v 0)]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [Complex.real_smul]
  norm_map' x := by
    simp only [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    congr 1
    change ‖star (x 1)‖ ^ 2 + ‖star (x 0)‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2
    rw [norm_star, norm_star, add_comm]

theorem tiltedK_symplComp_eq_map :
    tiltedK.map (tiltedJ.toLinearEquiv :
        EuclideanSpace ℂ (Fin 2) →ₗ[ℝ] EuclideanSpace ℂ (Fin 2)) =
      symplCompSubmodule (H := EuclideanSpace ℂ (Fin 2)) tiltedK := by
  ext w
  rw [Submodule.mem_map, mem_symplCompSubmodule_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ y hy
    rw [mem_tiltedK_iff] at hv hy
    change (⟪y, tiltedJ v⟫_ℂ).im = 0
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, tiltedJ,
      LinearIsometryEquiv.coe_mk]
    change (star (v 1) * starRingEnd ℂ (y 0) + star (v 0) * starRingEnd ℂ (y 1)).im = 0
    rw [hy, hv]
    simp only [Complex.star_def, map_mul, map_ofNat, Complex.conj_conj]
    have him1 : (2 * v 0 * starRingEnd ℂ (y 0) + starRingEnd ℂ (v 0) * (2 * y 0)).im = 0 := by
      have hconj : starRingEnd ℂ (2 * v 0 * starRingEnd ℂ (y 0)) =
          starRingEnd ℂ (v 0) * (2 * y 0) := by
        simp only [map_mul, map_ofNat, Complex.conj_conj]; ring
      rw [← hconj]
      simp only [Complex.add_im, Complex.conj_im, Complex.mul_im]
      ring
    simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using him1
  · intro hw
    have hw1 := hw (WithLp.toLp 2 ![(1 : ℂ), (2 : ℂ)]) (by simp [mem_tiltedK_iff])
    have hw2 := hw (WithLp.toLp 2 ![Complex.I, -(2 : ℂ) * Complex.I])
      (by simp [mem_tiltedK_iff])
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hw1 hw2
    have hre : (w 0).re = 2 * (w 1).re := by
      simp [Complex.add_im, Complex.mul_im] at hw2
      linarith
    have him : (w 0).im = -2 * (w 1).im := by
      simp [Complex.add_im, Complex.mul_im] at hw1
      linarith
    have hw0 : w 0 = 2 * star (w 1) := by
      refine Complex.ext ?_ ?_
      · simpa using hre
      · simpa using him
    refine ⟨tiltedJ w, ?_, tiltedJ.right_inv w⟩
    rw [mem_tiltedK_iff]
    change star (w 0) = 2 * star (star (w 1))
    rw [hw0]
    simp

theorem t5_m1_tiltedK_noncomm_and_bounds :
    ((projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK).comp
        (projIK (H := EuclideanSpace ℂ (Fin 2)) tiltedK) ≠
      (projIK (H := EuclideanSpace ℂ (Fin 2)) tiltedK).comp
        (projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK)) ∧
      rvdT (H := EuclideanSpace ℂ (Fin 2)) tiltedK ≠ 0 ∧
      rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK ≠ 1 ∧
      0 < (⟪tiltedE0, rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK tiltedE0⟫_ℂ).re ∧
      (⟪tiltedE0, rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK tiltedE0⟫_ℂ).re <
        2 * ‖tiltedE0‖ ^ 2 ∧
      rvdT (H := EuclideanSpace ℂ (Fin 2)) tiltedK *
          rvdT (H := EuclideanSpace ℂ (Fin 2)) tiltedK =
        rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK *
          ((2 : ℝ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2)) -
            rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rvdT_sq_eq tiltedK⟩
  · intro h
    have h1 := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) =>
      f tiltedE0 1) h
    simp only [ContinuousLinearMap.comp_apply, projIK_tiltedK_apply, projK_tiltedK_apply] at h1
    simp only [tiltedE0, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.star_def, map_mul, map_add, map_neg, map_div₀, map_one, map_ofNat, map_zero,
      Complex.conj_I, mul_zero, add_zero, mul_one] at h1
    ring_nf at h1
    rw [Complex.I_sq] at h1
    norm_num at h1
  · intro h
    have h0 := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) =>
      f tiltedE0 1) h
    rw [tiltedK_rvdT_e0] at h0
    simp at h0
  · intro h
    have h0 := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) =>
      f tiltedE0 0) h
    rw [tiltedK_rvdR_e0] at h0
    simp [tiltedE0] at h0
    norm_num at h0
  · rw [tiltedK_rvdR_e0]
    simp [tiltedE0, PiLp.inner_apply, Fin.sum_univ_two]
  · rw [tiltedK_rvdR_e0]
    have hnorm : ‖tiltedE0‖ ^ 2 = 1 := by
      simp [tiltedE0, EuclideanSpace.norm_sq_eq]
    rw [hnorm]
    simp [tiltedE0, PiLp.inner_apply, Fin.sum_univ_two]
    norm_num

theorem t5_m1_tiltedK_intertwining_kernels_and_J :
    ((IMapCLM (EuclideanSpace ℂ (Fin 2))).comp (rvdR tiltedK) =
        (rvdR tiltedK).comp (IMapCLM (EuclideanSpace ℂ (Fin 2)))) ∧
      ((IMapCLM (EuclideanSpace ℂ (Fin 2))).comp (rvdT tiltedK) =
        -((rvdT tiltedK).comp (IMapCLM (EuclideanSpace ℂ (Fin 2))))) ∧
      Function.Injective (rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK) ∧
      Function.Injective
        ((2 : ℝ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2)) -
          rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK) ∧
      symplCompSubmodule (H := EuclideanSpace ℂ (Fin 2)) tiltedK ≠ tiltedK ∧
      ((tiltedJ.toContinuousLinearEquiv :
            EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2)) *
          rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK *
          (tiltedJ.toContinuousLinearEquiv :
            EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2)) =
        (2 : ℝ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2)) -
          rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK) ∧
      ((2 : ℝ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2)) -
        rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK ≠
        rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK) := by
  refine ⟨IMapCLM_comp_rvdR tiltedK, IMapCLM_comp_rvdT tiltedK,
    rvdR_injective tiltedK tiltedK_isStandard,
    two_sub_rvdR_injective tiltedK tiltedK_isStandard, ?_, ?_, ?_⟩
  · intro h
    have hv : WithLp.toLp 2 ![(1 : ℂ), (2 : ℂ)] ∈ tiltedK := by simp [mem_tiltedK_iff]
    rw [← h, mem_symplCompSubmodule_iff] at hv
    have him := hv (WithLp.toLp 2 ![Complex.I, -(2 : ℂ) * Complex.I])
      (by simp [mem_tiltedK_iff])
    simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two] at him
    norm_num at him
  · exact j_conj_rvdR tiltedK tiltedJ (fun v => tiltedJ.left_inv v)
      (fun x => by ext i; fin_cases i <;> simp [tiltedJ]) tiltedK_symplComp_eq_map
  · intro h
    have h0 := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) =>
      f tiltedE0 0) h
    change ((2 : ℝ) • tiltedE0 - rvdR tiltedK tiltedE0) 0 = (rvdR tiltedK tiltedE0) 0 at h0
    rw [tiltedK_rvdR_e0] at h0
    simp [tiltedE0] at h0
    norm_num at h0

/-! ### `M2` (`FilteredGNSTomitaFriedrichsResolvent`): Off-Diagonal `CStarMatrixStage` Witness -/

section Tier5_M2

open scoped ComplexOrder
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.AlgebraicKMSStateColimit
open InfoGeometry.Canonical.FiniteSeedGibbsTomitaClosability

local instance t5CStarMatrixRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrixStage n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance t5CStarMatrixNonnegSpectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (CStarMatrixStage n) :=
  CStarAlgebra.instNonnegSpectrumClass

def tier5OffDiagH : MatrixStage 1 := Matrix.of ![![(0 : ℂ), 1], ![1, 0]]

theorem tier5OffDiagH_isHermitian : tier5OffDiagH.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tier5OffDiagH, Matrix.conjTranspose_apply]

theorem tier5OffDiagH_nonDiag : tier5OffDiagH 0 1 ≠ 0 := by
  simp [tier5OffDiagH]

theorem t5_m2_cstarMatrixStage_offDiag_resolvent :
    let ω := finiteSeedCompatibleStageStates tier5OffDiagH tier5OffDiagH_isHermitian 1
    let hclos := finiteSeedCompatibleStageStates_closable tier5OffDiagH tier5OffDiagH_isHermitian 1
    let A1 : CStarMatrixStage 1 :=
      CStarMatrix.ofMatrixStarAlgEquiv (Matrix.of ![![(0 : ℂ), 1], ![0, 0]])
    let ξ1 : (ω.state 1).functional.GNS :=
      (((ω.state 1).functional.toPreGNS A1 : (ω.state 1).functional.PreGNS) :
        (ω.state 1).functional.GNS)
    let ξ0 : (ω.state 0).functional.GNS :=
      (((ω.state 0).functional.toPreGNS (1 : CStarMatrixStage 0) :
        (ω.state 0).functional.PreGNS) :
        (ω.state 0).functional.GNS)
    ξ1 ≠ 0 ∧
      0 < (inner ℂ ξ1 (tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1)).re ∧
      (inner ℂ ξ1 (tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1)).re < ‖ξ1‖ ^ 2 ∧
      0 < (inner ℂ ξ1
        (tomitaFormComplementaryResolventCLM (ω.state 1) (hclos 1) ξ1)).re ∧
      tomitaSCompResolventRLM (ω.state 1) (hclos 1) ξ1 ≠ 0 ∧
      0 < ‖tomitaSCompResolventRLM (ω.state 1) (hclos 1) ξ1‖ ∧
      graphDomInclCLM (ω.state 1) (hclos 1)
          (filteredTomitaGraphDomMap CStarMatrixStage cstarMatrixInductiveSystem ω hclos
            (Nat.zero_le 1) (tomitaFormResolventDomCLM (ω.state 0) (hclos 0) ξ0)) =
        filteredGNSLinearIsometry CStarMatrixStage cstarMatrixInductiveSystem ω (Nat.zero_le 1)
          (tomitaFormResolventCLM (ω.state 0) (hclos 0) ξ0) ∧
      (inner ℂ ξ0 (tomitaFormResolventCLM (ω.state 0) (hclos 0) ξ0)).re ≤
        (inner ℂ
          (filteredGNSLinearIsometry CStarMatrixStage cstarMatrixInductiveSystem ω
            (Nat.zero_le 1) ξ0)
          (tomitaFormResolventCLM (ω.state 1) (hclos 1)
            (filteredGNSLinearIsometry CStarMatrixStage cstarMatrixInductiveSystem ω
              (Nat.zero_le 1) ξ0))).re := by
  intro ω hclos A1 ξ1 ξ0
  have hAne : A1 ≠ 0 := by
    intro h
    have h0 := congrArg (fun X : CStarMatrixStage 1 =>
      ((CStarMatrix.ofMatrixStarAlgEquiv).symm X) 0 1) h
    simp [A1] at h0
  have hstarAne : star A1 ≠ 0 := fun h => hAne (by simpa using congrArg star h)
  have hpre_ne : ∀ B : CStarMatrixStage 1, B ≠ 0 →
      (((ω.state 1).functional.toPreGNS B : (ω.state 1).functional.PreGNS) :
        (ω.state 1).functional.GNS) ≠ 0 := by
    intro B hBne h0
    have hn := congrArg norm h0
    rw [UniformSpace.Completion.norm_coe, norm_zero] at hn
    have hs := (ω.state 1).functional.preGNS_norm_sq ((ω.state 1).functional.toPreGNS B)
    rw [hn, Complex.ofReal_zero, zero_pow (by decide)] at hs
    have hs0 : (ω.state 1).functional (star B * B) = 0 := by
      simpa only [Complex.ofReal_zero, PositiveLinearMap.ofPreGNS_toPreGNS] using hs.symm
    have hs' : ((finiteSeedStageState tier5OffDiagH tier5OffDiagH_isHermitian 1 1).functional
        (star B * B)) = 0 := hs0
    have hB0 := (finiteSeedStageState_faithful tier5OffDiagH tier5OffDiagH_isHermitian 1 1 B).mp hs'
    exact hBne hB0
  have hξne : ξ1 ≠ 0 := hpre_ne A1 hAne
  have hS_ne : tomitaSCompResolventRLM (ω.state 1) (hclos 1) ξ1 ≠ 0 := by
    intro hS0
    have hRξ : tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1 = ξ1 := by
      have hsub : ξ1 - tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1 = 0 := by
        apply (dense_closedTomitaDomain (ω.state 1) (hclos 1)).eq_zero_of_inner_right ℂ
        intro y hy
        have hv := tomitaFormResolvent_variational (ω.state 1) (hclos 1) ξ1 ⟨⟨y, hy⟩⟩
        have hS0' : closedTomitaOperator (ω.state 1) (hclos 1)
            (tomitaFormResolventDomCLM (ω.state 1) (hclos 1) ξ1).val = 0 := by
          simpa only [tomitaSCompResolventRLM_apply] using hS0
        rw [hS0', inner_zero_right, add_zero] at hv
        have hv' : inner ℂ y (tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1) =
            inner ℂ y ξ1 := by
          rw [← inner_conj_symm, hv, inner_conj_symm]
        rw [inner_sub_right]
        exact sub_eq_zero.mpr hv'.symm
      exact (sub_eq_zero.mp hsub).symm
    let y : TomitaGraphDom (ω.state 1) (hclos 1) :=
      ⟨⟨ξ1, ⟨(tomitaCore (ω.state 1) ((ω.state 1).functional.toPreGNS A1) :
        (ω.state 1).functional.GNS),
        subset_closure ⟨(ω.state 1).functional.toPreGNS A1, rfl⟩⟩⟩⟩
    have hdom : tomitaFormResolventDomCLM (ω.state 1) (hclos 1) ξ1 = y := by
      apply TomitaGraphDom.ext
      apply Subtype.ext
      simpa only [tomitaFormResolventCLM_apply] using hRξ
    have hSy : closedTomitaOperator (ω.state 1) (hclos 1) y.val =
        (((ω.state 1).functional.toPreGNS (star A1) : (ω.state 1).functional.PreGNS) :
          (ω.state 1).functional.GNS) := by
      change closedTomitaValue (ω.state 1) y.val = _
      have heq := closedTomitaValue_eq_of_mem (ω.state 1) (hclos 1) y.val
        (tomitaCore (ω.state 1) ((ω.state 1).functional.toPreGNS A1) :
          (ω.state 1).functional.GNS)
        (subset_closure ⟨(ω.state 1).functional.toPreGNS A1, rfl⟩)
      simpa [tomitaCore_toPreGNS] using heq
    have hzero : (((ω.state 1).functional.toPreGNS (star A1) : (ω.state 1).functional.PreGNS) :
        (ω.state 1).functional.GNS) = 0 := by
      rw [← hSy, ← hdom]
      simpa only [tomitaSCompResolventRLM_apply] using hS0
    exact hpre_ne (star A1) hstarAne hzero
  have hcomp_eq : (inner ℂ ξ1
      (tomitaFormComplementaryResolventCLM (ω.state 1) (hclos 1) ξ1)).re =
      ‖ξ1‖ ^ 2 - (inner ℂ ξ1 (tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1)).re := by
    rw [tomitaFormComplementaryResolventCLM, _root_.sub_apply, ContinuousLinearMap.id_apply,
      inner_sub_right, Complex.sub_re, ← RCLike.re_to_complex,
      ← InnerProductSpace.norm_sq_eq_re_inner]
  have hcomp_pos : 0 < (inner ℂ ξ1
      (tomitaFormComplementaryResolventCLM (ω.state 1) (hclos 1) ξ1)).re := by
    have hsub : (inner ℂ ξ1
        (tomitaFormComplementaryResolventCLM (ω.state 1) (hclos 1) ξ1)).re =
        ‖ξ1 - tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1‖ ^ 2 +
          ‖tomitaSCompResolventRLM (ω.state 1) (hclos 1) ξ1‖ ^ 2 := by
      have he := tomitaFormResolvent_energy (ω.state 1) (hclos 1) ξ1
      have hnorm_sub : ‖ξ1 - tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1‖ ^ 2 =
          ‖ξ1‖ ^ 2 - 2 * (inner ℂ ξ1
            (tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1)).re +
          ‖tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1‖ ^ 2 := by
        rw [norm_sub_sq (𝕜 := ℂ), RCLike.re_to_complex]
      change _ = ‖ξ1 - tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1‖ ^ 2 +
        ‖closedTomitaOperator (ω.state 1) (hclos 1)
          (tomitaFormResolventDomCLM (ω.state 1) (hclos 1) ξ1).val‖ ^ 2
      linarith
    rw [hsub]
    have hSpos : 0 < ‖tomitaSCompResolventRLM (ω.state 1) (hclos 1) ξ1‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hS_ne)
    linarith [sq_nonneg ‖ξ1 - tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1‖]
  have hR_pos : 0 < (inner ℂ ξ1 (tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1)).re := by
    have he := tomitaFormResolvent_energy (ω.state 1) (hclos 1) ξ1
    have hRne : tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1 ≠ 0 := by
      intro h0
      apply hξne
      exact tomitaFormResolvent_injective (ω.state 1) (hclos 1)
        (h0.trans (map_zero _).symm)
    have hRsq : 0 < ‖tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hRne)
    linarith [sq_nonneg ‖closedTomitaOperator (ω.state 1) (hclos 1)
      (tomitaFormResolventDomCLM (ω.state 1) (hclos 1) ξ1).val‖]
  have hR_lt : (inner ℂ ξ1 (tomitaFormResolventCLM (ω.state 1) (hclos 1) ξ1)).re <
      ‖ξ1‖ ^ 2 := by
    linarith
  refine ⟨hξne, hR_pos, hR_lt, hcomp_pos, hS_ne, norm_pos_iff.mpr hS_ne, ?_, ?_⟩
  · exact (graphDomInclCLM_filteredTomitaGraphDomMap CStarMatrixStage cstarMatrixInductiveSystem
      ω hclos (Nat.zero_le 1) (tomitaFormResolventDomCLM (ω.state 0) (hclos 0) ξ0)).trans rfl
  · exact filteredTomitaFormResolvent_monotone CStarMatrixStage cstarMatrixInductiveSystem ω hclos
      (Nat.zero_le 1) ξ0

end Tier5_M2

/-! ### `M3a` (`TwistedCrossedProductAlgebra`): `covariantLift_unique` & `dualActionHom ≠ 1` -/

def tier5DihedralSignFun : DihedralGroup 4 →* ℂ where
  toFun g := match g with | DihedralGroup.r _ => 1 | DihedralGroup.sr _ => -1
  map_one' := rfl
  map_mul' g h := by rcases g with i | i <;> rcases h with j | j <;> simp

def tier5DihedralSignChar : DihedralGroup 4 →* unitary ℂ :=
  unitaryCharOf tier5DihedralSignFun (fun g => by
    rcases g with i | i
    · change star (1 : ℂ) * 1 = 1; simp
    · change star (-1 : ℂ) * (-1 : ℂ) = 1; simp)

theorem t5_m3a_covariantLift_unique_and_dualAction :
    (∀ Φ : WitnessCrossedProduct →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ,
      (∀ a, Φ (embedAlg a) = a) →
      (∀ g, Φ (embedGroup g) = (dihedral4UnitaryHom g : Matrix (Fin 2) (Fin 2) ℂ)) →
      Φ = witnessCovariantLift) ∧
    dualActionHom (θ := dihedral4Action) tier5DihedralSignChar ≠ 1 ∧
    dualAction (θ := dihedral4Action) tier5DihedralSignChar (embedGroup (DihedralGroup.sr 0)) ≠
      embedGroup (θ := dihedral4Action) (DihedralGroup.sr 0) ∧
    embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) *
        embedAlg (Matrix.of ![![(1 : ℂ), 0], ![0, 0]]) ≠
      embedAlg (Matrix.of ![![(1 : ℂ), 0], ![0, 0]]) *
        embedGroup (θ := dihedral4Action) (DihedralGroup.r 1) := by
  refine ⟨fun Φ hA hG => ?_, ?_, ?_, ?_⟩
  · exact covariantLift_unique (StarAlgHom.id ℂ _) dihedral4UnitaryHom (fun _ _ => rfl) Φ hA hG
  · intro h1
    have hsr := congrArg
      (fun Ψ : WitnessCrossedProduct ≃⋆ₐ[ℂ] WitnessCrossedProduct =>
        Ψ (embedGroup (DihedralGroup.sr 0))) h1
    change dualAction (θ := dihedral4Action) tier5DihedralSignChar
        (embedGroup (DihedralGroup.sr 0)) =
      embedGroup (θ := dihedral4Action) (DihedralGroup.sr 0) at hsr
    rw [dualAction_embedGroup] at hsr
    have hval : (tier5DihedralSignChar (DihedralGroup.sr 0) : ℂ) = -1 := rfl
    rw [hval] at hsr
    have hcoeff := congrArg (fun x : WitnessCrossedProduct =>
      (x.toFinsupp (DihedralGroup.sr 0)) 0 0) hsr
    simp at hcoeff
    norm_num at hcoeff
  · intro hsr
    rw [dualAction_embedGroup] at hsr
    have hval : (tier5DihedralSignChar (DihedralGroup.sr 0) : ℂ) = -1 := rfl
    rw [hval] at hsr
    have hcoeff := congrArg (fun x : WitnessCrossedProduct =>
      (x.toFinsupp (DihedralGroup.sr 0)) 0 0) hsr
    simp at hcoeff
    norm_num at hcoeff
  · exact witness_twist_noncommute

/-! ### `M3b` (`PowersModularSpectrum`): `UHFStage` Eigenvectors, Separation, & `1`-Closure -/

theorem t5_m3b_uhfStage1_eigenvectors_and_closure :
    let lam : ℝ := 1 / 3
    let i0 : Fin (2 ^ 1) := ⟨0, by decide⟩
    let i1 : Fin (2 ^ 1) := ⟨1, by decide⟩
    (elemUnit 1 i1 i0 ≠ 0 ∧
      powersModularOp lam 1 (elemUnit 1 i1 i0) = ((1 / 3 : ℝ) : ℂ) • elemUnit 1 i1 i0) ∧
    (elemUnit 1 i0 i0 ≠ 0 ∧
      powersModularOp lam 1 (elemUnit 1 i0 i0) = ((1 : ℝ) : ℂ) • elemUnit 1 i0 i0) ∧
    (elemUnit 1 i0 i1 ≠ 0 ∧
      powersModularOp lam 1 (elemUnit 1 i0 i1) = ((3 : ℝ) : ℂ) • elemUnit 1 i0 i1) ∧
    (∀ m n : ℤ, m ≠ n → 0 < |(1 / 3 : ℝ) ^ m - (1 / 3 : ℝ) ^ n|) ∧
    (0 : ℝ) ∉ closure (powersPointSpec (1 : ℝ)) ∧
    (0 : ℝ) ∈ closure (powersPointSpec (1 / 3 : ℝ)) := by
  intro lam i0 i1
  have hw0 : bitPopcount i0.val = 0 := by simp [i0]
  have hw1 : bitPopcount i1.val = 1 := by simpa using bitPopcount_twoPow_sub_one 1
  have hc : (1 / (1 + lam)) ^ 1 ≠ 0 := by norm_num [lam]
  have hr10 : powersWeight lam 1 i1 / powersWeight lam 1 i0 = (1 / 3 : ℝ) := by
    unfold powersWeight
    rw [mul_div_mul_left _ _ hc, hw1, hw0]
    norm_num [lam]
  have hr00 : powersWeight lam 1 i0 / powersWeight lam 1 i0 = (1 : ℝ) :=
    div_self (powersWeight_pos (by norm_num [lam]) 1 i0).ne'
  have hr01 : powersWeight lam 1 i0 / powersWeight lam 1 i1 = (3 : ℝ) := by
    unfold powersWeight
    rw [mul_div_mul_left _ _ hc, hw1, hw0]
    norm_num [lam]
  refine ⟨⟨elemUnit_ne_zero 1 i1 i0, ?_⟩, ⟨elemUnit_ne_zero 1 i0 i0, ?_⟩,
    ⟨elemUnit_ne_zero 1 i0 i1, ?_⟩, ?_, ?_, ?_⟩
  · rw [powersModularOp_elemUnit, hr10]
  · rw [powersModularOp_elemUnit, hr00]
  · rw [powersModularOp_elemUnit, hr01]
  · intro m n hmn
    exact abs_pos.mpr (sub_ne_zero.mpr fun h =>
      hmn (powersPointSpec_injective (by norm_num) (by norm_num) h))
  · intro hmem
    have hsub : powersPointSpec (1 : ℝ) ⊆ ({(1 : ℝ)} : Set ℝ) := by
      rintro _ ⟨k, rfl⟩
      simp
    have hcl : closure (powersPointSpec (1 : ℝ)) ⊆ ({(1 : ℝ)} : Set ℝ) :=
      closure_minimal hsub isClosed_singleton
    have h01 : (0 : ℝ) = 1 := Set.mem_singleton_iff.mp (hcl hmem)
    norm_num at h01
  · exact zero_mem_closure_powersPointSpec (by norm_num) (by norm_num)

/-! ### `M4` (`ComplexRelativeModularRN`): `u_π ≠ u_{π/2}^2`, 3-Density Chain, Intertwining, Polar -/

def witnessSqrt2Inv : ℂ := ((Real.sqrt 2 : ℝ)⁻¹ : ℂ)

lemma witnessSqrt2Inv_sq : witnessSqrt2Inv * witnessSqrt2Inv = (1 / 2 : ℂ) := by
  unfold witnessSqrt2Inv
  have hreal : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  simpa [Complex.ofReal_mul, Complex.ofReal_inv] using hc

def witnessV : Matrix (Fin 2) (Fin 2) ℂ :=
  witnessSqrt2Inv • !![(1 : ℂ), 1; 1, -1]

lemma witnessV_sq : witnessV * witnessV = 1 := by
  rw [witnessV, Matrix.smul_mul, Matrix.mul_smul, smul_smul, witnessSqrt2Inv_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

def witnessVUnit : (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  val := witnessV
  inv := witnessV
  val_inv := witnessV_sq
  inv_val := witnessV_sq

def witnessHChi : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), 1; 1, 0]

theorem witnessHChi_isHermitian : witnessHChi.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [witnessHChi, Matrix.conjTranspose_apply]

def witnessExpChi : ExpDensityFactor 2 where
  H := witnessHChi
  H_herm := witnessHChi_isHermitian

theorem witnessHChi_eq_conj :
    witnessHChi = witnessV * witnessHPhi * witnessV := by
  rw [witnessV, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    witnessSqrt2Inv_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessHChi, witnessHPhi, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    norm_num

theorem witnessExpChi_rho_eq :
    witnessExpChi.rho = witnessV * witnessRhoPhi * witnessV := by
  change NormedSpace.exp witnessHChi = witnessV * witnessRhoPhi * witnessV
  rw [witnessHChi_eq_conj]
  have hconj := Matrix.exp_units_conj witnessVUnit witnessHPhi
  simpa [witnessVUnit, witnessRhoPhi, ExpDensityFactor.rho, witnessExpPhi, Matrix.mul_assoc]
    using hconj

theorem witnessExpChi_noncomm_phi_psi :
    witnessExpChi.rho * witnessRhoPhi ≠ witnessRhoPhi * witnessExpChi.rho ∧
      witnessExpChi.rho * witnessRhoPsi ≠ witnessRhoPsi * witnessExpChi.rho := by
  have hchi_eq : witnessExpChi.rho =
      !![((Complex.exp (1 : ℂ) + Complex.exp (-1 : ℂ)) / 2),
         ((Complex.exp (1 : ℂ) - Complex.exp (-1 : ℂ)) / 2);
         ((Complex.exp (1 : ℂ) - Complex.exp (-1 : ℂ)) / 2),
         ((Complex.exp (1 : ℂ) + Complex.exp (-1 : ℂ)) / 2)] := by
    rw [witnessExpChi_rho_eq, witnessRhoPhi_eq, witnessV, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, witnessSqrt2Inv_sq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.vecMul, dotProduct]; ring)
  have hexp_ne : Complex.exp (1 : ℂ) ≠ Complex.exp (-1 : ℂ) := by
    intro h
    have hre : Real.exp 1 = Real.exp (-1) := Complex.ofReal_injective (by simpa using h)
    exact (Real.exp_strictMono (by norm_num : (-1 : ℝ) < 1)).ne' hre
  have hsub_ne : Complex.exp (1 : ℂ) - Complex.exp (-1 : ℂ) ≠ 0 := sub_ne_zero.mpr hexp_ne
  refine ⟨?_, ?_⟩
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    rw [hchi_eq, witnessRhoPhi_eq] at h01
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
    have hdiff : ((Complex.exp (1 : ℂ) - Complex.exp (-1 : ℂ)) / 2) *
        (Complex.exp (-1 : ℂ) - Complex.exp (1 : ℂ)) = 0 := by
      linear_combination h01
    rcases mul_eq_zero.mp hdiff with hzero | hzero
    · exact hsub_ne (by linear_combination 2 * hzero)
    · exact hexp_ne (sub_eq_zero.mp hzero).symm
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    rw [hchi_eq, witnessRhoPsi_eq, witnessRhoPhi_eq] at h01
    have hrot : witnessRotationUᴴ =
        !![(3 / 5 : ℂ), -(4 / 5 : ℂ); (4 / 5 : ℂ), (3 / 5 : ℂ)] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [witnessRotationU, Matrix.conjTranspose_apply]
    rw [hrot] at h01
    simp [witnessRotationU, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h01
    have hdiff : (7 / 50 : ℂ) * (Complex.exp (1 : ℂ) - Complex.exp (-1 : ℂ)) ^ 2 = 0 := by
      linear_combination h01
    have hc : (7 / 50 : ℂ) ≠ 0 := by norm_num
    have hsq : (Complex.exp (1 : ℂ) - Complex.exp (-1 : ℂ)) ^ 2 = 0 :=
      (mul_eq_zero.mp hdiff).resolve_left hc
    exact hsub_ne (sq_eq_zero_iff.mp hsq)

theorem t5_m4_cocycle_and_relTomita_hardening :
    relConnesCocycle witnessExpPsi witnessExpPhi Real.pi ≠
      (relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2)) ^ 2 ∧
    witnessRhoPsi * witnessRhoPhi ≠ witnessRhoPhi * witnessRhoPsi ∧
    witnessExpChi.rho * witnessRhoPhi ≠ witnessRhoPhi * witnessExpChi.rho ∧
    witnessExpChi.rho * witnessRhoPsi ≠ witnessRhoPsi * witnessExpChi.rho ∧
    relConnesCocycle witnessExpChi witnessExpPhi (Real.pi / 2) =
      relConnesCocycle witnessExpChi witnessExpPsi (Real.pi / 2) *
        relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2) ∧
    witnessExpPsi.modularFlow (Real.pi / 2) witnessE01 ≠
      witnessExpPhi.modularFlow (Real.pi / 2) witnessE01 ∧
    relTomitaAdjOp witnessExpPsi.toPositiveComplexDensityFactor
        witnessExpPhi.toPositiveComplexDensityFactor
        (relTomitaOp witnessExpPsi.toPositiveComplexDensityFactor
          witnessExpPhi.toPositiveComplexDensityFactor witnessE01) =
      relModularOp witnessExpPsi.toPositiveComplexDensityFactor
        witnessExpPhi.toPositiveComplexDensityFactor witnessE01 ∧
    relTomitaOp witnessExpPsi.toPositiveComplexDensityFactor
        witnessExpPhi.toPositiveComplexDensityFactor witnessE01 =
      matrixJ 2 (relModularSqrt witnessExpPsi.toPositiveComplexDensityFactor
        witnessExpPhi.toPositiveComplexDensityFactor witnessE01) ∧
    relModularOp witnessExpPsi.toPositiveComplexDensityFactor
        witnessExpPhi.toPositiveComplexDensityFactor witnessE01 ≠
      witnessE01 := by
  have hphi_pi : witnessExpPhi.unitary (-Real.pi) = -1 := by
    unfold ExpDensityFactor.unitary witnessExpPhi witnessHPhi
    have hsmul : (Complex.I * ((-Real.pi : ℝ) : ℂ)) • Matrix.diagonal ![(1 : ℂ), -1] =
        Matrix.diagonal ![-(Real.pi : ℂ) * Complex.I, (Real.pi : ℂ) * Complex.I] := by
      ext i j; fin_cases i <;> fin_cases j <;> (simp; try ring)
    rw [hsmul, Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.exp_neg_pi_mul_I, Complex.exp_pi_mul_I]
  have hpsi_pi : witnessExpPsi.unitary Real.pi = -1 := by
    unfold ExpDensityFactor.unitary witnessExpPsi witnessHPsi
    have hphi_pos : NormedSpace.exp ((Complex.I * (Real.pi : ℂ)) • witnessHPhi) = -1 := by
      unfold witnessHPhi
      have hsmul : (Complex.I * (Real.pi : ℂ)) • Matrix.diagonal ![(1 : ℂ), -1] =
          Matrix.diagonal ![(Real.pi : ℂ) * Complex.I, -(Real.pi : ℂ) * Complex.I] := by
        ext i j; fin_cases i <;> fin_cases j <;> (simp; try ring)
      rw [hsmul, Matrix.exp_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.exp_neg_pi_mul_I, Complex.exp_pi_mul_I]
    have hsmul : (Complex.I * (Real.pi : ℂ)) •
        (witnessRotationU * witnessHPhi * witnessRotationUᴴ) =
        witnessRotationU * ((Complex.I * (Real.pi : ℂ)) • witnessHPhi) * witnessRotationUᴴ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hsmul]
    have hconj := Matrix.exp_units_conj witnessRotationUUnit
      ((Complex.I * (Real.pi : ℂ)) • witnessHPhi)
    rw [hphi_pos] at hconj
    change NormedSpace.exp (witnessRotationU * ((Complex.I * (Real.pi : ℂ)) • witnessHPhi) *
      witnessRotationUᴴ) = witnessRotationU * (-1 : Matrix (Fin 2) (Fin 2) ℂ) *
      witnessRotationUᴴ at hconj
    rw [hconj]
    simp [witnessRotationU_mul_conjTranspose]
  have hu_pi : relConnesCocycle witnessExpPsi witnessExpPhi Real.pi = 1 := by
    unfold relConnesCocycle
    rw [hpsi_pi, hphi_pi]
    simp
  have hu_half : relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2) =
      !![(-(7 / 25) : ℂ), (24 / 25 : ℂ); -(24 / 25 : ℂ), -(7 / 25 : ℂ)] := by
    unfold relConnesCocycle
    rw [witnessExpPsi_unitary_pi_div_two, witnessExpPhi_unitary_neg_pi_div_two]
    have hrot : witnessRotationUᴴ =
        !![(3 / 5 : ℂ), -(4 / 5 : ℂ); (4 / 5 : ℂ), (3 / 5 : ℂ)] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [witnessRotationU, Matrix.conjTranspose_apply]
    rw [hrot]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [witnessRotationU, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two];
       ring_nf; rw [Complex.I_sq]; norm_num)
  refine ⟨?_, witnessRhoPsi_mul_witnessRhoPhi_ne, witnessExpChi_noncomm_phi_psi.1,
    witnessExpChi_noncomm_phi_psi.2,
    relConnesCocycle_chain_rule witnessExpChi witnessExpPsi witnessExpPhi (Real.pi / 2),
    ?_, relModularOp_eq_adj_comp_relTomita _ _ _, relTomitaOp_polar _ _ _, ?_⟩
  · intro h
    rw [hu_pi, hu_half] at h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two] at h01
    norm_num at h01
  · intro h
    rw [relConnesCocycle_intertwines witnessExpPsi witnessExpPhi (Real.pi / 2) witnessE01] at h
    have hadj : (relConnesCocycle witnessExpPsi witnessExpPhi (Real.pi / 2))ᴴ =
        !![(-(7 / 25) : ℂ), -(24 / 25 : ℂ); (24 / 25 : ℂ), -(7 / 25 : ℂ)] := by
      rw [hu_half]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
    have hphi_flow : witnessExpPhi.modularFlow (Real.pi / 2) witnessE01 =
        !![(0 : ℂ), -1; 0, 0] := by
      rw [ExpDensityFactor.modularFlow_apply, witnessExpPhi_unitary_pi_div_two,
        witnessExpPhi_unitary_neg_pi_div_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [witnessE01, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hadj, hu_half, hphi_flow] at h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  · intro h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
    have hphi_inv : witnessExpPhi.toPositiveComplexDensityFactor.rhoInv =
        Matrix.diagonal ![Complex.exp (-1 : ℂ), Complex.exp (1 : ℂ)] := by
      rw [ExpDensityFactor.toPositiveComplexDensityFactor_rhoInv]
      unfold ExpDensityFactor.rhoInv witnessExpPhi witnessHPhi
      have hneg : -Matrix.diagonal ![(1 : ℂ), -1] = Matrix.diagonal ![(-1 : ℂ), 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      rw [hneg, Matrix.exp_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
    have hpsi_rho : witnessExpPsi.toPositiveComplexDensityFactor.rho = witnessRhoPsi := by
      rw [ExpDensityFactor.toPositiveComplexDensityFactor_rho]
      rfl
    unfold relModularOp at h11
    rw [hpsi_rho, hphi_inv, witnessRhoPsi_eq, witnessRhoPhi_eq] at h11
    have hrot : witnessRotationUᴴ =
        !![(3 / 5 : ℂ), -(4 / 5 : ℂ); (4 / 5 : ℂ), (3 / 5 : ℂ)] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [witnessRotationU, Matrix.conjTranspose_apply]
    rw [hrot] at h11
    simp [witnessE01, witnessRotationU, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] at h11
    have hexp_eq : Complex.exp (1 : ℂ) = Complex.exp (-1 : ℂ) := by
      linear_combination (-25 / 12 : ℂ) * h11
    have hre : Real.exp 1 = Real.exp (-1) := Complex.ofReal_injective (by simpa using hexp_eq)
    exact (Real.exp_strictMono (by norm_num : (-1 : ℝ) < 1)).ne' hre

/-! ### `M5` (`LpSpectralMultiplicationModel`): Infinite-Measure `(ℝ, volume)` Witnesses -/

theorem t5_m5_real_volume_spectral_witness :
    let S : ℕ → Set ℝ := fun n => Set.Ico (n : ℝ) ((n : ℝ) + 1)
    let hS : ∀ n, MeasurableSet (S n) := fun _ => measurableSet_Ico
    let ψ : L2c ℝ volume :=
      MeasureTheory.indicatorConstLp 2 (measurableSet_Ico : MeasurableSet (Set.Ico (0 : ℝ) 2))
        (by simp [Real.volume_Ico]) (1 : ℂ)
    let f : ℝ → ℂ := fun _ => Complex.I
    let hf : AEStronglyMeasurable f volume := aestronglyMeasurable_const
    let hC : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ ≤ (1 : ℝ) :=
      Eventually.of_forall fun _ => by simp [f]
    Tendsto
        (fun N => ∑ n ∈ Finset.range N,
          pvmProj (α := ℝ) (μ := volume) (S n) (hS n) ψ)
        atTop
        (𝓝 (pvmProj (α := ℝ) (μ := volume) (⋃ n, S n) (MeasurableSet.iUnion hS) ψ)) ∧
      pvmProj (α := ℝ) (μ := volume) (S 0) (hS 0) ψ ≠ ψ ∧
      stoneMulGroup (α := ℝ) (μ := volume) id measurable_id (Real.pi / 2) ψ ≠ ψ ∧
      (lpMulOpOfBound (α := ℝ) (μ := volume) f hf 1 hC).adjoint ≠
        lpMulOpOfBound (α := ℝ) (μ := volume) f hf 1 hC ∧
      lpMulOpOfBound (α := ℝ) (μ := volume) f hf 1 hC ψ ≠ 0 := by
  intro S hS ψ f hf hC
  have hdisj : Pairwise (Disjoint on S) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_iff]
    intro x ⟨hxm, hxn⟩
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have hle : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
      linarith [hxm.2, hxn.1]
    · have hle : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hgt
      linarith [hxm.1, hxn.2]
  have hψ_ae : ⇑ψ =ᵐ[volume] (Set.Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℂ)) :=
    MeasureTheory.indicatorConstLp_coeFn
  have hvol12 : (volume : Measure ℝ) (Set.Ico (1 : ℝ) 2) ≠ 0 := by simp
  have hvol01 : (volume : Measure ℝ) (Set.Ioo (0 : ℝ) 1) ≠ 0 := by simp
  have : NeBot (ae ((volume : Measure ℝ).restrict (Set.Ico (1 : ℝ) 2))) :=
    MeasureTheory.ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hvol12)
  have : NeBot (ae ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))) :=
    MeasureTheory.ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hvol01)
  refine ⟨pvmProj_countable_add S hS hdisj ψ, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hae_eq : ⇑(pvmProj (α := ℝ) (μ := volume) (S 0) (hS 0) ψ) =ᵐ[volume] ⇑ψ :=
      MeasureTheory.Lp.ext_iff.mp hEq
    have hres : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ico (1 : ℝ) 2)),
        x ∈ Set.Ico (1 : ℝ) 2 ∧
        ⇑(pvmProj (α := ℝ) (μ := volume) (S 0) (hS 0) ψ) x =
          (S 0).indicator (fun _ => (1 : ℂ)) x * ⇑ψ x ∧
        ⇑ψ x = (Set.Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℂ)) x ∧
        ⇑(pvmProj (α := ℝ) (μ := volume) (S 0) (hS 0) ψ) x = ⇑ψ x := by
      refine (ae_restrict_mem measurableSet_Ico).and ?_
      exact MeasureTheory.ae_restrict_of_ae
        ((pvmProj_apply_ae (S 0) (hS 0) ψ).and (hψ_ae.and hae_eq))
    obtain ⟨x, hxIco, hP, hInd, hSame⟩ := hres.exists
    have hxS0 : x ∉ S 0 := by
      intro h0
      have : (1 : ℝ) ≤ x := hxIco.1
      have : x < 1 := by simpa [S] using h0.2
      linarith
    have hx02 : x ∈ Set.Ico (0 : ℝ) 2 := ⟨by linarith [hxIco.1], hxIco.2⟩
    rw [hSame, hInd, Set.indicator_of_mem hx02] at hP
    rw [Set.indicator_of_notMem hxS0, zero_mul] at hP
    exact one_ne_zero hP
  · intro hEq
    have hae_eq :
        ⇑(stoneMulGroup (α := ℝ) (μ := volume) id measurable_id (Real.pi / 2) ψ) =ᵐ[volume] ⇑ψ :=
      MeasureTheory.Lp.ext_iff.mp hEq
    have hres : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)),
        x ∈ Set.Ioo (0 : ℝ) 1 ∧
        ⇑(stoneMulGroup (α := ℝ) (μ := volume) id measurable_id (Real.pi / 2) ψ) x =
          Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ) * (x : ℂ)) * ⇑ψ x ∧
        ⇑ψ x = (Set.Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℂ)) x ∧
        ⇑(stoneMulGroup (α := ℝ) (μ := volume) id measurable_id (Real.pi / 2) ψ) x = ⇑ψ x := by
      refine (ae_restrict_mem measurableSet_Ioo).and ?_
      exact MeasureTheory.ae_restrict_of_ae
        ((stoneMulGroup_apply_ae id measurable_id (Real.pi / 2) ψ).and (hψ_ae.and hae_eq))
    obtain ⟨x, hxIoo, hU, hInd, hSame⟩ := hres.exists
    have hx02 : x ∈ Set.Ico (0 : ℝ) 2 := ⟨hxIoo.1.le, by linarith [hxIoo.2]⟩
    rw [hSame, hInd, Set.indicator_of_mem hx02, mul_one] at hU
    have him := congrArg Complex.im hU
    have harg : Complex.I * ((Real.pi / 2 : ℝ) : ℂ) * (x : ℂ) =
        ((Real.pi / 2 * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at him
    simp only [Complex.one_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at him
    have hpos : 0 < Real.sin (Real.pi / 2 * x) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_div_two_pos hxIoo.1)
        (by nlinarith [hxIoo.2, Real.pi_pos])
    linarith
  · intro hAdj
    have hψ_eq := congrArg (fun T : L2c ℝ volume →L[ℂ] L2c ℝ volume => T ψ) hAdj
    have hstar_m : AEStronglyMeasurable (star ∘ f) volume := hf.star
    have hstar_b : ∀ᵐ x ∂(volume : Measure ℝ), ‖(star ∘ f) x‖ ≤ (1 : ℝ) :=
      Eventually.of_forall fun _ => by simp [f]
    rw [lpMulOpOfBound_adjoint f hf 1 hC hstar_m 1 hstar_b] at hψ_eq
    have hae_eq := MeasureTheory.Lp.ext_iff.mp hψ_eq
    have hres : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)),
        x ∈ Set.Ioo (0 : ℝ) 1 ∧
        ⇑(lpMulOpOfBound (α := ℝ) (μ := volume) (star ∘ f) hstar_m 1 hstar_b ψ) x =
          (star ∘ f) x * ⇑ψ x ∧
        ⇑(lpMulOpOfBound (α := ℝ) (μ := volume) f hf 1 hC ψ) x = f x * ⇑ψ x ∧
        ⇑ψ x = (Set.Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℂ)) x ∧
        ⇑(lpMulOpOfBound (α := ℝ) (μ := volume) (star ∘ f) hstar_m 1 hstar_b ψ) x =
          ⇑(lpMulOpOfBound (α := ℝ) (μ := volume) f hf 1 hC ψ) x := by
      refine (ae_restrict_mem measurableSet_Ioo).and ?_
      exact MeasureTheory.ae_restrict_of_ae
        ((lpMulOpOfBound_apply_ae (star ∘ f) hstar_m 1 hstar_b ψ).and
          ((lpMulOpOfBound_apply_ae f hf 1 hC ψ).and (hψ_ae.and hae_eq)))
    obtain ⟨x, hxIoo, hL, hR, hInd, hSame⟩ := hres.exists
    have hx02 : x ∈ Set.Ico (0 : ℝ) 2 := ⟨hxIoo.1.le, by linarith [hxIoo.2]⟩
    rw [hSame, hR, hInd, Set.indicator_of_mem hx02, mul_one] at hL
    simp only [Function.comp_apply, f, Complex.star_def, Complex.conj_I] at hL
    have him := congrArg Complex.im hL
    norm_num at him
  · intro h0
    have hae_eq : ⇑(lpMulOpOfBound (α := ℝ) (μ := volume) f hf 1 hC ψ) =ᵐ[volume]
        ⇑(0 : L2c ℝ volume) :=
      MeasureTheory.Lp.ext_iff.mp h0
    have hres : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1)),
        x ∈ Set.Ioo (0 : ℝ) 1 ∧
        ⇑(lpMulOpOfBound (α := ℝ) (μ := volume) f hf 1 hC ψ) x = f x * ⇑ψ x ∧
        ⇑ψ x = (Set.Ico (0 : ℝ) 2).indicator (fun _ => (1 : ℂ)) x ∧
        ⇑(lpMulOpOfBound (α := ℝ) (μ := volume) f hf 1 hC ψ) x = ⇑(0 : L2c ℝ volume) x ∧
        ⇑(0 : L2c ℝ volume) x = 0 := by
      refine (ae_restrict_mem measurableSet_Ioo).and ?_
      exact MeasureTheory.ae_restrict_of_ae
        ((lpMulOpOfBound_apply_ae f hf 1 hC ψ).and
          (hψ_ae.and (hae_eq.and (MeasureTheory.Lp.coeFn_zero ℂ 2 volume))))
    obtain ⟨x, hxIoo, hL, hInd, hSame, hZ⟩ := hres.exists
    have hx02 : x ∈ Set.Ico (0 : ℝ) 2 := ⟨hxIoo.1.le, by linarith [hxIoo.2]⟩
    rw [hSame, hZ, hInd, Set.indicator_of_mem hx02, mul_one] at hL
    exact Complex.I_ne_zero hL.symm

/-! ### `M6` (`TomitaRegularCommutantAndKMSBridge`): `shearOp` & Non-Diagonal KMS Bridge -/

def shearOp : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (!![(0 : ℂ), 1; 4, 0]).toEuclideanLin.toContinuousLinearMap

theorem shearOp_adjoint :
    shearOp.adjoint = (!![(0 : ℂ), 4; 1, 0]).toEuclideanLin.toContinuousLinearMap := by
  have hconj : (!![(0 : ℂ), 1; 4, 0])ᴴ = !![(0 : ℂ), 4; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  have hadj := Matrix.toEuclideanLin_conjTranspose_eq_adjoint !![(0 : ℂ), 1; 4, 0]
  change ⟪(!![(0 : ℂ), 4; 1, 0]).toEuclideanLin u, v⟫_ℂ =
    ⟪u, (!![(0 : ℂ), 1; 4, 0]).toEuclideanLin v⟫_ℂ
  rw [← hconj, hadj, LinearMap.adjoint_inner_left]

theorem t5_m6_shearOp_counterexample :
    (∀ x ∈ tiltedK, shearOp x ∈ tiltedK) ∧
      ¬ (∀ x ∈ tiltedK, shearOp.adjoint x ∈ tiltedK) ∧
      (shearOp.restrictScalars ℝ).comp (projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK) ≠
        (projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK).comp (shearOp.restrictScalars ℝ) ∧
      (shearOp.restrictScalars ℝ).comp (rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK) ≠
        (rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK).comp (shearOp.restrictScalars ℝ) := by
  have hAK : ∀ x ∈ tiltedK, shearOp x ∈ tiltedK := by
    intro x hx
    rw [mem_tiltedK_iff] at hx ⊢
    change (!![(0 : ℂ), 1; 4, 0]).toEuclideanLin x 1 =
      2 * star ((!![(0 : ℂ), 1; 4, 0]).toEuclideanLin x 0)
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two, hx]
    ring
  have hAdj : ¬ (∀ x ∈ tiltedK, shearOp.adjoint x ∈ tiltedK) := by
    intro h
    have hv : WithLp.toLp 2 ![(1 : ℂ), 2] ∈ tiltedK := by simp [mem_tiltedK_iff]
    have hadj := h _ hv
    rw [mem_tiltedK_iff, shearOp_adjoint] at hadj
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply] at hadj
    norm_num at hadj
  refine ⟨hAK, hAdj, ?_, ?_⟩
  · intro hP
    have h0 := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) =>
      f tiltedE0 0) hP
    change shearOp (projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK tiltedE0) 0 =
      projK (H := EuclideanSpace ℂ (Fin 2)) tiltedK (shearOp tiltedE0) 0 at h0
    rw [projK_tiltedK_apply, projK_tiltedK_apply] at h0
    simp [shearOp, tiltedE0, Matrix.toEuclideanLin, Matrix.toLpLin_apply] at h0
    norm_num at h0
  · intro hR
    have h0 := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 2) =>
      f tiltedE0 1) hR
    change shearOp (rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK tiltedE0) 1 =
      rvdR (H := EuclideanSpace ℂ (Fin 2)) tiltedK (shearOp tiltedE0) 1 at h0
    rw [tiltedK_rvdR_e0] at h0
    have hSe0 : shearOp tiltedE0 = WithLp.toLp 2 ![(0 : ℂ), 4] := by
      ext i
      fin_cases i <;>
        simp [shearOp, tiltedE0, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    rw [hSe0, rvdR_apply, projIK_tiltedK_apply, projK_tiltedK_apply, projK_tiltedK_apply] at h0
    simp [shearOp, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.smul_apply] at h0
    ring_nf at h0
    simp [Complex.I_sq] at h0
    norm_num at h0

set_option maxHeartbeats 2500000 in
def stage1OffDiagTomitaAndKMSBridge :
    StageKTomitaAndKMSBridge tier5OffDiagH tier5OffDiagH_isHermitian 1 zero_lt_one 0 :=
  stageKTomitaAndKMSBridge tier5OffDiagH tier5OffDiagH_isHermitian 1 zero_lt_one 0

set_option maxHeartbeats 2500000 in
theorem t5_m6_nondiag_stageKTomitaAndKMSBridge
    (X Y : InfoGeometry.Canonical.CuntzMatrixTowerInstantiation.MatrixStage 1) :
    tier5OffDiagH 0 1 ≠ 0 ∧
      stage1OffDiagTomitaAndKMSBridge.kmsState.state 1 = 1 ∧
      ComplexMatrixTomitaDuality.modularOp stage1OffDiagTomitaAndKMSBridge.densityFactor X =
        InfoGeometry.Canonical.FiniteMatrixGibbsFunctional.gibbsImaginaryTimeAlgEquiv
          tier5OffDiagH tier5OffDiagH_isHermitian 1 X ∧
      InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS.seedFunctional
          tier5OffDiagH tier5OffDiagH_isHermitian 1 0
          (InfoGeometry.Canonical.FiniteSeedRepresentedRealTime.seedStageHom
            tier5OffDiagH tier5OffDiagH_isHermitian 1
            (X * ComplexMatrixTomitaDuality.modularOp
              (gibbsDensityFactor tier5OffDiagH tier5OffDiagH_isHermitian 1) Y)) =
        InfoGeometry.Canonical.FiniteSeedRepresentedAnalyticKMS.seedFunctional
          tier5OffDiagH tier5OffDiagH_isHermitian 1 0
          (InfoGeometry.Canonical.FiniteSeedRepresentedRealTime.seedStageHom
            tier5OffDiagH tier5OffDiagH_isHermitian 1 (Y * X)) :=
  ⟨tier5OffDiagH_nonDiag,
    stage1OffDiagTomitaAndKMSBridge.kmsState.state_one,
    stage1OffDiagTomitaAndKMSBridge.modularOp_eq X,
    seedFunctional_stage_modularOp_kms tier5OffDiagH tier5OffDiagH_isHermitian 1 0 X Y⟩

end Tier5_Adversarial

end InfoGeometry.Tests.TomitaFrontiersRoadmap

/-! ## In-File Axiom Self-Audit (`TomitaFrontiersRoadmapTests`) -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut allAxioms : Array Name := #[]
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isSome then continue
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration in test module: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed axiom {ax} in test declaration {name}"
      if !allAxioms.contains ax then
        allAxioms := allAxioms.push ax
    count := count + 1
  if count == 0 then
    throwError "No test declarations audited in current module"
  logInfo m!"TEST_SELF_AUDIT_AXIOMS: {allAxioms.qsort Name.lt}"
  logInfo m!"TEST_SELF_AUDIT_COUNT: {count}"
