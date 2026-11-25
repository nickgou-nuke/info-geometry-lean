/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.Tactic.Module

/-!
# Skew graphs in the canonical neutral phase space

For a linear map from the algebraic dual to the primal space, its graph is
an actual submodule of the existing neutral phase space. Evaluation-skewness
is equivalent to isotropy and implies equality with its neutral orthogonal.
Opposite graphs intersect precisely along kernel covectors. They form a
complementary pair precisely when the map is bijective.

These are algebraic statements. A graph of a variable bivector is a Dirac
subbundle only after the additional differential integrability condition is
proved. No such manifold or integrability assertion is made here.
-/

noncomputable section

namespace InfoGeometry.Geometry.SkewGraphNeutralPairing

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The graph with primal coordinate first and dual coordinate second. -/
def dualGraph (P : Module.Dual ℝ E →ₗ[ℝ] E) : Submodule ℝ (PhaseSpaceCarrier E) :=
  LinearMap.range (P.prod LinearMap.id)

@[simp] theorem mem_dualGraph (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (z : PhaseSpaceCarrier E) : z ∈ dualGraph P ↔ z.1 = P z.2 := by
  constructor
  · rintro ⟨ξ, rfl⟩
    rfl
  · intro h
    exact ⟨z.2, Prod.ext h.symm rfl⟩

@[simp] theorem graph_vector_mem (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (ξ : Module.Dual ℝ E) : (P ξ, ξ) ∈ dualGraph P := by
  rw [mem_dualGraph]

theorem dualGraph_pair (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (ξ η : Module.Dual ℝ E) :
    canonicalNeutralBilin (P ξ, ξ) (P η, η) = ξ (P η) + η (P ξ) := by
  rw [canonicalNeutralBilin_apply]

/-- Isotropy is exactly skewness relative to evaluation; no Euclidean duality is chosen. -/
theorem dualGraph_isotropic_iff (P : Module.Dual ℝ E →ₗ[ℝ] E) :
    (∀ z ∈ dualGraph P, ∀ w ∈ dualGraph P, canonicalNeutralBilin z w = 0) ↔
      ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ) := by
  constructor
  · intro h ξ η
    have hp := h (P ξ, ξ) (graph_vector_mem P ξ) (P η, η) (graph_vector_mem P η)
    rw [dualGraph_pair] at hp
    exact eq_neg_of_add_eq_zero_left hp
  · intro h z hz w hw
    rw [mem_dualGraph] at hz hw
    rw [canonicalNeutralBilin_apply, hz, hw, h z.2 w.2]
    exact neg_add_cancel _

/-- A skew graph is its own neutral orthogonal, hence is maximally isotropic. -/
theorem dualGraph_orthogonal_eq [Module.Projective ℝ E]
    (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hSkew : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ)) :
    (dualGraph P).orthogonalBilin canonicalNeutralBilin = dualGraph P := by
  ext z
  rw [Submodule.mem_orthogonalBilin, mem_dualGraph]
  constructor
  · intro hz
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℝ (z.1 - P z.2)).mp
    intro ξ
    have h := hz (P ξ, ξ) (graph_vector_mem P ξ)
    rw [canonicalNeutralBilin_apply, hSkew z.2 ξ] at h
    simpa only [map_sub, sub_eq_add_neg, map_add, map_neg] using h
  · intro hz w hw
    rw [mem_dualGraph] at hw
    rw [canonicalNeutralBilin_apply, hw, hz, hSkew w.2 z.2]
    exact neg_add_cancel _

/-- Negating a skew graph map preserves isotropy. -/
theorem neg_dualGraph_isotropic (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hSkew : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ)) :
    ∀ z ∈ dualGraph (-P), ∀ w ∈ dualGraph (-P), canonicalNeutralBilin z w = 0 := by
  apply (dualGraph_isotropic_iff (-P)).mpr
  intro ξ η
  simp only [LinearMap.neg_apply, map_neg, neg_neg]
  rw [hSkew ξ η, neg_neg]

/-- The opposite-graph pairing in the unscaled neutral normalization. -/
theorem dualGraph_cross_pair (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (hSkew : ∀ ξ η : Module.Dual ℝ E, ξ (P η) = -η (P ξ))
    (ξ η : Module.Dual ℝ E) :
    canonicalNeutralBilin (P ξ, ξ) ((-P) η, η) = 2 * η (P ξ) := by
  rw [canonicalNeutralBilin_apply]
  simp only [LinearMap.neg_apply, map_neg]
  rw [hSkew ξ η]
  ring

/-- The intersection formula needs no skewness assumption. -/
theorem mem_dualGraph_inf_neg (P : Module.Dual ℝ E →ₗ[ℝ] E)
    (z : PhaseSpaceCarrier E) :
    z ∈ dualGraph P ⊓ dualGraph (-P) ↔ z.1 = 0 ∧ P z.2 = 0 := by
  rw [Submodule.mem_inf, mem_dualGraph, mem_dualGraph]
  simp only [LinearMap.neg_apply]
  constructor
  · rintro ⟨h₁, h₂⟩
    have hsum : z.1 + z.1 = 0 := by
      calc
        z.1 + z.1 = P z.2 + -(P z.2) := congrArg₂ (· + ·) h₁ h₂
        _ = 0 := add_neg_cancel _
    have htwo : (2 : ℝ) • z.1 = 0 := by
      calc
        (2 : ℝ) • z.1 = z.1 + z.1 := by module
        _ = 0 := hsum
    have hz : z.1 = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact ⟨hz, h₁.symm.trans hz⟩
  · rintro ⟨hz, hp⟩
    simp [hz, hp]

/-- As submodules, the intersection is the dual-coordinate image of the kernel. -/
theorem dualGraph_inf_neg_eq (P : Module.Dual ℝ E →ₗ[ℝ] E) :
    dualGraph P ⊓ dualGraph (-P) =
      (LinearMap.ker P).map (LinearMap.inr ℝ E (Module.Dual ℝ E)) := by
  ext z
  rw [mem_dualGraph_inf_neg, Submodule.mem_map]
  constructor
  · rintro ⟨hz, hp⟩
    exact ⟨z.2, hp, Prod.ext hz.symm rfl⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨rfl, hξ⟩

/-- Opposite graphs are disjoint exactly when their defining map is injective. -/
theorem dualGraph_inf_neg_eq_bot_iff (P : Module.Dual ℝ E →ₗ[ℝ] E) :
    dualGraph P ⊓ dualGraph (-P) = ⊥ ↔ Function.Injective P := by
  constructor
  · intro h ξ η hξη
    have hz : (0, ξ - η) ∈ dualGraph P ⊓ dualGraph (-P) := by
      rw [mem_dualGraph_inf_neg]
      exact ⟨rfl, by simp [map_sub, hξη]⟩
    rw [h, Submodule.mem_bot] at hz
    exact sub_eq_zero.mp (congrArg Prod.snd hz)
  · intro h
    apply le_antisymm _ bot_le
    intro z hz
    rw [mem_dualGraph_inf_neg] at hz
    have hξ : z.2 = 0 := h (hz.2.trans (map_zero P).symm)
    exact (Submodule.mem_bot ℝ).mpr (Prod.ext hz.1 hξ)

/-- The sum of opposite graphs fills phase space exactly when the map is surjective. -/
theorem dualGraph_sup_neg_eq_top_iff (P : Module.Dual ℝ E →ₗ[ℝ] E) :
    dualGraph P ⊔ dualGraph (-P) = ⊤ ↔ Function.Surjective P := by
  constructor
  · intro h x
    have hx : (x, 0) ∈ dualGraph P ⊔ dualGraph (-P) := by
      rw [h]
      trivial
    rcases Submodule.mem_sup.mp hx with ⟨z, hz, w, hw, hzw⟩
    rw [mem_dualGraph] at hz hw
    refine ⟨z.2 - w.2, ?_⟩
    have hfst := congrArg Prod.fst hzw
    simpa only [Prod.fst_add, hz, hw, LinearMap.neg_apply, map_sub,
      sub_eq_add_neg, map_add, map_neg] using hfst
  · intro h
    apply top_unique
    intro z _
    obtain ⟨η, hη⟩ := h z.1
    let ξPlus := (1 / 2 : ℝ) • (z.2 + η)
    let ξMinus := (1 / 2 : ℝ) • (z.2 - η)
    apply Submodule.mem_sup.mpr
    refine ⟨(P ξPlus, ξPlus), graph_vector_mem P ξPlus,
      ((-P) ξMinus, ξMinus), graph_vector_mem (-P) ξMinus, ?_⟩
    apply Prod.ext
    · change P ξPlus + (-P) ξMinus = z.1
      simp only [ξPlus, ξMinus, LinearMap.neg_apply, map_smul, map_add, map_sub]
      rw [← hη]
      module
    · change ξPlus + ξMinus = z.2
      dsimp [ξPlus, ξMinus]
      module

/-- Complementarity requires both injectivity and surjectivity in arbitrary dimension. -/
theorem dualGraph_isCompl_iff (P : Module.Dual ℝ E →ₗ[ℝ] E) :
    IsCompl (dualGraph P) (dualGraph (-P)) ↔ Function.Bijective P := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  exact and_congr (dualGraph_inf_neg_eq_bot_iff P) (dualGraph_sup_neg_eq_top_iff P)

end InfoGeometry.Geometry.SkewGraphNeutralPairing
