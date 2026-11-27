/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear

/-!
# Strong real group generators and domain intertwining

The generic generator interface and proofs are extracted unchanged from
`TripotentUnboundedResolventFlow`. Public names and theorem contracts retain
their existing namespace; the original owner imports this focused owner.

The legacy record stores group laws and generator-domain/derivative laws.
It has no separate strong-continuity field. The concrete real ℓ² owner proves
strong continuity independently as `continuous_U_unb`.
-/

namespace InfoGeometry.OperatorAlgebra.TripotentUnboundedResolventFlow

set_option linter.unusedSectionVars false

/-! ### Section 3: C₀-Group Strong HasDerivAt Commutation -/

section C0Group

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

structure C0GroupGenerator (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  U : ℝ → (H →L[ℝ] H)
  U_zero : U 0 = ContinuousLinearMap.id ℝ H
  U_add : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  D_K : Submodule ℝ H
  K : D_K →ₗ[ℝ] H
  hasDerivAt_gen : ∀ x : D_K, HasDerivAt (fun t => U t x.1) (K x) 0
  mem_domain_of_hasDerivAt : ∀ (x : H) (v : H), HasDerivAt (fun t => U t x) v 0 → x ∈ D_K
  gen_eq_of_hasDerivAt : ∀ (x : D_K) (v : H), HasDerivAt (fun t => U t x.1) v 0 → K x = v

instance : Inhabited (C0GroupGenerator H) where
  default := {
    U := fun _ => ContinuousLinearMap.id ℝ H
    U_zero := rfl
    U_add := by
      intro s t
      ext x
      rfl
    D_K := ⊤
    K := 0
    hasDerivAt_gen := by
      intro x
      simpa using hasDerivAt_const (0 : ℝ) x.1
    mem_domain_of_hasDerivAt := by
      intro x v _
      exact Submodule.mem_top
    gen_eq_of_hasDerivAt := by
      intro x v hv
      have h0 : HasDerivAt (fun _ : ℝ => x.1) 0 0 := hasDerivAt_const 0 x.1
      have heq : v = 0 := hv.unique h0
      simp [heq]
  }

theorem c0_group_commute_implies_domain_intertwining
    (G : C0GroupGenerator H) (S : H →L[ℝ] H)
    (hS : ∀ t : ℝ, S.comp (G.U t) = (G.U t).comp S) :
    (∀ ⦃x : H⦄, x ∈ G.D_K → S x ∈ G.D_K) ∧
    ∀ (h_inv : ∀ ⦃x : H⦄, x ∈ G.D_K → S x ∈ G.D_K) (x : G.D_K),
      S (G.K x) = G.K ⟨S x.1, h_inv x.2⟩ := by
  have hS_apply (t : ℝ) (x : H) : S (G.U t x) = G.U t (S x) := by
    have h := ContinuousLinearMap.ext_iff.mp (hS t) x
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply] using h
  have h_inv : ∀ ⦃x : H⦄, x ∈ G.D_K → S x ∈ G.D_K := by
    intro x hx
    have hderiv := G.hasDerivAt_gen ⟨x, hx⟩
    have hderiv_comp : HasDerivAt (fun t => S (G.U t x)) (S (G.K ⟨x, hx⟩)) 0 :=
      S.hasFDerivAt.comp_hasDerivAt 0 hderiv
    have hderiv_eq : HasDerivAt (fun t => G.U t (S x)) (S (G.K ⟨x, hx⟩)) 0 := by
      refine hderiv_comp.congr_of_eventuallyEq ?_
      filter_upwards with t
      exact (hS_apply t x).symm
    exact G.mem_domain_of_hasDerivAt (S x) (S (G.K ⟨x, hx⟩)) hderiv_eq
  refine ⟨h_inv, fun _ x => ?_⟩
  have hderiv := G.hasDerivAt_gen x
  have hderiv_comp : HasDerivAt (fun t => S (G.U t x.1)) (S (G.K x)) 0 :=
    S.hasFDerivAt.comp_hasDerivAt 0 hderiv
  have hderiv_eq : HasDerivAt (fun t => G.U t (S x.1)) (S (G.K x)) 0 := by
    refine hderiv_comp.congr_of_eventuallyEq ?_
    filter_upwards with t
    exact (hS_apply t x.1).symm
  have hK := G.gen_eq_of_hasDerivAt ⟨S x.1, h_inv x.2⟩ (S (G.K x)) hderiv_eq
  exact hK.symm

/-- Commutation with a C₀-group forces domain intertwining and eigenspace invariance. -/
theorem c0_group_commute_implies_domain_intertwining_and_fiveGrade_invariance
    (G : C0GroupGenerator H) (S : H →L[ℝ] H)
    (hS : ∀ t : ℝ, S.comp (G.U t) = (G.U t).comp S) :
    ((∀ ⦃x : H⦄, x ∈ G.D_K → S x ∈ G.D_K) ∧
      ∀ (h_inv : ∀ ⦃x : H⦄, x ∈ G.D_K → S x ∈ G.D_K) (x : G.D_K),
        S (G.K x) = G.K ⟨S x.1, h_inv x.2⟩) ∧
    (∀ (lam : ℝ) (v : H), S v = lam • v → ∀ t : ℝ, S (G.U t v) = lam • (G.U t v)) := by
  refine ⟨c0_group_commute_implies_domain_intertwining G S hS, ?_⟩
  intro lam v hv t
  have hS_apply : S (G.U t v) = G.U t (S v) := by
    have h := ContinuousLinearMap.ext_iff.mp (hS t) v
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply] using h
  rw [hS_apply, hv, map_smul]

end C0Group

end InfoGeometry.OperatorAlgebra.TripotentUnboundedResolventFlow
