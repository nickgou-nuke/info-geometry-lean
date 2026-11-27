/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE7SerreHom
import InfoGeometry.Algebra.SplitE8SerreHom
import InfoGeometry.Algebra.CompactOctonionG2Derivations
import InfoGeometry.Algebra.CompactE8MagicSquare
import InfoGeometry.Algebra.H3ZornFreudenthalTKK5E8
import InfoGeometry.Algebra.H3ZornE6SerreHom
import InfoGeometry.Algebra.H3OctonionTKKLieAlgebra
import InfoGeometry.Algebra.H3OctonionSimplicity
import InfoGeometry.Algebra.H3ZornFreudenthalE7Group
import Mathlib.Algebra.Lie.Killing

/-!
# E2E Test Suite for Exceptional Algebra Tier 2 (`E₇` & `E₈` Serre, Compact/Quaternionic `E₈`, 5-Graded TKK `E₈`)

Opaque-box Tiers 1–4 test suite covering all 13 mathematical features across R1–R4:
- **R1 (`H3ZornE7SerreHom`)**: Features 1–3 (`LieAlgebra.e₇ ℝ ≃ₗ⁅ℝ⁆ H3ZornTKKLie`, `finrank = 133`, `IsSimple ℝ`, `IsKilling ℝ`).
- **R2 (`SplitE8SerreHom`)**: Features 4–6 (`e8Simple_serre_E/F`, `LieAlgebra.e₈ ℝ ≃ₗ⁅ℝ⁆ SplitE8Lie`, `finrank = 248`, `IsSimple ℝ`, `IsKilling ℝ`).
- **R3 (`CompactOctonionG2Derivations`, `CompactE8MagicSquare`)**: Features 7–10 (`𝔤₂(-14)`, `𝔈₈(-248)`, `𝔈₈(-24)`, Killing & Cartan signature separation `-248` vs `-24` vs `+8`).
- **R4 (`H3ZornFreudenthalTKK5E8`)**: Features 11–13 (`56D` `repE7`, `248D` 5-graded TKK `𝔈₈`, `sl₂ ⊕ E₇`, `8D` split Cartan, `+8` signature).
- **Tier 3**: Pairwise cross-feature interactions across all 5 major pairs (`R1↔R2`, `R1↔R4`, `R2↔R3`, `R2↔R4`, `R3↔R4`).
- **Tier 4**: Real-world mathematical application scenarios 1–6.
-/

set_option autoImplicit false

namespace InfoGeometry.Tests.E7E8Tier2

open InfoGeometry.Algebra
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.NativeTitsE8Carrier
open InfoGeometry.Algebra.MagicSquareTitsBracket
open InfoGeometry.Algebra.H3ZornFreudenthal
open InfoGeometry.Exceptional.CFSGPort.Chevalley
open scoped TensorProduct BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ## Canonical Opaque-Box Serre Generators -/

private noncomputable abbrev qE6H (i : Fin 6) : LieAlgebra.e₆ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))

private noncomputable abbrev qE6E (i : Fin 6) : LieAlgebra.e₆ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))

private noncomputable abbrev qE6F (i : Fin 6) : LieAlgebra.e₆ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))

private noncomputable abbrev qE7H (i : Fin 7) : LieAlgebra.e₇ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))

private noncomputable abbrev qE7E (i : Fin 7) : LieAlgebra.e₇ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))

private noncomputable abbrev qE7F (i : Fin 7) : LieAlgebra.e₇ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))

private noncomputable abbrev qE8H (i : Fin 8) : LieAlgebra.e₈ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))

private noncomputable abbrev qE8E (i : Fin 8) : LieAlgebra.e₈ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))

private noncomputable abbrev qE8F (i : Fin 8) : LieAlgebra.e₈ ℝ :=
  Submodule.Quotient.mk (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))

/-! ## Local Helper Lemmas for Constructive Witnesses -/

private lemma msEmbedG2LM_lie {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) (D₁ D₂ : G₂) :
    msEmbedG2LM O J ⁅D₁, D₂⁆ = ⁅msEmbedG2LM O J D₁, msEmbedG2LM O J D₂⁆ := by
  change msEmbedG2LM O J ⁅D₁, D₂⁆ =
    magicSquareBracketLM O J (msEmbedG2LM O J D₁) (msEmbedG2LM O J D₂)
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedG2LM]

private lemma msEmbedF4LM_lie {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) (F₁ F₂ : F₄) :
    msEmbedF4LM O J ⁅F₁, F₂⁆ = ⁅msEmbedF4LM O J F₁, msEmbedF4LM O J F₂⁆ := by
  change msEmbedF4LM O J ⁅F₁, F₂⁆ =
    magicSquareBracketLM O J (msEmbedF4LM O J F₁) (msEmbedF4LM O J F₂)
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedF4LM]

private lemma msEmbedG2LM_bracket_msEmbedF4LM {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄) (D : G₂) (F : F₄) :
    ⁅msEmbedG2LM O J D, msEmbedF4LM O J F⁆ = 0 := by
  change magicSquareBracketLM O J (msEmbedG2LM O J D) (msEmbedF4LM O J F) = 0
  apply MagicSquareLie.ext <;> simp [magicSquareBracketLM, msEmbedG2LM, msEmbedF4LM]

private noncomputable def compactG2WitnessD1 : CompactOctonionDerivations :=
  compactOctStanDer (CompactOctonion.basisVec 1) (CompactOctonion.basisVec 2)

private lemma compactG2WitnessD1_apply_basis3_e6 :
    (compactG2WitnessD1.1 (CompactOctonion.basisVec 3)).e6 = 2 := by
  change ((compactOctStanDer (CompactOctonion.basisVec 1) (CompactOctonion.basisVec 2)).1
      (CompactOctonion.basisVec 3)).e6 = 2
  rw [compactOctStanDer_normal_form]
  simp only [compactOctAssociator, CompactOctonion.mul, CompactOctonion.basisVec, sub_eq_add_neg]
  rw [← Nat.cast_smul_eq_nsmul ℝ 3]
  simp
  norm_num

private lemma compactG2WitnessD1_ne_zero : compactG2WitnessD1 ≠ 0 := by
  intro h0
  have h1 := congrArg (fun D : CompactOctonionDerivations =>
    (D.1 (CompactOctonion.basisVec 3)).e6) h0
  rw [compactG2WitnessD1_apply_basis3_e6] at h1
  simp at h1

private lemma cartanE7_eq_castSucc_E8 (i j : Fin 7) :
    CartanMatrix.E 7 i j = CartanMatrix.E 8 i.castSucc j.castSucc := by
  fin_cases i <;> fin_cases j <;> decide

private noncomputable def e7ToE8LiftFree :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 7)) →ₗ⁅ℝ⁆
      FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 8)) :=
  FreeLieAlgebra.lift ℝ (fun g : CartanMatrix.Generators (Fin 7) =>
    FreeLieAlgebra.of ℝ (match g with
      | .H i => CartanMatrix.Generators.H i.castSucc
      | .E i => CartanMatrix.Generators.E i.castSucc
      | .F i => CartanMatrix.Generators.F i.castSucc))

private noncomputable def e8QuotMk :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 8)) →ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ where
  toFun := Submodule.Quotient.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

private noncomputable def e7ToE8FreeLift :
    FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 7)) →ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ :=
  e8QuotMk.comp e7ToE8LiftFree

private lemma local_map_iterate_ad {R L L' : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ L') (x y : L) (n : ℕ) :
    f (Nat.iterate (fun z => ⁅x, z⁆) n y) =
      Nat.iterate (fun z => ⁅f x, z⁆) n (f y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', LieHom.map_lie, ih]

private lemma local_ad_pow_apply_eq_iterate {R L : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] (x y : L) (n : ℕ) :
    ((LieAlgebra.ad R L x) ^ n) y = Nat.iterate (fun z => ⁅x, z⁆) n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change (LieAlgebra.ad R L x) (((LieAlgebra.ad R L x) ^ n) y) = _
      rw [ih]
      simp only [LieAlgebra.ad_apply, Function.iterate_succ_apply']

private noncomputable def e7ToE8SerreHom : LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ := by
  have hI : (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule ≤
      LinearMap.ker e7ToE8FreeLift.toLinearMap := by
    change CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7) ≤ e7ToE8FreeLift.ker
    change LieSubmodule.lieSpan ℝ _ (CartanMatrix.Relations.toSet ℝ (CartanMatrix.E 7)) ≤
      e7ToE8FreeLift.ker
    rw [LieSubmodule.lieSpan_le]
    intro x hx
    change (Submodule.Quotient.mk (e7ToE8LiftFree x) :
      FreeLieAlgebra ℝ (CartanMatrix.Generators (Fin 8)) ⧸
        (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)).toSubmodule) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change e7ToE8LiftFree x ∈ CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 8)
    apply LieSubmodule.subset_lieSpan
    simp only [CartanMatrix.Relations.toSet, Set.mem_union, Set.mem_range] at hx ⊢
    rcases hx with (((((⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) |
        ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩) | ⟨⟨i, j⟩, rfl⟩)
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨i.castSucc, j.castSucc⟩, ?_⟩))))
      simp [CartanMatrix.Relations.HH, e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply]
    · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨i.castSucc, j.castSucc⟩, ?_⟩))))
      by_cases hij : i = j
      · subst j
        simp [CartanMatrix.Relations.EF, e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply]
      · have hne : i.castSucc ≠ j.castSucc := fun h => hij (Fin.castSucc_injective 7 h)
        simp [CartanMatrix.Relations.EF, hij, hne, e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply]
    · refine Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨i.castSucc, j.castSucc⟩, ?_⟩)))
      simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply,
        map_sub, LieHom.map_lie, map_zsmul, e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply,
        cartanE7_eq_castSucc_E8]
    · refine Or.inl (Or.inl (Or.inr ⟨⟨i.castSucc, j.castSucc⟩, ?_⟩))
      simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply,
        map_add, LieHom.map_lie, map_zsmul, e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply,
        cartanE7_eq_castSucc_E8]
    · refine Or.inl (Or.inr ⟨⟨i.castSucc, j.castSucc⟩, ?_⟩)
      simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply]
      rw [local_ad_pow_apply_eq_iterate, local_ad_pow_apply_eq_iterate, local_map_iterate_ad,
        LieHom.map_lie, cartanE7_eq_castSucc_E8]
      simp [e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply]
    · refine Or.inr ⟨⟨i.castSucc, j.castSucc⟩, ?_⟩
      simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply]
      rw [local_ad_pow_apply_eq_iterate, local_ad_pow_apply_eq_iterate, local_map_iterate_ad,
        LieHom.map_lie, cartanE7_eq_castSucc_E8]
      simp [e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply]
  refine
    { (CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.liftQ
        e7ToE8FreeLift.toLinearMap hI with
      map_lie' := ?_ }
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change e7ToE8FreeLift ⁅x, y⁆ = ⁅e7ToE8FreeLift x, e7ToE8FreeLift y⁆
      exact e7ToE8FreeLift.map_lie x y

@[simp] private lemma e7ToE8SerreHom_H (i : Fin 7) :
    e7ToE8SerreHom (qE7H i) = qE8H i.castSucc := by
  change ((CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.liftQ
    e7ToE8FreeLift.toLinearMap _) (Submodule.Quotient.mk _) = _
  rw [Submodule.liftQ_apply]
  change e8QuotMk (e7ToE8LiftFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.H i))) =
    qE8H i.castSucc
  simp [e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply, e8QuotMk, qE8H]
  rfl

@[simp] private lemma e7ToE8SerreHom_E (i : Fin 7) :
    e7ToE8SerreHom (qE7E i) = qE8E i.castSucc := by
  change ((CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.liftQ
    e7ToE8FreeLift.toLinearMap _) (Submodule.Quotient.mk _) = _
  rw [Submodule.liftQ_apply]
  change e8QuotMk (e7ToE8LiftFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.E i))) =
    qE8E i.castSucc
  simp [e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply, e8QuotMk, qE8E]
  rfl

@[simp] private lemma e7ToE8SerreHom_F (i : Fin 7) :
    e7ToE8SerreHom (qE7F i) = qE8F i.castSucc := by
  change ((CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7)).toSubmodule.liftQ
    e7ToE8FreeLift.toLinearMap _) (Submodule.Quotient.mk _) = _
  rw [Submodule.liftQ_apply]
  change e8QuotMk (e7ToE8LiftFree (FreeLieAlgebra.of ℝ (CartanMatrix.Generators.F i))) =
    qE8F i.castSucc
  simp [e7ToE8LiftFree, FreeLieAlgebra.lift_of_apply, e8QuotMk, qE8F]
  rfl

private noncomputable def e6ToE7SerreHom : LieAlgebra.e₆ ℝ →ₗ⁅ℝ⁆ LieAlgebra.e₇ ℝ :=
  (h3zornE7SerreEquiv.symm.toLieHom.comp h3zornCubicStabilizerToTKK).comp
    h3zornE6SerreEquiv.toLieHom

/-! =========================================================================
    TIER 1 & TIER 2: R1 — `InfoGeometry.Algebra.H3ZornE7SerreHom` (F1–F3)
    ========================================================================= -/

/-! ### Feature 1: `E₇` Serre quotient hom (`LieAlgebra.e₇ ℝ →ₗ⁅ℝ⁆ H3ZornTKKLie`) -/

theorem f1_t1_quotient_map_generators (i : Fin 7) :
    h3zornE7SerreQuotientMap (qE7H i) = e7SimpleH i ∧
    h3zornE7SerreQuotientMap (qE7E i) = e7SimpleE i ∧
    h3zornE7SerreQuotientMap (qE7F i) = e7SimpleF i :=
  ⟨h3zornE7SerreQuotientMap_H i, h3zornE7SerreQuotientMap_E i, h3zornE7SerreQuotientMap_F i⟩

theorem f1_t1_quotient_map_brackets :
    h3zornE7SerreQuotientMap ⁅qE7E 0, qE7F 0⁆ = e7SimpleH 0 ∧
    h3zornE7SerreQuotientMap ⁅qE7H 6, qE7E 6⁆ = (2 : ℝ) • e7SimpleE 6 := by
  refine ⟨?_, ?_⟩
  · rw [LieHom.map_lie, h3zornE7SerreQuotientMap_E, h3zornE7SerreQuotientMap_F,
      e7Simple_bracket_EF_same]
  · rw [LieHom.map_lie, h3zornE7SerreQuotientMap_H, h3zornE7SerreQuotientMap_E,
      e7Simple_bracket_HE, h3zornE7_cartan_eq_mathlib]
    have hc : CartanMatrix.E 7 6 6 = 2 := by decide
    rw [hc]; simp

theorem f1_t1_serre_ideal_and_cartan_matrix :
    CartanMatrix.Relations.toIdeal ℝ (CartanMatrix.E 7) ≤ h3zornE7FreeSerreEval.ker ∧
    Tag.cartan .E7 = CartanMatrix.E 7 :=
  ⟨h3zornE7FreeSerreEval_serreIdeal, h3zornE7_cartan_eq_mathlib⟩

theorem f1_t1_castSucc_e6_and_node6_images (i : Fin 6) :
    h3zornE7SerreQuotientMap (qE7E i.castSucc) = h3zornCubicStabilizerToTKK (e6SimpleE i) ∧
    h3zornE7SerreQuotientMap (qE7F i.castSucc) = h3zornCubicStabilizerToTKK (e6SimpleF i) ∧
    h3zornE7SerreQuotientMap (qE7H i.castSucc) = h3zornCubicStabilizerToTKK (e6SimpleH i) ∧
    h3zornE7SerreQuotientMap (qE7E 6) = negInj (h3ZornBasis 10) ∧
    h3zornE7SerreQuotientMap (qE7F 6) = (2 : ℝ) • posInj (h3ZornBasis 3) := by
  rw [h3zornE7SerreQuotientMap_E, h3zornE7SerreQuotientMap_F, h3zornE7SerreQuotientMap_H,
    h3zornE7SerreQuotientMap_E, h3zornE7SerreQuotientMap_F]
  exact ⟨e7SimpleE_castSucc i, e7SimpleF_castSucc i, e7SimpleH_castSucc i,
    e7SimpleE_six, e7SimpleF_six⟩

theorem f1_t1_cartan_span_and_linear_indep :
    Submodule.span ℝ (Set.range (fun i : Fin 7 => h3zornE7SerreQuotientMap (qE7H i))) =
      h3zornE7Cartan.toSubmodule ∧
    LinearIndependent ℝ (fun i : Fin 7 => h3zornE7SerreQuotientMap (qE7H i)) := by
  simp only [h3zornE7SerreQuotientMap_H]
  exact ⟨rfl, e7SimpleH_linearIndependent⟩

theorem f1_t2_quotient_map_zero_and_self_bracket (i : Fin 7) :
    h3zornE7SerreQuotientMap 0 = 0 ∧
    h3zornE7SerreQuotientMap ⁅qE7E i, qE7E i⁆ = 0 :=
  ⟨map_zero _, by rw [LieHom.map_lie, lie_self]⟩

theorem f1_t2_cartan_entries_diag_adj_nonadj :
    CartanMatrix.E 7 0 0 = 2 ∧
    CartanMatrix.E 7 0 2 = -1 ∧
    CartanMatrix.E 7 5 6 = -1 ∧
    CartanMatrix.E 7 0 1 = 0 ∧
    CartanMatrix.E 7 0 6 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem f1_t2_ef_boundary_diag_vs_offdiag {i j : Fin 7} (hij : i ≠ j) :
    h3zornE7SerreQuotientMap ⁅qE7E i, qE7F i⁆ = e7SimpleH i ∧
    h3zornE7SerreQuotientMap ⁅qE7E i, qE7F j⁆ = 0 := by
  rw [LieHom.map_lie, LieHom.map_lie, h3zornE7SerreQuotientMap_E,
    h3zornE7SerreQuotientMap_F, h3zornE7SerreQuotientMap_F]
  exact ⟨e7Simple_bracket_EF_same i, e7Simple_bracket_EF_ne hij⟩

theorem f1_t2_branch_node3_vs_leaves :
    CartanMatrix.E 7 3 1 = -1 ∧
    CartanMatrix.E 7 3 2 = -1 ∧
    CartanMatrix.E 7 3 4 = -1 ∧
    ⁅e7SimpleE 0, e7SimpleE 1⁆ = 0 ∧
    ⁅e7SimpleE 0, e7SimpleE 6⁆ = 0 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · have h := e7Simple_serre_E (i := (0 : Fin 7)) (j := 1) (by decide)
    rw [h3zornE7_cartan_eq_mathlib] at h
    have hc : (1 - CartanMatrix.E 7 0 1).toNat = 1 := by decide
    simpa [hc] using h
  · have h := e7Simple_serre_E (i := (0 : Fin 7)) (j := 6) (by decide)
    rw [h3zornE7_cartan_eq_mathlib] at h
    have hc : (1 - CartanMatrix.E 7 0 6).toNat = 1 := by decide
    simpa [hc] using h

theorem f1_t2_node6_nonunit_scale_two :
    h3zornE7SerreQuotientMap (qE7F 6) = (2 : ℝ) • posInj (h3ZornBasis 3) ∧
    h3zornE7SerreQuotientMap (qE7F 6) ≠ posInj (h3ZornBasis 3) := by
  rw [h3zornE7SerreQuotientMap_F, e7SimpleF_six]
  refine ⟨rfl, ?_⟩
  intro h
  have hpos := congrArg (fun S : H3ZornTKKLie => (h3ZornBasis.repr S.pos) 3) h
  change (h3ZornBasis.repr ((2 : ℝ) • h3ZornBasis 3)) 3 = (h3ZornBasis.repr (h3ZornBasis 3)) 3 at hpos
  simp at hpos

/-! ### Feature 2: `E₇` generators generate & surjectivity -/

theorem f2_t1_rootVec_in_closure_EF (r : Fin 126) :
    e7RootVec r ∈ LieSubalgebra.lieSpan ℝ H3ZornTKKLie (Set.range e7SimpleE ∪ Set.range e7SimpleF) := by
  rw [h3zornE7_lieSpan_EF_eq_top]
  trivial

theorem f2_t1_chevalleyBasis_in_closure_HEF (k : Fin 7 ⊕ Fin 126) :
    e7ChevalleyBasis k ∈
      LieSubalgebra.lieSpan ℝ H3ZornTKKLie
        (Set.range e7SimpleH ∪ Set.range e7SimpleE ∪ Set.range e7SimpleF) := by
  rw [h3zornE7_lieSpan_HEF_eq_top]
  trivial

theorem f2_t1_surjective_explicit_targets :
    (∃ x : LieAlgebra.e₇ ℝ, h3zornE7SerreQuotientMap x = negInj 1) ∧
    (∃ y : LieAlgebra.e₇ ℝ, h3zornE7SerreQuotientMap y = posInj 1) ∧
    (∃ z : LieAlgebra.e₇ ℝ, h3zornE7SerreQuotientMap z = h3zornTKKGradeOp) :=
  ⟨h3zornE7SerreQuotientMap_surjective _,
    h3zornE7SerreQuotientMap_surjective _,
    h3zornE7SerreQuotientMap_surjective _⟩

theorem f2_t1_e6_subalgebra_inside_e7_closure (x : h3zornCubicStabilizer) :
    h3zornCubicStabilizerToTKK x ∈
      LieSubalgebra.lieSpan ℝ H3ZornTKKLie (Set.range e7SimpleE ∪ Set.range e7SimpleF) := by
  rw [h3zornE7_lieSpan_EF_eq_top]
  trivial

theorem f2_t1_node6_commutator_nonzero :
    ⁅h3zornE7SerreQuotientMap (qE7E 6), h3zornE7SerreQuotientMap (qE7F 6)⁆ = e7SimpleH 6 ∧
    e7SimpleH 6 ≠ 0 := by
  rw [h3zornE7SerreQuotientMap_E, h3zornE7SerreQuotientMap_F, e7Simple_bracket_EF_same]
  refine ⟨rfl, ?_⟩
  intro h0
  have hev := e7Simple_bracket_HE 6 6
  rw [h0, zero_lie, h3zornE7_cartan_eq_mathlib] at hev
  have hc6 : CartanMatrix.E 7 6 6 = 2 := by decide
  rw [hc6] at hev
  have he6_0 : e7SimpleE 6 = 0 := by
    have hsm : (2 : ℝ) • e7SimpleE 6 = 0 := by simpa using hev.symm
    exact (smul_eq_zero.mp hsm).resolve_left (by norm_num)
  exact e7RootVec_ne_zero (e7ESimpleIdx 6) (by rwa [← e7SimpleE_eq_rootVec])

theorem f2_t2_pure_H_closure_strictly_lt_top :
    LieSubalgebra.lieSpan ℝ H3ZornTKKLie (Set.range e7SimpleH) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hle : (⊤ : LieSubalgebra ℝ H3ZornTKKLie) ≤ h3zornE7Cartan := by
    rw [← htop, LieSubalgebra.lieSpan_le]
    rintro _ ⟨i, rfl⟩
    exact e7SimpleH_mem_h3zornE7Cartan i
  have hctop : h3zornE7Cartan.toSubmodule = ⊤ :=
    top_unique fun x hx => hle hx
  have hfin := congrArg (fun S : Submodule ℝ H3ZornTKKLie => Module.finrank ℝ S) hctop
  change Module.finrank ℝ h3zornE7Cartan =
    Module.finrank ℝ (⊤ : Submodule ℝ H3ZornTKKLie) at hfin
  rw [finrank_top, finrank_H3ZornTKKLie, finrank_h3zornE7Cartan] at hfin
  omega

theorem f2_t2_e6_excludes_node6 :
    e7SimpleE 6 ∉ Set.range h3zornCubicStabilizerToTKK ∧
    e7SimpleF 6 ∉ Set.range h3zornCubicStabilizerToTKK := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    have hn := congrArg JordanTKK.neg hx
    change (h3zornCubicStabilizerToTKK x).neg = (e7SimpleE 6).neg at hn
    rw [e7SimpleE_six] at hn
    change (0 : H3Zorn ℝ) = h3ZornBasis 10 at hn
    exact h3ZornBasis.ne_zero 10 hn.symm
  · rintro ⟨x, hx⟩
    have hp := congrArg JordanTKK.pos hx
    change (h3zornCubicStabilizerToTKK x).pos = (e7SimpleF 6).pos at hp
    rw [e7SimpleF_six] at hp
    change (0 : H3Zorn ℝ) = (2 : ℝ) • h3ZornBasis 3 at hp
    have h3 := (smul_eq_zero.mp hp.symm).resolve_left (by norm_num)
    exact h3ZornBasis.ne_zero 3 h3

theorem f2_t2_omitting_node6_misses_negInj_basis10 :
    negInj (h3ZornBasis 10) ∉
      LieSubalgebra.map h3zornCubicStabilizerToTKK (⊤ : LieSubalgebra ℝ h3zornCubicStabilizer) := by
  rintro ⟨x, _, hx⟩
  exact f2_t2_e6_excludes_node6.1 ⟨x, by simpa [e7SimpleE_six] using hx⟩

theorem f2_t2_serre_ad2_zero_vs_ad1_nonzero :
    ⁅e7SimpleE 5, ⁅e7SimpleE 5, e7SimpleE 6⁆⁆ = 0 ∧
    ⁅e7SimpleE 5, e7SimpleE 6⁆ ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have h := e7Simple_serre_E (i := (5 : Fin 7)) (j := 6) (by decide)
    rw [h3zornE7_cartan_eq_mathlib] at h
    have hc : (1 - CartanMatrix.E 7 5 6).toNat = 2 := by decide
    simpa [hc] using h
  · intro h0
    have he := congrArg (fun X : H3ZornTKKLie => ⁅e7SimpleF 5, X⁆) h0
    rw [lie_zero, leibniz_lie, ← lie_skew (e7SimpleF 5) (e7SimpleE 5), e7Simple_bracket_EF_same] at he
    have hne : (5 : Fin 7) ≠ 6 := by decide
    rw [← lie_skew (e7SimpleF 5) (e7SimpleE 6), e7Simple_bracket_EF_ne hne.symm, neg_zero,
      lie_zero, add_zero, neg_lie, e7Simple_bracket_HE, h3zornE7_cartan_eq_mathlib] at he
    have hc : CartanMatrix.E 7 5 6 = -1 := by decide
    rw [hc] at he
    have h6z : e7SimpleE 6 = 0 := by
      have hpos : e7SimpleE 6 = 0 := by simpa using he
      exact hpos
    exact e7RootVec_ne_zero (e7ESimpleIdx 6) (by rwa [← e7SimpleE_eq_rootVec])

theorem f2_t2_semisimple_H6_vs_nilpotent_E6 :
    ⁅e7SimpleH 6, e7SimpleE 6⁆ = (2 : ℝ) • e7SimpleE 6 ∧
    ⁅e7SimpleH 6, e7SimpleE 6⁆ ≠ 0 ∧
    ⁅e7SimpleE 6, ⁅e7SimpleE 6, ⁅e7SimpleE 6, e7SimpleF 6⁆⁆⁆ = 0 := by
  have hHE : ⁅e7SimpleH 6, e7SimpleE 6⁆ = (2 : ℝ) • e7SimpleE 6 := by
    rw [e7Simple_bracket_HE, h3zornE7_cartan_eq_mathlib]
    have hc : CartanMatrix.E 7 6 6 = 2 := by decide
    rw [hc]; simp
  refine ⟨hHE, ?_, ?_⟩
  · rw [hHE]
    intro h0
    have he := (smul_eq_zero.mp h0).resolve_left (by norm_num)
    exact e7RootVec_ne_zero (e7ESimpleIdx 6) (by rwa [← e7SimpleE_eq_rootVec])
  · rw [e7Simple_bracket_EF_same, ← lie_skew (e7SimpleE 6) (e7SimpleH 6), hHE]
    simp [lie_self]

/-! ### Feature 3: `E₇` Serre `finrank = 133`, `h3zornE7SerreEquiv`, `IsSimple ℝ` -/

theorem f3_t1_finrank_le_and_eq_133 :
    Module.finrank ℝ (LieAlgebra.e₇ ℝ) ≤ 133 ∧
    Module.finrank ℝ (LieAlgebra.e₇ ℝ) = 133 :=
  ⟨finrank_e7_serre_le, finrank_e7_serre⟩

theorem f3_t1_serre_equiv_bijective_and_bracket (x y : LieAlgebra.e₇ ℝ) :
    Function.Bijective h3zornE7SerreEquiv ∧
    h3zornE7SerreEquiv ⁅x, y⁆ = ⁅h3zornE7SerreEquiv x, h3zornE7SerreEquiv y⁆ :=
  ⟨h3zornE7SerreEquiv.bijective, h3zornE7SerreEquiv.map_lie x y⟩

theorem f3_t1_isSimple : LieAlgebra.IsSimple ℝ (LieAlgebra.e₇ ℝ) :=
  e7Serre_isSimple

theorem f3_t1_isKilling_and_center_bot :
    LieAlgebra.IsKilling ℝ (LieAlgebra.e₇ ℝ) ∧
    LieAlgebra.center ℝ (LieAlgebra.e₇ ℝ) = ⊥ := by
  have hk : LieAlgebra.IsKilling ℝ (LieAlgebra.e₇ ℝ) :=
    LieEquiv.isKilling h3zornE7SerreEquiv.symm
  exact ⟨hk, LieAlgebra.center_eq_bot ℝ (LieAlgebra.e₇ ℝ)⟩

theorem f3_t1_serre_equiv_sl2_triple (i : Fin 7) :
    IsSl2Triple (qE7H i) (qE7E i) (qE7F i) := by
  have ht := e7Simple_isSl2Triple i
  have hH : h3zornE7SerreEquiv (qE7H i) = e7SimpleH i := h3zornE7SerreQuotientMap_H i
  have hE : h3zornE7SerreEquiv (qE7E i) = e7SimpleE i := h3zornE7SerreQuotientMap_E i
  have hF : h3zornE7SerreEquiv (qE7F i) = e7SimpleF i := h3zornE7SerreQuotientMap_F i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    apply ht.h_ne_zero
    have h1 := congrArg h3zornE7SerreEquiv h0
    rw [hH, map_zero] at h1
    exact h1
  · apply h3zornE7SerreEquiv.injective
    change h3zornE7SerreEquiv ⁅qE7E i, qE7F i⁆ = h3zornE7SerreEquiv (qE7H i)
    rw [LieEquiv.map_lie, hE, hF, hH]
    exact ht.lie_e_f
  · apply h3zornE7SerreEquiv.injective
    change h3zornE7SerreEquiv ⁅qE7H i, qE7E i⁆ = h3zornE7SerreEquiv (2 • qE7E i)
    rw [LieEquiv.map_lie, map_nsmul, hH, hE]
    exact ht.lie_h_e_nsmul
  · apply h3zornE7SerreEquiv.injective
    change h3zornE7SerreEquiv ⁅qE7H i, qE7F i⁆ = h3zornE7SerreEquiv (-(2 • qE7F i))
    rw [LieEquiv.map_lie, map_neg, map_nsmul, hH, hF]
    exact ht.lie_h_f_nsmul

theorem f3_t2_ideal_dichotomy (I : LieIdeal ℝ (LieAlgebra.e₇ ℝ)) (hI : I ≠ ⊥) :
    I = ⊤ :=
  (LieAlgebra.IsSimple.eq_bot_or_eq_top I).resolve_left hI

theorem f3_t2_killingForm_zero_vs_nondeg :
    (∀ x : LieAlgebra.e₇ ℝ, killingForm ℝ (LieAlgebra.e₇ ℝ) 0 x = 0) ∧
    (∀ x : LieAlgebra.e₇ ℝ, x ≠ 0 → ∃ y : LieAlgebra.e₇ ℝ,
      killingForm ℝ (LieAlgebra.e₇ ℝ) x y ≠ 0) := by
  have hk : LieAlgebra.IsKilling ℝ (LieAlgebra.e₇ ℝ) :=
    LieEquiv.isKilling h3zornE7SerreEquiv.symm
  refine ⟨fun x => by simp, fun x hx => ?_⟩
  have hnd : (killingForm ℝ (LieAlgebra.e₇ ℝ)).Nondegenerate :=
    LieAlgebra.IsKilling.killingForm_nondegenerate ℝ (LieAlgebra.e₇ ℝ)
  by_contra h
  push Not at h
  exact hx (hnd.1 x h)

theorem f3_t2_cartan_det_two_and_hasTrivialRadical :
    (CartanMatrix.E 7).det = 2 ∧
    LieAlgebra.HasTrivialRadical ℝ (LieAlgebra.e₇ ℝ) := by
  have hk : LieAlgebra.IsKilling ℝ (LieAlgebra.e₇ ℝ) :=
    LieEquiv.isKilling h3zornE7SerreEquiv.symm
  refine ⟨?_, inferInstance⟩
  simpa using CartanMatrix.E_det (by norm_num : 3 ≤ 7)

theorem f3_t2_not_equiv_e6 :
    IsEmpty (LieAlgebra.e₇ ℝ ≃ₗ⁅ℝ⁆ LieAlgebra.e₆ ℝ) := by
  refine ⟨fun e => ?_⟩
  have hfin := LinearEquiv.finrank_eq e.toLinearEquiv
  rw [finrank_e7_serre, finrank_e6_serre] at hfin
  omega

theorem f3_t2_symm_zero_and_noncomm_witness :
    h3zornE7SerreEquiv.symm 0 = 0 ∧
    ⁅qE7H 6, qE7E 6⁆ ≠ 0 := by
  refine ⟨map_zero _, ?_⟩
  intro h0
  have h1 := congrArg h3zornE7SerreEquiv h0
  rw [LieEquiv.map_lie, map_zero] at h1
  change ⁅h3zornE7SerreQuotientMap (qE7H 6), h3zornE7SerreQuotientMap (qE7E 6)⁆ = 0 at h1
  rw [h3zornE7SerreQuotientMap_H, h3zornE7SerreQuotientMap_E, e7Simple_bracket_HE,
    h3zornE7_cartan_eq_mathlib] at h1
  have hc : CartanMatrix.E 7 6 6 = 2 := by decide
  rw [hc] at h1
  have h2 : (2 : ℝ) • e7SimpleE 6 = 0 := by simpa using h1
  have he := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact e7RootVec_ne_zero (e7ESimpleIdx 6) (by rwa [← e7SimpleE_eq_rootVec])

/-! =========================================================================
    TIER 1 & TIER 2: R2 — `InfoGeometry.Algebra.SplitE8SerreHom` (F4–F6)
    ========================================================================= -/

/-! ### Feature 4: Split `E₈` Serre relations (`e8Simple_serre_E`, `e8Simple_serre_F`) -/

theorem f4_t1_serre_E_adjacent_edges :
    ⁅e8SimpleE 0, ⁅e8SimpleE 0, e8SimpleE 2⁆⁆ = 0 ∧
    ⁅e8SimpleE 1, ⁅e8SimpleE 1, e8SimpleE 3⁆⁆ = 0 ∧
    ⁅e8SimpleE 5, ⁅e8SimpleE 5, e8SimpleE 6⁆⁆ = 0 ∧
    ⁅e8SimpleE 6, ⁅e8SimpleE 6, e8SimpleE 7⁆⁆ = 0 := by
  have h02 := e8Simple_serre_E (i := (0 : Fin 8)) (j := 2) (by decide)
  have h13 := e8Simple_serre_E (i := (1 : Fin 8)) (j := 3) (by decide)
  have h56 := e8Simple_serre_E (i := (5 : Fin 8)) (j := 6) (by decide)
  have h67 := e8Simple_serre_E (i := (6 : Fin 8)) (j := 7) (by decide)
  rw [splitE8_cartan_eq_mathlib] at h02 h13 h56 h67
  have c02 : (1 - CartanMatrix.E 8 0 2).toNat = 2 := by decide
  have c13 : (1 - CartanMatrix.E 8 1 3).toNat = 2 := by decide
  have c56 : (1 - CartanMatrix.E 8 5 6).toNat = 2 := by decide
  have c67 : (1 - CartanMatrix.E 8 6 7).toNat = 2 := by decide
  rw [c02] at h02; rw [c13] at h13; rw [c56] at h56; rw [c67] at h67
  exact ⟨by simpa using h02, by simpa using h13, by simpa using h56, by simpa using h67⟩

theorem f4_t1_serre_F_adjacent_edges :
    ⁅e8SimpleF 0, ⁅e8SimpleF 0, e8SimpleF 2⁆⁆ = 0 ∧
    ⁅e8SimpleF 1, ⁅e8SimpleF 1, e8SimpleF 3⁆⁆ = 0 ∧
    ⁅e8SimpleF 5, ⁅e8SimpleF 5, e8SimpleF 6⁆⁆ = 0 ∧
    ⁅e8SimpleF 6, ⁅e8SimpleF 6, e8SimpleF 7⁆⁆ = 0 := by
  have h02 := e8Simple_serre_F (i := (0 : Fin 8)) (j := 2) (by decide)
  have h13 := e8Simple_serre_F (i := (1 : Fin 8)) (j := 3) (by decide)
  have h56 := e8Simple_serre_F (i := (5 : Fin 8)) (j := 6) (by decide)
  have h67 := e8Simple_serre_F (i := (6 : Fin 8)) (j := 7) (by decide)
  rw [splitE8_cartan_eq_mathlib] at h02 h13 h56 h67
  have c02 : (1 - CartanMatrix.E 8 0 2).toNat = 2 := by decide
  have c13 : (1 - CartanMatrix.E 8 1 3).toNat = 2 := by decide
  have c56 : (1 - CartanMatrix.E 8 5 6).toNat = 2 := by decide
  have c67 : (1 - CartanMatrix.E 8 6 7).toNat = 2 := by decide
  rw [c02] at h02; rw [c13] at h13; rw [c56] at h56; rw [c67] at h67
  exact ⟨by simpa using h02, by simpa using h13, by simpa using h56, by simpa using h67⟩

theorem f4_t1_cartan_chevalley_relations (i j : Fin 8) :
    ⁅e8SimpleH i, e8SimpleH j⁆ = 0 ∧
    ⁅e8SimpleE i, e8SimpleF i⁆ = e8SimpleH i ∧
    ⁅e8SimpleH i, e8SimpleE j⁆ = ((CartanMatrix.E 8 i j : ℤ) : ℝ) • e8SimpleE j ∧
    ⁅e8SimpleH i, e8SimpleF j⁆ = (-(CartanMatrix.E 8 i j : ℤ) : ℝ) • e8SimpleF j := by
  refine ⟨e8SimpleH_comm i j, e8Simple_bracket_EF_same i, ?_, ?_⟩
  · rw [e8Simple_bracket_HE, splitE8_cartan_eq_mathlib]
  · rw [e8Simple_bracket_HF, splitE8_cartan_eq_mathlib]

theorem f4_t1_ad1_sharpness_adjacent :
    ⁅e8SimpleE 6, e8SimpleE 7⁆ ≠ 0 ∧
    ⁅e8SimpleF 1, e8SimpleF 3⁆ ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro h0
    have he := congrArg (fun X : SplitE8Lie => ⁅e8SimpleF 6, X⁆) h0
    rw [lie_zero, leibniz_lie, ← lie_skew (e8SimpleF 6) (e8SimpleE 6), e8Simple_bracket_EF_same] at he
    have hne : (6 : Fin 8) ≠ 7 := by decide
    rw [← lie_skew (e8SimpleF 6) (e8SimpleE 7), e8Simple_bracket_EF_ne hne.symm, neg_zero,
      lie_zero, add_zero, neg_lie, e8Simple_bracket_HE, splitE8_cartan_eq_mathlib] at he
    have hc : CartanMatrix.E 8 6 7 = -1 := by decide
    rw [hc] at he
    have h7z : e8SimpleE 7 = 0 := by simpa using he
    exact e8RootVec_ne_zero (e8ESimpleIdx 7) (by rwa [← e8SimpleE_eq_rootVec])
  · intro h0
    have he := congrArg (fun X : SplitE8Lie => ⁅e8SimpleE 1, X⁆) h0
    rw [lie_zero, leibniz_lie, e8Simple_bracket_EF_same] at he
    have hne : (1 : Fin 8) ≠ 3 := by decide
    rw [e8Simple_bracket_EF_ne hne, lie_zero, add_zero, e8Simple_bracket_HF,
      splitE8_cartan_eq_mathlib] at he
    have hc : CartanMatrix.E 8 1 3 = -1 := by decide
    rw [hc] at he
    have h3z : e8SimpleF 3 = 0 := by simpa using he
    have h3s : e8SimpleF 3 = e8FSimpleScale 3 • e8RootVec (e8FSimpleIdx 3) :=
      e8SimpleF_eq_rootVec 3
    rw [h3s] at h3z
    have hs3 : e8FSimpleScale 3 = 1 := rfl
    rw [hs3, one_smul] at h3z
    exact e8RootVec_ne_zero (e8FSimpleIdx 3) h3z

theorem f4_t1_nonadjacent_commutation :
    ⁅e8SimpleE 0, e8SimpleE 7⁆ = 0 ∧
    ⁅e8SimpleF 0, e8SimpleF 1⁆ = 0 := by
  have hE := e8Simple_serre_E (i := (0 : Fin 8)) (j := 7) (by decide)
  have hF := e8Simple_serre_F (i := (0 : Fin 8)) (j := 1) (by decide)
  rw [splitE8_cartan_eq_mathlib] at hE hF
  have cE : (1 - CartanMatrix.E 8 0 7).toNat = 1 := by decide
  have cF : (1 - CartanMatrix.E 8 0 1).toNat = 1 := by decide
  rw [cE] at hE; rw [cF] at hF
  exact ⟨by simpa using hE, by simpa using hF⟩

theorem f4_t2_diag_cartan_and_free_serre_adE (i j : Fin 8) :
    CartanMatrix.E 8 i i = 2 ∧
    splitE8FreeSerreEval (CartanMatrix.Relations.adE ℝ (CartanMatrix.E 8) (i, j)) = 0 :=
  ⟨CartanMatrix.E_diag 8 i, splitE8FreeSerreEval_adE i j⟩

theorem f4_t2_nonadj_commute_deg1 :
    ⁅e8SimpleE 0, e8SimpleE 1⁆ = 0 ∧
    ⁅e8SimpleE 1, e8SimpleE 7⁆ = 0 ∧
    ⁅e8SimpleF 0, e8SimpleF 7⁆ = 0 := by
  have h01 := e8Simple_serre_E (i := (0 : Fin 8)) (j := 1) (by decide)
  have h17 := e8Simple_serre_E (i := (1 : Fin 8)) (j := 7) (by decide)
  have h07 := e8Simple_serre_F (i := (0 : Fin 8)) (j := 7) (by decide)
  rw [splitE8_cartan_eq_mathlib] at h01 h17 h07
  have c01 : (1 - CartanMatrix.E 8 0 1).toNat = 1 := by decide
  have c17 : (1 - CartanMatrix.E 8 1 7).toNat = 1 := by decide
  have c07 : (1 - CartanMatrix.E 8 0 7).toNat = 1 := by decide
  rw [c01] at h01; rw [c17] at h17; rw [c07] at h07
  exact ⟨by simpa using h01, by simpa using h17, by simpa using h07⟩

theorem f4_t2_adjacent_ad2_zero_and_ad1_nonzero :
    ⁅e8SimpleE 5, ⁅e8SimpleE 5, e8SimpleE 6⁆⁆ = 0 ∧
    ⁅e8SimpleE 5, e8SimpleE 6⁆ ≠ 0 := by
  refine ⟨f4_t1_serre_E_adjacent_edges.2.2.1, ?_⟩
  intro h0
  have he := congrArg (fun X : SplitE8Lie => ⁅e8SimpleF 5, X⁆) h0
  rw [lie_zero, leibniz_lie, ← lie_skew (e8SimpleF 5) (e8SimpleE 5), e8Simple_bracket_EF_same] at he
  have hne : (5 : Fin 8) ≠ 6 := by decide
  rw [← lie_skew (e8SimpleF 5) (e8SimpleE 6), e8Simple_bracket_EF_ne hne.symm, neg_zero,
    lie_zero, add_zero, neg_lie, e8Simple_bracket_HE, splitE8_cartan_eq_mathlib] at he
  have hc : CartanMatrix.E 8 5 6 = -1 := by decide
  rw [hc] at he
  have h6z : e8SimpleE 6 = 0 := by simpa using he
  exact e8RootVec_ne_zero (e8ESimpleIdx 6) (by rwa [← e8SimpleE_eq_rootVec])

theorem f4_t2_asymmetric_scale_EF {i j : Fin 8} (hij : i ≠ j) :
    e8FSimpleScale 0 = 1 / 4 ∧
    e8FSimpleScale 1 = -1 ∧
    e8FSimpleScale 3 = 1 ∧
    ⁅e8SimpleE i, e8SimpleF i⁆ = e8SimpleH i ∧
    ⁅e8SimpleE i, e8SimpleF j⁆ = 0 :=
  ⟨rfl, rfl, rfl, e8Simple_bracket_EF_same i, e8Simple_bracket_EF_ne hij⟩

theorem f4_t2_sl2_ad3_vanishing (i : Fin 8) :
    ⁅e8SimpleE i, ⁅e8SimpleE i, ⁅e8SimpleE i, e8SimpleF i⁆⁆⁆ = 0 := by
  rw [e8Simple_bracket_EF_same, ← lie_skew (e8SimpleE i) (e8SimpleH i), e8Simple_bracket_HE,
    splitE8_cartan_eq_mathlib, CartanMatrix.E_diag 8 i]
  simp [lie_self]

/-! ### Feature 5: Split `E₈` generators generate & surjectivity -/

theorem f5_t1_rootVec_in_closure (r : Fin 240) :
    e8RootVec r ∈
      LieSubalgebra.lieSpan ℝ SplitE8Lie
        (Set.range e8SimpleH ∪ Set.range e8SimpleE ∪ Set.range e8SimpleF) := by
  rw [splitE8_simple_generators_lieSpan_eq_top]
  trivial

theorem f5_t1_surjective_chevalleyBasis (k : Fin 8 ⊕ Fin 240) :
    ∃ x : LieAlgebra.e₈ ℝ, splitE8SerreQuotientMap x = e8ChevalleyBasis k :=
  splitE8SerreQuotientMap_surjective (e8ChevalleyBasis k)

theorem f5_t1_highest_root_in_closure :
    e8RootVec e8HighestRootIdx ∈
      LieSubalgebra.lieSpan ℝ SplitE8Lie
        (Set.range e8SimpleH ∪ Set.range e8SimpleE ∪ Set.range e8SimpleF) :=
  f5_t1_rootVec_in_closure e8HighestRootIdx

theorem f5_t1_g2_f4_in_range (D : G2DerivationCarrier) (E : F4DerivationCarrier) :
    embedG2 D ∈ Set.range splitE8SerreQuotientMap ∧
    embedF4 E ∈ Set.range splitE8SerreQuotientMap :=
  ⟨splitE8SerreQuotientMap_surjective (embedG2 D),
    splitE8SerreQuotientMap_surjective (embedF4 E)⟩

theorem f5_t1_cartan_eq_span_qH :
    splitE8Cartan.toSubmodule =
      Submodule.span ℝ (Set.range (fun i : Fin 8 => splitE8SerreQuotientMap (qE8H i))) := by
  simp only [splitE8SerreQuotientMap_H]
  exact splitE8Cartan_eq_span_e8SimpleH

theorem f5_t2_e7_nodes_cartan_strictly_lt_top :
    Submodule.span ℝ (Set.range (fun i : Fin 7 => e8SimpleH i.castSucc)) <
      splitE8Cartan.toSubmodule := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact e8SimpleH_mem_splitE8Cartan i.castSucc
  · intro heq
    have hfin := congrArg (fun S : Submodule ℝ SplitE8Lie => Module.finrank ℝ S) heq
    have hle : Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun i : Fin 7 => e8SimpleH i.castSucc))) ≤ 7 := by
      have h0 := finrank_range_le_card (fun i : Fin 7 => e8SimpleH i.castSucc) (R := ℝ)
      simpa [Set.finrank] using h0
    change Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin 7 => e8SimpleH i.castSucc))) =
      Module.finrank ℝ splitE8Cartan at hfin
    rw [finrank_splitE8Cartan] at hfin
    omega

theorem f5_t2_g2_sup_f4_strictly_lt_top :
    (LinearMap.range embedG2.toLinearMap ⊔ LinearMap.range embedF4.toLinearMap : Submodule ℝ SplitE8Lie) < ⊤ ∧
    e8SimpleE 5 ∉ (LinearMap.range embedG2.toLinearMap ⊔ LinearMap.range embedF4.toLinearMap : Submodule ℝ SplitE8Lie) := by
  refine ⟨?_, ?_⟩
  · rw [lt_top_iff_ne_top]
    intro htop
    have : Module.Finite ℝ G2DerivationCarrier :=
      FiniteDimensional.of_finrank_pos (by rw [finrank_g2DerivationCarrier]; norm_num)
    have : Module.Finite ℝ F4DerivationCarrier :=
      FiniteDimensional.of_finrank_pos (by rw [finrank_f4DerivationCarrier]; norm_num)
    have hg2 : Module.finrank ℝ (LinearMap.range embedG2.toLinearMap) ≤ 14 := by
      have h := LinearMap.finrank_range_le (R := ℝ) embedG2.toLinearMap
      rwa [finrank_g2DerivationCarrier] at h
    have hf4 : Module.finrank ℝ (LinearMap.range embedF4.toLinearMap) ≤ 52 := by
      have h := LinearMap.finrank_range_le (R := ℝ) embedF4.toLinearMap
      rwa [finrank_f4DerivationCarrier] at h
    have hinf : Module.finrank ℝ
        (LinearMap.range embedG2.toLinearMap ⊔ LinearMap.range embedF4.toLinearMap :
          Submodule ℝ SplitE8Lie) = 248 := by
      rw [htop, finrank_top, finrank_splitE8Lie]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range embedG2.toLinearMap) (LinearMap.range embedF4.toLinearMap)
    omega
  · intro hmem
    rcases Submodule.mem_sup.mp hmem with ⟨_, ⟨D, rfl⟩, _, ⟨E, rfl⟩, hDE⟩
    have hm := congrArg projMixed hDE
    have he5 : e8SimpleE 5 = embedTensor (zornU 1) (h3TraceZeroOff 1) := rfl
    rw [he5] at hm
    change (embedG2 D).mixed + (embedF4 E).mixed =
      (embedTensor (zornU 1) (h3TraceZeroOff 1)).mixed at hm
    simp only [embedG2_apply, embedF4_apply, embedTensor_apply, embedMixed_apply, add_zero] at hm
    have he50 : e8SimpleE 5 = 0 := by
      rw [he5, embedTensor_apply, ← hm]
      apply SplitE8Lie.ext <;> simp [embedMixed_apply]
    exact e8RootVec_ne_zero (e8ESimpleIdx 5) (by rwa [← e8SimpleE_eq_rootVec])

theorem f5_t2_zero_in_closure_and_generators_generate (S : LieSubalgebra ℝ SplitE8Lie)
    (hH : ∀ i : Fin 8, e8SimpleH i ∈ S)
    (hE : ∀ i : Fin 8, e8SimpleE i ∈ S)
    (hF : ∀ i : Fin 8, e8SimpleF i ∈ S) :
    (0 : SplitE8Lie) ∈
      LieSubalgebra.lieSpan ℝ SplitE8Lie
        (Set.range e8SimpleH ∪ Set.range e8SimpleE ∪ Set.range e8SimpleF) ∧
    S = ⊤ :=
  ⟨Submodule.zero_mem _, splitE8_simple_generators_generate S hH hE hF⟩

theorem f5_t2_node7_EF_nonzero_bracket :
    ⁅e8SimpleE 7, e8SimpleF 7⁆ = e8SimpleH 7 ∧ e8SimpleH 7 ≠ 0 := by
  refine ⟨e8Simple_bracket_EF_same 7, ?_⟩
  intro h0
  have he := e8Simple_bracket_HE 7 7
  rw [h0, zero_lie, splitE8_cartan_eq_mathlib] at he
  have hc : CartanMatrix.E 8 7 7 = 2 := by decide
  rw [hc] at he
  have h2 : (2 : ℝ) • e8SimpleE 7 = 0 := by simpa using he.symm
  have h7z : e8SimpleE 7 = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact e8RootVec_ne_zero (e8ESimpleIdx 7) (by rwa [← e8SimpleE_eq_rootVec])

theorem f5_t2_semisimple_H7_vs_nilpotent_E7 :
    ⁅e8SimpleH 7, e8SimpleE 7⁆ = (2 : ℝ) • e8SimpleE 7 ∧
    ⁅e8SimpleH 7, e8SimpleE 7⁆ ≠ 0 ∧
    ⁅e8SimpleE 7, ⁅e8SimpleE 7, ⁅e8SimpleE 7, e8SimpleF 7⁆⁆⁆ = 0 := by
  have hHE : ⁅e8SimpleH 7, e8SimpleE 7⁆ = (2 : ℝ) • e8SimpleE 7 := by
    rw [e8Simple_bracket_HE, splitE8_cartan_eq_mathlib]
    have hc : CartanMatrix.E 8 7 7 = 2 := by decide
    rw [hc]; simp
  refine ⟨hHE, ?_, f4_t2_sl2_ad3_vanishing 7⟩
  rw [hHE]
  intro h0
  have he := (smul_eq_zero.mp h0).resolve_left (by norm_num)
  exact e8RootVec_ne_zero (e8ESimpleIdx 7) (by rwa [← e8SimpleE_eq_rootVec])

/-! ### Feature 6: `E₈` Serre `finrank = 248`, `splitE8SerreEquiv`, `IsSimple ℝ` -/

theorem f6_t1_finrank_le_and_eq_248 :
    Module.finrank ℝ (LieAlgebra.e₈ ℝ) ≤ 248 ∧
    Module.finrank ℝ (LieAlgebra.e₈ ℝ) = 248 :=
  ⟨finrank_e8_serre_le, finrank_e8_serre⟩

theorem f6_t1_serre_equiv_sl2_triple (i : Fin 8) :
    IsSl2Triple (qE8H i) (qE8E i) (qE8F i) := by
  have ht := e8Simple_isSl2Triple i
  have hH : splitE8SerreEquiv (qE8H i) = e8SimpleH i := splitE8SerreQuotientMap_H i
  have hE : splitE8SerreEquiv (qE8E i) = e8SimpleE i := splitE8SerreQuotientMap_E i
  have hF : splitE8SerreEquiv (qE8F i) = e8SimpleF i := splitE8SerreQuotientMap_F i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    apply ht.h_ne_zero
    have h1 := congrArg splitE8SerreEquiv h0
    rw [hH, map_zero] at h1
    exact h1
  · apply splitE8SerreEquiv.injective
    change splitE8SerreEquiv ⁅qE8E i, qE8F i⁆ = splitE8SerreEquiv (qE8H i)
    rw [LieEquiv.map_lie, hE, hF, hH]
    exact ht.lie_e_f
  · apply splitE8SerreEquiv.injective
    change splitE8SerreEquiv ⁅qE8H i, qE8E i⁆ = splitE8SerreEquiv (2 • qE8E i)
    rw [LieEquiv.map_lie, map_nsmul, hH, hE]
    exact ht.lie_h_e_nsmul
  · apply splitE8SerreEquiv.injective
    change splitE8SerreEquiv ⁅qE8H i, qE8F i⁆ = splitE8SerreEquiv (-(2 • qE8F i))
    rw [LieEquiv.map_lie, map_neg, map_nsmul, hH, hF]
    exact ht.lie_h_f_nsmul

theorem f6_t1_isSimple : LieAlgebra.IsSimple ℝ (LieAlgebra.e₈ ℝ) :=
  e8Serre_isSimple

theorem f6_t1_isKilling_and_center_bot :
    LieAlgebra.IsKilling ℝ (LieAlgebra.e₈ ℝ) ∧
    LieAlgebra.center ℝ (LieAlgebra.e₈ ℝ) = ⊥ := by
  have hk : LieAlgebra.IsKilling ℝ (LieAlgebra.e₈ ℝ) :=
    LieEquiv.isKilling splitE8SerreEquiv.symm
  exact ⟨hk, LieAlgebra.center_eq_bot ℝ (LieAlgebra.e₈ ℝ)⟩

theorem f6_t1_serre_equiv_bijective_and_bracket (x y : LieAlgebra.e₈ ℝ) :
    Function.Bijective splitE8SerreEquiv ∧
    splitE8SerreEquiv ⁅x, y⁆ = ⁅splitE8SerreEquiv x, splitE8SerreEquiv y⁆ :=
  ⟨splitE8SerreEquiv.bijective, splitE8SerreEquiv.map_lie x y⟩

theorem f6_t2_not_equiv_e7_and_e6 :
    IsEmpty (LieAlgebra.e₈ ℝ ≃ₗ⁅ℝ⁆ LieAlgebra.e₇ ℝ) ∧
    IsEmpty (LieAlgebra.e₈ ℝ ≃ₗ⁅ℝ⁆ LieAlgebra.e₆ ℝ) := by
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩
  · have hfin := LinearEquiv.finrank_eq e.toLinearEquiv
    rw [finrank_e8_serre, finrank_e7_serre] at hfin
    omega
  · have hfin := LinearEquiv.finrank_eq e.toLinearEquiv
    rw [finrank_e8_serre, finrank_e6_serre] at hfin
    omega

theorem f6_t2_cartan_det_one : (CartanMatrix.E 8).det = 1 := by
  simpa using CartanMatrix.E_det (by norm_num : 3 ≤ 8)

theorem f6_t2_killingForm_nondegenerate :
    (killingForm ℝ (LieAlgebra.e₈ ℝ)).Nondegenerate ∧
    ∀ x : LieAlgebra.e₈ ℝ, x ≠ 0 → ∃ y : LieAlgebra.e₈ ℝ, killingForm ℝ (LieAlgebra.e₈ ℝ) x y ≠ 0 := by
  have hk : LieAlgebra.IsKilling ℝ (LieAlgebra.e₈ ℝ) :=
    LieEquiv.isKilling splitE8SerreEquiv.symm
  have hnd : (killingForm ℝ (LieAlgebra.e₈ ℝ)).Nondegenerate :=
    LieAlgebra.IsKilling.killingForm_nondegenerate ℝ (LieAlgebra.e₈ ℝ)
  refine ⟨hnd, fun x hx => ?_⟩
  by_contra h
  push Not at h
  exact hx (hnd.1 x h)

theorem f6_t2_ideal_dichotomy (I : LieIdeal ℝ (LieAlgebra.e₈ ℝ)) :
    I = ⊥ ∨ I = ⊤ :=
  LieAlgebra.IsSimple.eq_bot_or_eq_top I

theorem f6_t2_symm_zero_and_noncomm_witness :
    splitE8SerreEquiv.symm 0 = 0 ∧ ⁅qE8H 0, qE8E 0⁆ ≠ 0 := by
  refine ⟨map_zero _, ?_⟩
  intro h0
  have h1 := congrArg splitE8SerreEquiv h0
  rw [LieEquiv.map_lie, map_zero] at h1
  change ⁅splitE8SerreQuotientMap (qE8H 0), splitE8SerreQuotientMap (qE8E 0)⁆ = 0 at h1
  rw [splitE8SerreQuotientMap_H, splitE8SerreQuotientMap_E] at h1
  exact e8_noncomm_witness h1

/-! =========================================================================
    TIER 1 & TIER 2: R3 — `CompactOctonionG2Derivations` & `CompactE8MagicSquare` (F7–F10)
    ========================================================================= -/

/-! ### Feature 7: Compact `𝔤₂(-14)` derivations -/

theorem f7_t1_finrank_14 :
    Module.finrank ℝ CompactOctonionDerivations = 14 :=
  finrank_compactOctonionDerivations

theorem f7_t1_leibniz_and_one_zero (D : CompactOctonionDerivations) (x y : CompactOctonion ℝ) :
    D.1 (CompactOctonion.mul x y) =
      CompactOctonion.mul (D.1 x) y + CompactOctonion.mul x (D.1 y) ∧
    D.1 1 = 0 :=
  ⟨(mem_compactOctonionDerivations D.1).mp D.2 x y, compactOctonion_derivation_apply_one_eq_zero D⟩

theorem f7_t1_bilin_skew_and_conj (D : CompactOctonionDerivations) (x y : CompactOctonion ℝ) :
    CompactOctonion.bilin (D.1 x) y + CompactOctonion.bilin x (D.1 y) = 0 ∧
    D.1 (CompactOctonion.conj x) = CompactOctonion.conj (D.1 x) :=
  ⟨compactOctonion_derivation_bilin_skew D x y, compactOctonion_derivation_conj D x⟩

theorem f7_t1_trace_sq_nonpos (D : CompactOctonionDerivations) :
    LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) ≤ 0 :=
  compactG2_trace_sq_nonpos D

theorem f7_t1_trace_sq_eq_zero_iff_and_nonzero_witness :
    (∀ D : CompactOctonionDerivations,
      LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) = 0 ↔ D = 0) ∧
    (∃ D : CompactOctonionDerivations,
      D ≠ 0 ∧ LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) < 0) := by
  refine ⟨compactG2_trace_sq_eq_zero_iff, compactG2WitnessD1, compactG2WitnessD1_ne_zero, ?_⟩
  exact lt_of_le_of_ne (compactG2_trace_sq_nonpos compactG2WitnessD1)
    (mt (compactG2_trace_sq_eq_zero_iff compactG2WitnessD1).mp compactG2WitnessD1_ne_zero)

theorem f7_t2_trace_sq_zero :
    LinearMap.trace ℝ (CompactOctonion ℝ)
      ((0 : CompactOctonionDerivations).1 * (0 : CompactOctonionDerivations).1) = 0 :=
  (compactG2_trace_sq_eq_zero_iff 0).mpr rfl

theorem f7_t2_one_mem_ker_all (D : CompactOctonionDerivations) :
    (1 : CompactOctonion ℝ) ∈ LinearMap.ker D.1 :=
  compactOctonion_derivation_apply_one_eq_zero D

theorem f7_t2_nonabelian_witness :
    ∃ D₁ D₂ : CompactOctonionDerivations, ⁅D₁, D₂⁆ ≠ 0 := by
  by_contra h
  push Not at h
  have habC : ∀ x y : ℂ ⊗[ℝ] CompactOctonionDerivations, ⁅x, y⁆ = 0 := by
    intro x y
    induction x using TensorProduct.inductionOn generalizing y with
    | tmul z₁ d₁ =>
      induction y using TensorProduct.inductionOn with
      | tmul z₂ d₂ =>
        rw [LieAlgebra.ExtendScalars.bracket_tmul, h d₁ d₂, TensorProduct.tmul_zero]
      | add a b ha hb =>
        have hadd : ⁅z₁ ⊗ₜ[ℝ] d₁, a + b⁆ = ⁅z₁ ⊗ₜ[ℝ] d₁, a⁆ + ⁅z₁ ⊗ₜ[ℝ] d₁, b⁆ :=
          lie_add (z₁ ⊗ₜ[ℝ] d₁) a b
        rw [hadd, ha, hb, add_zero]
    | add a b ha hb =>
      have hadd : ⁅a + b, y⁆ = ⁅a, y⁆ + ⁅b, y⁆ := add_lie a b y
      rw [hadd, ha y, hb y, add_zero]
  have habG2 : ∀ u v : ℂ ⊗[ℝ] G2DerivationCarrier, ⁅u, v⁆ = 0 := by
    intro u v
    apply compactG2BaseChangeVDerEquiv.symm.injective
    change compactG2BaseChangeVDerEquiv.symm ⁅u, v⁆ = compactG2BaseChangeVDerEquiv.symm 0
    rw [LieEquiv.map_lie, map_zero]
    exact habC _ _
  have hE6 : e8SimpleE 6 = embedG2 (projG2 (e8SimpleE 6)) := by
    apply SplitE8Lie.ext <;> rfl
  have hF6 : e8SimpleF 6 = embedG2 (projG2 (e8SimpleF 6)) := by
    have hF : e8SimpleF 6 = embedG2 (g2Param 12) := by
      simp [e8SimpleF, e8FSimpleScale, e8FSimpleIdx, e8RootVec, g2LongIdx]
    rw [hF]
    apply SplitE8Lie.ext <;> rfl
  have hbr0 : ⁅projG2 (e8SimpleE 6), projG2 (e8SimpleF 6)⁆ = 0 := by
    have h1 := habG2 ((1 : ℂ) ⊗ₜ[ℝ] projG2 (e8SimpleE 6)) ((1 : ℂ) ⊗ₜ[ℝ] projG2 (e8SimpleF 6))
    rw [LieAlgebra.ExtendScalars.bracket_tmul, mul_one] at h1
    let reMap : (ℂ ⊗[ℝ] G2DerivationCarrier) →ₗ[ℝ] G2DerivationCarrier :=
      (TensorProduct.lid ℝ G2DerivationCarrier).toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.map Complex.reCLM.toLinearMap LinearMap.id)
    have h2 := congrArg reMap h1
    simpa [reMap] using h2
  have hH6 : e8SimpleH 6 = 0 := by
    rw [← e8Simple_bracket_EF_same 6, hE6, hF6, bracket_g2_g2, hbr0, map_zero]
  have he := e8Simple_bracket_HE 6 6
  rw [hH6, zero_lie, splitE8_cartan_eq_mathlib] at he
  have hc : CartanMatrix.E 8 6 6 = 2 := by decide
  rw [hc] at he
  have h2 : (2 : ℝ) • e8SimpleE 6 = 0 := by simpa using he.symm
  have h6z : e8SimpleE 6 = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact e8RootVec_ne_zero (e8ESimpleIdx 6) (by rwa [← e8SimpleE_eq_rootVec])

theorem f7_t2_mul_eq_zero_iff_no_zero_divisors (x y : CompactOctonion ℝ) :
    CompactOctonion.mul x y = 0 ↔ x = 0 ∨ y = 0 :=
  CompactOctonion.mul_eq_zero_iff x y

theorem f7_t2_bilin_pos_def_no_isotropic (x : CompactOctonion ℝ) (hx : x ≠ 0) :
    0 < CompactOctonion.bilin x x := by
  rw [CompactOctonion.bilin_self]
  have hn : 0 < CompactOctonion.norm x :=
    lt_of_le_of_ne (CompactOctonion.norm_nonneg x)
      (fun h => hx ((CompactOctonion.norm_eq_zero_iff x).mp h.symm))
  linarith

/-! ### Feature 8: Compact `𝔈₈(-248)` Magic Square (`CompactE8Lie`) -/

theorem f8_t1_finrank_248 : Module.finrank ℝ CompactE8Lie = 248 :=
  finrank_compactE8Lie

theorem f8_t1_jacobi_and_lie_smul (r : ℝ) (X Y Z : CompactE8Lie) :
    ⁅X, ⁅Y, Z⁆⁆ = ⁅⁅X, Y⁆, Z⁆ + ⁅Y, ⁅X, Z⁆⁆ ∧
    ⁅X, r • Y⁆ = r • ⁅X, Y⁆ :=
  ⟨leibniz_lie X Y Z, lie_smul r X Y⟩

theorem f8_t1_isSimple : LieAlgebra.IsSimple ℝ CompactE8Lie :=
  compactE8Lie_isSimple

theorem f8_t1_isKilling_and_center_bot :
    LieAlgebra.IsKilling ℝ CompactE8Lie ∧
    LieAlgebra.center ℝ CompactE8Lie = ⊥ :=
  ⟨compactE8Lie_isKilling, LieAlgebra.center_eq_bot ℝ CompactE8Lie⟩

theorem f8_t1_g2_f4_embed_and_commute
    (D₁ D₂ : CompactOctonionDerivations) (F₁ F₂ : H3OctonionF4Derivations) :
    msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum ⁅D₁, D₂⁆ =
      ⁅msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum D₁,
        msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum D₂⁆ ∧
    msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum ⁅F₁, F₂⁆ =
      ⁅msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum F₁,
        msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum F₂⁆ ∧
    ⁅msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum D₁,
      msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum F₁⁆ = 0 :=
  ⟨msEmbedG2LM_lie _ _ D₁ D₂, msEmbedF4LM_lie _ _ F₁ F₂,
    msEmbedG2LM_bracket_msEmbedF4LM _ _ D₁ F₁⟩

theorem f8_t2_killingForm_zero :
    killingForm ℝ CompactE8Lie 0 0 = 0 := by
  simp

theorem f8_t2_h3Octonion_formal_reality (x y : H3Octonion ℝ) (h : x * x + y * y = 0) :
    x = 0 ∧ y = 0 :=
  H3Octonion.formal_reality x y h

theorem f8_t2_killingForm_strictly_neg_nonzero (X : CompactE8Lie) (hX : X ≠ 0) :
    killingForm ℝ CompactE8Lie X X < 0 :=
  lt_of_le_of_ne (compactE8_killingForm_nonpos X)
    (fun h => hX ((compactE8_killingForm_eq_zero_iff X).mp h))

theorem f8_t2_g2_f4_not_ideals :
    (∃ D : CompactOctonionDerivations, ∃ X : CompactE8Lie,
      ⁅msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum D, X⁆ ∉
        Set.range (msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum)) ∧
    (∃ F : H3OctonionF4Derivations, ∃ X : CompactE8Lie,
      ⁅msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum F, X⁆ ∉
        Set.range (msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum)) := by
  let o₃ : CompactOctonionTraceZero :=
    ⟨CompactOctonion.basisVec 3, by
      change CompactOctonion.trace (CompactOctonion.basisVec 3) = 0
      simp [CompactOctonion.trace, CompactOctonion.basisVec]⟩
  let j₁ : h3OctonionTraceZero :=
    ⟨H3Octonion.diagCartan 1 0 (-1), by
      change H3Octonion.linearTrace (H3Octonion.diagCartan 1 0 (-1)) = 0
      simp [H3Octonion.linearTrace, H3Octonion.diagCartan]⟩
  let F0 := h3OctonionJordanInnerDerivation
    (H3Octonion.diagCartan (1 : ℝ) 0 0) (H3Octonion.embedJ12 (1 : CompactOctonion ℝ))
  refine ⟨⟨compactG2WitnessD1, msEmbedTensor compactOctonionDatum h3OctonionJordanDatum o₃ j₁, ?_⟩,
    ⟨F0, msEmbedTensor compactOctonionDatum h3OctonionJordanDatum o₃ j₁, ?_⟩⟩
  · rintro ⟨D', hD'⟩
    have hm := congrArg (fun Y : CompactE8Lie =>
      magicMixedBilin compactOctonionDatum h3OctonionJordanDatum
        ((compactG2Act compactG2WitnessD1 o₃) ⊗ₜ[ℝ] j₁) Y.mixed) hD'
    have hbr_mix :
        (⁅msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum compactG2WitnessD1,
          msEmbedTensor compactOctonionDatum h3OctonionJordanDatum o₃ j₁⁆ : CompactE8Lie).mixed =
        (compactG2Act compactG2WitnessD1 o₃) ⊗ₜ[ℝ] j₁ := by
      change (magicSquareBracketLM compactOctonionDatum h3OctonionJordanDatum
        (msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum compactG2WitnessD1)
        (msEmbedMixed compactOctonionDatum h3OctonionJordanDatum (o₃ ⊗ₜ[ℝ] j₁))).mixed = _
      simp [magicSquareBracketLM, msEmbedG2LM, msEmbedMixed]
      rfl
    have hD'm : (msEmbedG2LM compactOctonionDatum h3OctonionJordanDatum D').mixed = 0 := rfl
    rw [hbr_mix, hD'm, map_zero, magicMixedBilin_tmul] at hm
    have ho_nz : (compactG2Act compactG2WitnessD1 o₃).1 ≠ 0 := by
      intro h0
      have he6 := congrArg CompactOctonion.e6 h0
      have hact : (compactG2Act compactG2WitnessD1 o₃).1.e6 = 2 :=
        compactG2WitnessD1_apply_basis3_e6
      rw [hact] at he6
      norm_num at he6
    have hj_nz : j₁.1 ≠ 0 := by
      intro h0
      have hα := congrArg H3Octonion.α₁ h0
      change (1 : ℝ) = 0 at hα
      norm_num at hα
    have ho_pos : 0 < CompactOctonion.bilin (compactG2Act compactG2WitnessD1 o₃).1
        (compactG2Act compactG2WitnessD1 o₃).1 :=
      f7_t2_bilin_pos_def_no_isotropic _ ho_nz
    have hj_pos : 0 < H3Octonion.traceBilin j₁.1 j₁.1 :=
      lt_of_le_of_ne (H3Octonion.traceBilin_self_nonneg j₁.1)
        (fun h => hj_nz ((H3Octonion.traceBilin_self_eq_zero_iff j₁.1).mp h.symm))
    have hprod : 0 < compactOctonionDatum.bilin₀ (compactG2Act compactG2WitnessD1 o₃)
        (compactG2Act compactG2WitnessD1 o₃) * h3OctonionJordanDatum.traceBilin₀ j₁ j₁ :=
      mul_pos ho_pos hj_pos
    linarith
  · rintro ⟨F', hF'⟩
    have hbr_mix :
        (⁅msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum F0,
          msEmbedTensor compactOctonionDatum h3OctonionJordanDatum o₃ j₁⁆ : CompactE8Lie).mixed =
        o₃ ⊗ₜ[ℝ] (h3OctonionJordanDatum.act F0 j₁) := by
      change (magicSquareBracketLM compactOctonionDatum h3OctonionJordanDatum
        (msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum F0)
        (msEmbedMixed compactOctonionDatum h3OctonionJordanDatum (o₃ ⊗ₜ[ℝ] j₁))).mixed = _
      simp [magicSquareBracketLM, msEmbedF4LM, msEmbedMixed]
    have hm := congrArg (fun Y : CompactE8Lie =>
      magicMixedBilin compactOctonionDatum h3OctonionJordanDatum
        (o₃ ⊗ₜ[ℝ] (h3OctonionJordanDatum.act F0 j₁)) Y.mixed) hF'
    have hF'm : (msEmbedF4LM compactOctonionDatum h3OctonionJordanDatum F').mixed = 0 := rfl
    rw [hbr_mix, hF'm, map_zero, magicMixedBilin_tmul] at hm
    have ho_pos : 0 < CompactOctonion.bilin o₃.1 o₃.1 := by
      change 0 < CompactOctonion.bilin (CompactOctonion.basisVec 3) (CompactOctonion.basisVec 3)
      rw [CompactOctonion.bilin_basis 3 3]
      norm_num
    have hFj_nz : (h3OctonionJordanDatum.act F0 j₁).1 ≠ 0 := by
      intro h0
      have ha : (h3OctonionJordanDatum.act F0 j₁).1.a.e0 = -1 / 4 := by
        change (H3Octonion.diagCartan (1 : ℝ) 0 0 *
            (H3Octonion.embedJ12 (1 : CompactOctonion ℝ) * H3Octonion.diagCartan (1 : ℝ) 0 (-1)) -
          H3Octonion.embedJ12 (1 : CompactOctonion ℝ) *
            (H3Octonion.diagCartan (1 : ℝ) 0 0 * H3Octonion.diagCartan (1 : ℝ) 0 (-1))).a.e0 =
          -1 / 4
        have hm1 : H3Octonion.diagCartan (1 : ℝ) 0 0 * H3Octonion.diagCartan (1 : ℝ) 0 (-1) =
            H3Octonion.diagCartan (1 : ℝ) 0 0 := by
          rw [H3Octonion.mul_trace_formula]
          have hlt : H3Octonion.linearTrace (H3Octonion.diagCartan (1 : ℝ) 0 0) = 1 := by
            simp [H3Octonion.linearTrace, H3Octonion.diagCartan]
          have hcr : H3Octonion.crossProduct (H3Octonion.diagCartan (1 : ℝ) 0 0)
              (H3Octonion.diagCartan (1 : ℝ) 0 (-1)) = ⟨0, -1, 0, 0, 0, 0⟩ := by
            apply H3Octonion.ext_h3 <;> simp [H3Octonion.crossProduct, H3Octonion.diagCartan]
          rw [hlt, hcr]
          apply H3Octonion.ext_h3 <;>
            simp [H3Octonion.diagCartan, H3Octonion.linearTrace]
          norm_num
        have hm2 : H3Octonion.embedJ12 (1 : CompactOctonion ℝ) *
              H3Octonion.diagCartan (1 : ℝ) 0 (-1) =
            (1 / 2 : ℝ) • H3Octonion.embedJ12 (1 : CompactOctonion ℝ) := by
          rw [_root_.mul_comm, H3Octonion.mul_trace_formula]
          have hlt : H3Octonion.linearTrace (H3Octonion.diagCartan (1 : ℝ) 0 (-1)) = 0 := by
            simp [H3Octonion.linearTrace, H3Octonion.diagCartan]
          have hcr : H3Octonion.crossProduct (H3Octonion.diagCartan (1 : ℝ) 0 (-1))
              (H3Octonion.embedJ12 (1 : CompactOctonion ℝ)) =
              H3Octonion.embedJ12 (1 : CompactOctonion ℝ) := by
            apply H3Octonion.ext_h3 <;> (try apply CompactOctonion.ext) <;>
              simp [H3Octonion.crossProduct, H3Octonion.diagCartan, H3Octonion.embedJ12]
          rw [hlt, hcr]
          apply H3Octonion.ext_h3 <;> (try apply CompactOctonion.ext) <;>
            simp [H3Octonion.diagCartan, H3Octonion.linearTrace, H3Octonion.embedJ12]
        have hm3 : H3Octonion.diagCartan (1 : ℝ) 0 0 *
              H3Octonion.embedJ12 (1 : CompactOctonion ℝ) =
            (1 / 2 : ℝ) • H3Octonion.embedJ12 (1 : CompactOctonion ℝ) := by
          rw [H3Octonion.mul_trace_formula]
          have hlt : H3Octonion.linearTrace (H3Octonion.diagCartan (1 : ℝ) 0 0) = 1 := by
            simp [H3Octonion.linearTrace, H3Octonion.diagCartan]
          have hcr : H3Octonion.crossProduct (H3Octonion.diagCartan (1 : ℝ) 0 0)
              (H3Octonion.embedJ12 (1 : CompactOctonion ℝ)) = 0 := by
            apply H3Octonion.ext_h3 <;> (try apply CompactOctonion.ext) <;>
              simp [H3Octonion.crossProduct, H3Octonion.diagCartan, H3Octonion.embedJ12]
          rw [hlt, hcr]
          apply H3Octonion.ext_h3 <;> (try apply CompactOctonion.ext) <;>
            simp [H3Octonion.diagCartan, H3Octonion.linearTrace, H3Octonion.embedJ12]
        rw [hm1, hm2, mul_smul_comm, hm3,
          _root_.mul_comm (H3Octonion.embedJ12 (1 : CompactOctonion ℝ)), hm3]
        simp [H3Octonion.embedJ12]
        rw [sub_eq_add_neg]
        simp
        norm_num
      have he0 := congrArg (fun w : H3Octonion ℝ => w.a.e0) h0
      rw [ha] at he0
      norm_num at he0
    have hj_pos : 0 < H3Octonion.traceBilin (h3OctonionJordanDatum.act F0 j₁).1
        (h3OctonionJordanDatum.act F0 j₁).1 :=
      lt_of_le_of_ne (H3Octonion.traceBilin_self_nonneg _)
        (fun h => hFj_nz ((H3Octonion.traceBilin_self_eq_zero_iff _).mp h.symm))
    have hprod : 0 < compactOctonionDatum.bilin₀ o₃ o₃ *
        h3OctonionJordanDatum.traceBilin₀ (h3OctonionJordanDatum.act F0 j₁)
          (h3OctonionJordanDatum.act F0 j₁) :=
      mul_pos ho_pos hj_pos
    linarith

theorem f8_t2_sector_invBilin_orthogonal
    (D : CompactOctonionDerivations) (F : H3OctonionF4Derivations)
    (m : CompactOctonionTraceZero ⊗[ℝ] h3OctonionTraceZero) :
    magicInvBilin compactOctonionDatum h3OctonionJordanDatum
      (msEmbedG2LM _ _ D) (msEmbedMixed _ _ m) = 0 ∧
    magicInvBilin compactOctonionDatum h3OctonionJordanDatum
      (msEmbedG2LM _ _ D) (msEmbedF4LM _ _ F) = 0 ∧
    magicInvBilin compactOctonionDatum h3OctonionJordanDatum
      (msEmbedMixed _ _ m) (msEmbedF4LM _ _ F) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [magicInvBilin_apply, msEmbedG2LM, msEmbedMixed, msEmbedF4LM]

/-! ### Feature 9: Quaternionic `𝔈₈(-24)` Magic Square (`QuaternionicE8Lie`) -/

theorem f9_t1_finrank_248 : Module.finrank ℝ QuaternionicE8Lie = 248 :=
  finrank_quaternionicE8Lie

theorem f9_t1_jacobi_and_lie_smul (r : ℝ) (X Y Z : QuaternionicE8Lie) :
    ⁅X, ⁅Y, Z⁆⁆ = ⁅⁅X, Y⁆, Z⁆ + ⁅Y, ⁅X, Z⁆⁆ ∧
    ⁅X, r • Y⁆ = r • ⁅X, Y⁆ :=
  ⟨leibniz_lie X Y Z, lie_smul r X Y⟩

theorem f9_t1_isSimple : LieAlgebra.IsSimple ℝ QuaternionicE8Lie :=
  quaternionicE8Lie_isSimple

theorem f9_t1_isKilling_and_center_bot :
    LieAlgebra.IsKilling ℝ QuaternionicE8Lie ∧
    LieAlgebra.center ℝ QuaternionicE8Lie = ⊥ :=
  ⟨quaternionicE8Lie_isKilling, LieAlgebra.center_eq_bot ℝ QuaternionicE8Lie⟩

theorem f9_t1_g2_f4_embed_and_commute
    (D₁ D₂ : CompactOctonionDerivations) (F₁ F₂ : F4DerivationCarrier) :
    msEmbedG2LM compactOctonionDatum h3ZornJordanDatum ⁅D₁, D₂⁆ =
      ⁅msEmbedG2LM compactOctonionDatum h3ZornJordanDatum D₁,
        msEmbedG2LM compactOctonionDatum h3ZornJordanDatum D₂⁆ ∧
    msEmbedF4LM compactOctonionDatum h3ZornJordanDatum ⁅F₁, F₂⁆ =
      ⁅msEmbedF4LM compactOctonionDatum h3ZornJordanDatum F₁,
        msEmbedF4LM compactOctonionDatum h3ZornJordanDatum F₂⁆ ∧
    ⁅msEmbedG2LM compactOctonionDatum h3ZornJordanDatum D₁,
      msEmbedF4LM compactOctonionDatum h3ZornJordanDatum F₁⁆ = 0 :=
  ⟨msEmbedG2LM_lie _ _ D₁ D₂, msEmbedF4LM_lie _ _ F₁ F₂,
    msEmbedG2LM_bracket_msEmbedF4LM _ _ D₁ F₁⟩

theorem f9_t2_zero_and_antisymm (X Y : QuaternionicE8Lie) :
    ⁅X, X⁆ = 0 ∧ ⁅Y, X⁆ = -⁅X, Y⁆ ∧ ⁅(0 : QuaternionicE8Lie), X⁆ = 0 :=
  ⟨lie_self X, (lie_skew Y X).symm, zero_lie X⟩

theorem f9_t2_h3zorn_nilpotent_witness :
    ∃ w : H3Zorn ℝ, w ≠ 0 ∧ w * w = 0 := by
  refine ⟨h3ZornBasis 3, h3ZornBasis.ne_zero 3, ?_⟩
  rw [show (3 : Fin 27) = ⟨3 + (0 : Fin 8).val, by omega⟩ from rfl, h3ZornBasis_12 0,
    embedJ12_mul_embedJ12, zornBilin_zorn_basis 0 0]
  have hz : zornBilinInt 0 0 = 0 := rfl
  rw [hz]
  simp

theorem f9_t2_cartan_k_p_disjoint_and_finrank :
    (quaternionicE8CartanCompact ⊓ quaternionicE8CartanNoncompact) = ⊥ ∧
    Module.finrank ℝ quaternionicE8CartanCompact = 136 ∧
    Module.finrank ℝ quaternionicE8CartanNoncompact = 112 := by
  refine ⟨?_, finrank_quaternionicE8CartanCompact, finrank_quaternionicE8CartanNoncompact⟩
  rw [eq_bot_iff]
  intro X ⟨hXk, hXp⟩
  have hXk' : quaternionicE8CartanInvolution X = X := by
    change quaternionicE8CartanInvolution X - X = 0 at hXk
    exact sub_eq_zero.mp hXk
  have hXp' : quaternionicE8CartanInvolution X = -X := by
    change quaternionicE8CartanInvolution X + X = 0 at hXp
    exact add_eq_zero_iff_eq_neg.mp hXp
  rw [hXk'] at hXp'
  have h2 : (2 : ℝ) • X = 0 := by
    calc
      (2 : ℝ) • X = X + X := two_smul ℝ X
      _ = X - (-X) := by rw [sub_neg_eq_add]
      _ = X - X := by rw [← hXp']
      _ = 0 := sub_self X
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem f9_t2_killingForm_k_neg_and_p_pos :
    (∃ X ∈ quaternionicE8CartanCompact, X ≠ 0 ∧ killingForm ℝ QuaternionicE8Lie X X < 0) ∧
    (∃ Y ∈ quaternionicE8CartanNoncompact, Y ≠ 0 ∧ 0 < killingForm ℝ QuaternionicE8Lie Y Y) := by
  have hk_ne : (quaternionicE8CartanCompact : Submodule ℝ QuaternionicE8Lie) ≠ ⊥ := by
    intro h0
    have hf := finrank_quaternionicE8CartanCompact
    rw [h0, finrank_bot] at hf
    norm_num at hf
  have hp_ne : quaternionicE8CartanNoncompact ≠ ⊥ := by
    intro h0
    have hf := finrank_quaternionicE8CartanNoncompact
    rw [h0, finrank_bot] at hf
    norm_num at hf
  obtain ⟨X, hXk, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk_ne
  obtain ⟨Y, hYp, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp_ne
  refine ⟨⟨X, hXk, hX0, lt_of_le_of_ne (quaternionicE8_killingForm_k_nonpos hXk)
      (fun h => hX0 ((quaternionicE8_killingForm_k_eq_zero_iff hXk).mp h))⟩,
    ⟨Y, hYp, hY0, lt_of_le_of_ne (quaternionicE8_killingForm_p_nonneg hYp)
      (fun h => hY0 ((quaternionicE8_killingForm_p_eq_zero_iff hYp).mp h.symm))⟩⟩

theorem f9_t2_coexistence_neg_g2_and_pos_f4_trace_sq :
    (∃ D : CompactOctonionDerivations,
      LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) < 0) ∧
    LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) = 3 / 2 :=
  ⟨⟨compactG2WitnessD1, lt_of_le_of_ne (compactG2_trace_sq_nonpos compactG2WitnessD1)
      (mt (compactG2_trace_sq_eq_zero_iff compactG2WitnessD1).mp compactG2WitnessD1_ne_zero)⟩,
    splitF4TracePosWitness_trace_sq⟩

/-! ### Feature 10: `E₈` Killing & Cartan signature separation (`-248` vs `-24` vs `+8`) -/

theorem f10_t1_compactE8_signature_neg_248 :
    (Module.finrank ℝ compactE8CartanNoncompact : ℤ) - Module.finrank ℝ compactE8CartanCompact = -248 ∧
    ∀ X : CompactE8Lie, killingForm ℝ CompactE8Lie X X ≤ 0 :=
  ⟨compactE8_signature_eq_neg_248, compactE8_killingForm_nonpos⟩

theorem f10_t1_quaternionicE8_cartan_involution_and_sig (X : QuaternionicE8Lie) :
    quaternionicE8CartanInvolution (quaternionicE8CartanInvolution X) = X ∧
    Module.finrank ℝ quaternionicE8CartanCompact = 136 ∧
    Module.finrank ℝ quaternionicE8CartanNoncompact = 112 ∧
    (Module.finrank ℝ quaternionicE8CartanNoncompact : ℤ) -
      Module.finrank ℝ quaternionicE8CartanCompact = -24 :=
  ⟨quaternionicE8CartanInvolution_involutive X, finrank_quaternionicE8CartanCompact,
    finrank_quaternionicE8CartanNoncompact, quaternionicE8_signature_eq_neg_24⟩

theorem f10_t1_splitE8_cartan_involution_and_sig (X : SplitE8Lie) :
    splitE8CartanInvolution (splitE8CartanInvolution X) = X ∧
    Module.finrank ℝ splitE8CartanCompact = 120 ∧
    Module.finrank ℝ splitE8CartanNoncompact = 128 ∧
    (Module.finrank ℝ splitE8CartanNoncompact : ℤ) -
      Module.finrank ℝ splitE8CartanCompact = 8 :=
  ⟨splitE8CartanInvolution_involutive X, finrank_splitE8CartanCompact,
    finrank_splitE8CartanNoncompact, splitE8_signature_eq_pos_8⟩

theorem f10_t1_killing_definiteness_quaternionic_and_split :
    (∀ X ∈ quaternionicE8CartanCompact, killingForm ℝ QuaternionicE8Lie X X = 0 ↔ X = 0) ∧
    (∀ Y ∈ quaternionicE8CartanNoncompact, killingForm ℝ QuaternionicE8Lie Y Y = 0 ↔ Y = 0) ∧
    (∀ X ∈ splitE8CartanCompact, killingForm ℝ SplitE8Lie X X = 0 ↔ X = 0) ∧
    (∀ Y ∈ splitE8CartanNoncompact, killingForm ℝ SplitE8Lie Y Y = 0 ↔ Y = 0) :=
  ⟨fun _ h => quaternionicE8_killingForm_k_eq_zero_iff h,
    fun _ h => quaternionicE8_killingForm_p_eq_zero_iff h,
    fun _ h => splitE8_killingForm_k_eq_zero_iff h,
    fun _ h => splitE8_killingForm_p_eq_zero_iff h⟩

theorem f10_t1_pairwise_non_isomorphic :
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ QuaternionicE8Lie) ∧
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ SplitE8Lie) ∧
    IsEmpty (QuaternionicE8Lie ≃ₗ⁅ℝ⁆ SplitE8Lie) :=
  ⟨compactE8_not_lieEquiv_quaternionicE8, compactE8_not_lieEquiv_splitE8,
    quaternionicE8_not_lieEquiv_splitE8⟩

theorem f10_t2_compactE8_trivial_involution_boundary :
    compactE8CartanCompact = ⊤ ∧
    compactE8CartanNoncompact = ⊥ ∧
    Module.finrank ℝ compactE8CartanNoncompact = 0 :=
  ⟨compactE8CartanCompact_eq_top, compactE8CartanNoncompact_eq_bot,
    finrank_compactE8CartanNoncompact⟩

theorem f10_t2_signatures_pairwise_distinct :
    (-248 : ℤ) ≠ -24 ∧ (-24 : ℤ) ≠ 8 ∧ (-248 : ℤ) ≠ 8 :=
  e8_real_form_signatures_pairwise_distinct

theorem f10_t2_killing_k_p_ortho_both :
    (∀ X ∈ quaternionicE8CartanCompact, ∀ Y ∈ quaternionicE8CartanNoncompact,
      killingForm ℝ QuaternionicE8Lie X Y = 0) ∧
    (∀ X ∈ splitE8CartanCompact, ∀ Y ∈ splitE8CartanNoncompact,
      killingForm ℝ SplitE8Lie X Y = 0) :=
  ⟨fun _ hX _ hY => quaternionicE8_killingForm_k_p_ortho hX hY,
    fun _ hX _ hY => splitE8_killingForm_k_p_ortho hX hY⟩

theorem f10_t2_invBilin_symm_lieInvariant_zero
    (X Y : CompactE8Lie) (Z₁ X₁ Y₁ : QuaternionicE8Lie) :
    magicInvBilin compactOctonionDatum h3OctonionJordanDatum X Y =
      magicInvBilin compactOctonionDatum h3OctonionJordanDatum Y X ∧
    magicInvBilin compactOctonionDatum h3OctonionJordanDatum 0 Y = 0 ∧
    magicInvBilin compactOctonionDatum h3ZornJordanDatum ⁅Z₁, X₁⁆ Y₁ +
      magicInvBilin compactOctonionDatum h3ZornJordanDatum X₁ ⁅Z₁, Y₁⁆ = 0 :=
  ⟨magicInvBilin_symm X Y, by simp, magicInvBilin_lieInvariant Z₁ X₁ Y₁⟩

theorem f10_t2_reverse_non_isomorphic_all_six_pairs :
    IsEmpty (QuaternionicE8Lie ≃ₗ⁅ℝ⁆ CompactE8Lie) ∧
    IsEmpty (SplitE8Lie ≃ₗ⁅ℝ⁆ CompactE8Lie) ∧
    IsEmpty (SplitE8Lie ≃ₗ⁅ℝ⁆ QuaternionicE8Lie) :=
  ⟨⟨fun e => compactE8_not_lieEquiv_quaternionicE8.false e.symm⟩,
    ⟨fun e => compactE8_not_lieEquiv_splitE8.false e.symm⟩,
    ⟨fun e => quaternionicE8_not_lieEquiv_splitE8.false e.symm⟩⟩

/-! =========================================================================
    TIER 1 & TIER 2: R4 — `InfoGeometry.Algebra.H3ZornFreudenthalTKK5E8` (F11–F13)
    ========================================================================= -/

/-! ### Feature 11: `56D` `H3ZornTKKLie` rep `repE7` -/

theorem f11_t1_repE7_map_lie (X Y : H3ZornTKKLie) :
    repE7 ⁅X, Y⁆ = ⁅repE7 X, repE7 Y⁆ :=
  repE7.map_lie X Y

theorem f11_t1_symplecticForm_skew (X : H3ZornTKKLie) (Q₁ Q₂ : Charge) :
    symplecticForm (repE7 X Q₁) Q₂ + symplecticForm Q₁ (repE7 X Q₂) = 0 :=
  repE7_symplecticForm_skew X Q₁ Q₂

theorem f11_t1_quarticInvariant_deriv_zero (X : H3ZornTKKLie) (Q : Charge) :
    HasDerivAt (fun t : ℝ => quarticInvariant (Q + t • repE7 X Q)) 0 0 :=
  repE7_preserves_quarticInvariant_deriv X Q

theorem f11_t1_repE7_faithful :
    LinearMap.ker repE7.toLinearMap = ⊥ ∧ repE7 ≠ 0 := by
  have hnz : repE7 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun f : H3ZornTKKLie →ₗ⁅ℝ⁆ Module.End ℝ Charge =>
      (f (negInj (1 : H3Zorn ℝ)) (scalarCharge 0 1)).x) h0
    rw [zero_apply, LinearMap.zero_apply] at h1
    change (repE7 (negInj (1 : H3Zorn ℝ)) (scalarCharge 0 1)).x = 0 at h1
    have hn : (negInj (1 : H3Zorn ℝ)).neg = 1 := rfl
    have hz : (negInj (1 : H3Zorn ℝ)).zero = 0 := rfl
    have hp : (negInj (1 : H3Zorn ℝ)).pos = 0 := rfl
    have hqx : (scalarCharge 0 1).x = 0 := rfl
    have hqy : (scalarCharge 0 1).y = 0 := rfl
    have hqb : (scalarCharge 0 1).beta = 1 := rfl
    have hstr0 : strTrace (negInj (1 : H3Zorn ℝ)).zero = 0 := by
      rw [hz]; exact map_zero strTrace
    have h00 : (negInj (1 : H3Zorn ℝ)).zero.1 (0 : H3Zorn ℝ) = 0 := rfl
    have hcp0 : H3Zorn.crossProduct (0 : H3Zorn ℝ) 0 = 0 := by
      rw [H3Zorn.crossProduct, add_zero, sub_self, adjointQuad_zero, sub_zero]
    rw [repE7_x, hn, hp, hqx, hqy, hqb, hcp0, hstr0, h00, one_smul,
      mul_zero, zero_smul, sub_zero, sub_zero, add_zero] at h1
    have h1' : (1 : H3Zorn ℝ) = 0 := (smul_eq_zero.mp h1).resolve_left (by norm_num)
    have hα := congrArg H3Zorn.α₁ h1'
    change (1 : ℝ) = 0 at hα
    norm_num at hα
  refine ⟨?_, hnz⟩
  have hker : repE7.ker = ⊥ ∨ repE7.ker = ⊤ :=
    LieAlgebra.IsSimple.eq_bot_or_eq_top repE7.ker
  rcases hker with hbot | htop
  · exact congrArg LieSubmodule.toSubmodule hbot
  · exfalso
    apply hnz
    apply LieHom.ext
    intro X
    have hmem : X ∈ repE7.ker := by rw [htop]; trivial
    exact hmem

theorem f11_t1_e6_levi_compatibility (T : h3zornCubicStabilizer) (Q : Charge) :
    repE7 (h3zornCubicStabilizerToTKK T) Q = ⟨0, 0, T.1 Q.x, -h3zornTraceAdjoint T.1 Q.y⟩ := by
  have htr : strTrace (h3zornCubicStabilizerToTKK T).zero = 0 := by
    rw [strTrace_apply]
    change H3Zorn.linearTrace (T.1 1) = 0
    have h111 := T.2 1 1 1
    have h3 : h3zornNormTrilin (T.1 1) 1 1 = 0 := by
      have hs : h3zornNormTrilin 1 (T.1 1) 1 = h3zornNormTrilin (T.1 1) 1 1 :=
        h3zornCubicJordanDatum.normTrilin_swap₁₂ 1 (T.1 1) 1
      have hs' : h3zornNormTrilin 1 1 (T.1 1) = h3zornNormTrilin (T.1 1) 1 1 := by
        change h3zornCubicJordanDatum.normTrilin 1 1 (T.1 1) =
          h3zornCubicJordanDatum.normTrilin (T.1 1) 1 1
        rw [h3zornCubicJordanDatum.normTrilin_swap₂₃, h3zornCubicJordanDatum.normTrilin_swap₁₂]
      linarith
    rw [← h3zornNormTrilin_one_one (T.1 1), h3, mul_zero]
  have hneg : (h3zornCubicStabilizerToTKK T).neg = 0 := rfl
  have hpos : (h3zornCubicStabilizerToTKK T).pos = 0 := rfl
  have hzero : (h3zornCubicStabilizerToTKK T).zero.1 = T.1 := rfl
  have hcp0 (A : H3Zorn ℝ) : H3Zorn.crossProduct 0 A = 0 := by
    rw [H3Zorn.crossProduct, zero_add, adjointQuad_zero, sub_zero, sub_self]
  apply InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge.ext
  · rw [repE7_alpha, htr, hneg, H3Zorn.traceBilin_zero_left]
    norm_num
  · rw [repE7_beta, htr, hpos, H3Zorn.traceBilin_zero_left]
    norm_num
  · rw [repE7_x, htr, hneg, hpos, hzero, hcp0, mul_zero, zero_smul, sub_zero,
      smul_zero, smul_zero, sub_zero, zero_add]
  · rw [repE7_y, htr, hneg, hpos, hzero, hcp0, mul_zero, zero_smul, add_zero,
      neg_zero, smul_zero, zero_add, smul_zero, add_zero]

theorem f11_t2_repE7_zero_arg : repE7 0 = 0 :=
  map_zero repE7

theorem f11_t2_repE7_apply_zero_charge (X : H3ZornTKKLie) :
    repE7 X 0 = 0 :=
  map_zero (repE7 X)

theorem f11_t2_charge_orbits_regular_boundary_scalar :
    Regular (electricCharge 1 (1 : H3Zorn ℝ)) ∧
    Boundary (scalarCharge 1 0) ∧
    quarticInvariant (scalarCharge 1 0) = 0 := by
  have hq : quarticInvariant (scalarCharge 1 0) = 0 := by
    rw [quarticInvariant_scalarCharge]
    ring
  have hne : scalarCharge 1 0 ≠ 0 := by
    intro h0
    have ha := congrArg InfoGeometry.Exceptional.Freudenthal.FreudenthalCharge.alpha h0
    change (1 : ℝ) = 0 at ha
    norm_num at ha
  refine ⟨?_, ⟨hq, hne⟩, hq⟩
  change quarticInvariant (electricCharge 1 (1 : H3Zorn ℝ)) ≠ 0
  rw [unit_electric_quartic]
  norm_num

theorem f11_t2_symplectic_alternating_vs_nondeg (Q : Charge) :
    symplecticForm Q Q = 0 ∧
    symplecticForm (scalarCharge 1 0) (scalarCharge 0 1) = 1 := by
  refine ⟨symplecticForm_self Q, ?_⟩
  rw [symplecticForm_expanded]
  simp [scalarCharge]

theorem f11_t2_repE7_noncomm_witness :
    ⁅repE7 (negInj (1 : H3Zorn ℝ)), repE7 (posInj (1 : H3Zorn ℝ))⁆ ≠ 0 := by
  intro h0
  rw [← repE7.map_lie] at h0
  have ha := congrArg (fun E : Module.End ℝ Charge => (E (scalarCharge 1 0)).alpha) h0
  have hbr : ⁅negInj (1 : H3Zorn ℝ), posInj (1 : H3Zorn ℝ)⁆ = h3zornTKKGradeOp :=
    negInj_one_bracket_posInj_one_eq_gradeOp
  rw [hbr, repE7_alpha] at ha
  have htr : strTrace h3zornTKKGradeOp.zero = 3 := by
    rw [strTrace_apply]
    change H3Zorn.linearTrace (h3zornStrOne.1 1) = 3
    rw [h3zornStrOne_apply]
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  have hneg : h3zornTKKGradeOp.neg = 0 := rfl
  rw [hneg, htr, H3Zorn.traceBilin_zero_left] at ha
  simp [scalarCharge] at ha

/-! ### Feature 12: `248D` 5-graded TKK `𝔈₈` carrier & bracket -/

theorem f12_t1_finrank_248 :
    Module.finrank ℝ FreudenthalTKK5E8 = 248 :=
  finrank_freudenthalTKK5E8

theorem f12_t1_graded_finranks :
    Module.finrank ℝ (gGrade (-2)) = 1 ∧
    Module.finrank ℝ (gGrade (-1)) = 56 ∧
    Module.finrank ℝ (gGrade 0) = 134 ∧
    Module.finrank ℝ (gGrade 1) = 56 ∧
    Module.finrank ℝ (gGrade 2) = 1 :=
  ⟨finrank_gGrade_neg_two, finrank_gGrade_neg_one, finrank_gGrade_zero,
    finrank_gGrade_pos_one, finrank_gGrade_pos_two⟩

theorem f12_t1_jacobi_and_lie_smul (r : ℝ) (U V W : FreudenthalTKK5E8) :
    ⁅U, ⁅V, W⁆⁆ = ⁅⁅U, V⁆, W⁆ + ⁅V, ⁅U, W⁆⁆ ∧
    ⁅U, r • V⁆ = r • ⁅U, V⁆ :=
  ⟨leibniz_lie U V W, lie_smul r U V⟩

theorem f12_t1_gGrade_bracket_closure {i j : ℤ} {U V : FreudenthalTKK5E8}
    (hU : U ∈ gGrade i) (hV : V ∈ gGrade j) :
    ⁅U, V⁆ ∈ gGrade (i + j) :=
  gGrade_bracket_mem hU hV

theorem f12_t1_heisenberg_brackets (Q₁ Q₂ : Charge) :
    ⁅injPlus1 Q₁, injMinus1 Q₂⁆ =
      injZeroE7 (K Q₁ Q₂) + injZeroCenter (-(1 / 2 : ℝ) * symplecticForm Q₁ Q₂) ∧
    ⁅injPlus1 Q₁, injPlus1 Q₂⁆ = injPlus2 (symplecticForm Q₁ Q₂) := by
  refine ⟨?_, ?_⟩
  · change bracket5LM (injPlus1 Q₁) (injMinus1 Q₂) = _
    apply FreudenthalTKK5E8.ext
    · simp [bracket5LM_gMinus2, injPlus1, injMinus1, injZeroE7, injZeroCenter]
    · simp [bracket5LM_gMinus1, injPlus1, injMinus1, injZeroE7, injZeroCenter]
    · simp [bracket5LM_gZeroE7, injPlus1, injMinus1, injZeroE7, injZeroCenter]
    · simp [bracket5LM_gZeroCenter, injPlus1, injMinus1, injZeroE7, injZeroCenter,
        symplecticForm_self]
    · simp [bracket5LM_gPlus1, injPlus1, injMinus1, injZeroE7, injZeroCenter]
    · simp [bracket5LM_gPlus2, injPlus1, injMinus1, injZeroE7, injZeroCenter]
  · change bracket5LM (injPlus1 Q₁) (injPlus1 Q₂) = _
    apply FreudenthalTKK5E8.ext
    · simp [bracket5LM_gMinus2, injPlus1, injPlus2]
    · simp [bracket5LM_gMinus1, injPlus1, injPlus2]
    · simp [bracket5LM_gZeroE7, injPlus1, injPlus2]
    · simp [bracket5LM_gZeroCenter, injPlus1, injPlus2]
    · simp [bracket5LM_gPlus1, injPlus1, injPlus2]
    · simp [bracket5LM_gPlus2, injPlus1, injPlus2]

theorem f12_t2_zero_components :
    (0 : FreudenthalTKK5E8).gMinus2 = 0 ∧
    (0 : FreudenthalTKK5E8).gMinus1 = 0 ∧
    (0 : FreudenthalTKK5E8).gZeroE7 = 0 ∧
    (0 : FreudenthalTKK5E8).gZeroCenter = 0 ∧
    (0 : FreudenthalTKK5E8).gPlus1 = 0 ∧
    (0 : FreudenthalTKK5E8).gPlus2 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem f12_t2_out_of_range_grades_bot_and_vanish (Q : Charge) :
    gGrade 3 = ⊥ ∧
    gGrade (-3) = ⊥ ∧
    ⁅ePlus2, ePlus2⁆ = 0 ∧
    ⁅eMinus2, eMinus2⁆ = 0 ∧
    ⁅injPlus1 Q, ePlus2⁆ = 0 ∧
    ⁅injMinus1 Q, eMinus2⁆ = 0 := by
  refine ⟨gGrade_eq_bot_of_abs_gt_two 3 (by decide),
    gGrade_eq_bot_of_abs_gt_two (-3) (by decide),
    lie_self ePlus2, lie_self eMinus2, ?_, ?_⟩
  · have h1 : injPlus1 Q ∈ gGrade 1 := (mem_gGrade_pos_one_iff _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩
    have h2 : ePlus2 ∈ gGrade 2 := (mem_gGrade_pos_two_iff _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hb := gGrade_bracket_mem h1 h2
    rw [show (1 : ℤ) + 2 = 3 by norm_num, gGrade_eq_bot_of_abs_gt_two 3 (by decide)] at hb
    simpa using hb
  · have h1 : injMinus1 Q ∈ gGrade (-1) := (mem_gGrade_neg_one_iff _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩
    have h2 : eMinus2 ∈ gGrade (-2) := (mem_gGrade_neg_two_iff _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hb := gGrade_bracket_mem h1 h2
    rw [show (-1 : ℤ) + (-2) = -3 by norm_num, gGrade_eq_bot_of_abs_gt_two (-3) (by decide)] at hb
    simpa using hb

theorem f12_t2_gGrade_zero_split_and_e2_bracket (X : H3ZornTKKLie) :
    ⁅zeroE7Hom X, gradeCenterZ⁆ = 0 ∧
    ⁅ePlus2, eMinus2⁆ = gradeCenterZ ∧
    ⁅ePlus2, eMinus2⁆.gZeroE7 = 0 := by
  refine ⟨zeroE7Hom_comm_gradeCenterZ X, freudenthalTKK5E8_sl2Triple.lie_e_f, ?_⟩
  rw [freudenthalTKK5E8_sl2Triple.lie_e_f]
  rfl

theorem f12_t2_heisenberg_nonzero_K_projection :
    ⁅injPlus1 (scalarCharge 1 0), injMinus1 (scalarCharge 0 1)⁆.gZeroE7 =
      K (scalarCharge 1 0) (scalarCharge 0 1) ∧
    K (scalarCharge 1 0) (scalarCharge 0 1) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · change (bracket5LM (injPlus1 (scalarCharge 1 0)) (injMinus1 (scalarCharge 0 1))).gZeroE7 = _
    rw [bracket5LM_gZeroE7]
    simp [injPlus1, injMinus1]
  · intro h0
    have hB := B_E7_K_eq (scalarCharge 1 0) (scalarCharge 0 1) h3zornTKKGradeOp
    rw [h0, map_zero, LinearMap.zero_apply] at hB
    have hrep : (repE7 h3zornTKKGradeOp (scalarCharge 1 0)).alpha = 3 / 2 := by
      rw [repE7_alpha]
      have htr : strTrace h3zornTKKGradeOp.zero = 3 := by
        rw [strTrace_apply]
        change H3Zorn.linearTrace (h3zornStrOne.1 1) = 3
        rw [h3zornStrOne_apply]
        change (1 : ℝ) + 1 + 1 = 3
        norm_num
      have hneg : h3zornTKKGradeOp.neg = 0 := rfl
      rw [hneg, htr, H3Zorn.traceBilin_zero_left]
      simp [scalarCharge]
      norm_num
    have h0a : (scalarCharge 0 1).alpha = 0 := rfl
    have h0b : (scalarCharge 0 1).beta = 1 := rfl
    have h0x : (scalarCharge 0 1).x = 0 := rfl
    have h0y : (scalarCharge 0 1).y = 0 := rfl
    rw [symplecticForm_expanded, hrep, h0a, h0b, h0x, h0y,
      H3Zorn.traceBilin_zero_right, H3Zorn.traceBilin_zero_right] at hB
    norm_num at hB

theorem f12_t2_boundary_charges_jacobi_and_grade :
    Boundary (scalarCharge 1 0) ∧
    ⁅injPlus1 (scalarCharge 1 0), injPlus1 (scalarCharge 0 1)⁆ = ePlus2 ∧
    ⁅injPlus1 (scalarCharge 1 0), ⁅injMinus1 (scalarCharge 0 1), ePlus2⁆⁆ =
      ⁅⁅injPlus1 (scalarCharge 1 0), injMinus1 (scalarCharge 0 1)⁆, ePlus2⁆ +
        ⁅injMinus1 (scalarCharge 0 1), ⁅injPlus1 (scalarCharge 1 0), ePlus2⁆⁆ := by
  refine ⟨f11_t2_charge_orbits_regular_boundary_scalar.2.1, ?_, leibniz_lie _ _ _⟩
  rw [(f12_t1_heisenberg_brackets (scalarCharge 1 0) (scalarCharge 0 1)).2,
    (f11_t2_symplectic_alternating_vs_nondeg (scalarCharge 0 1)).2]
  rfl

/-! ### Feature 13: 5-graded `E₈` simplicity, `IsKilling`, Cartan, `sl₂ ⊕ E₇` & Split comparison -/

theorem f13_t1_isSimple : LieAlgebra.IsSimple ℝ FreudenthalTKK5E8 :=
  freudenthalTKK5E8_isSimple

theorem f13_t1_isKilling_and_center_bot :
    LieAlgebra.IsKilling ℝ FreudenthalTKK5E8 ∧
    LieAlgebra.center ℝ FreudenthalTKK5E8 = ⊥ :=
  ⟨freudenthalTKK5E8_isKilling, LieAlgebra.center_eq_bot ℝ FreudenthalTKK5E8⟩

theorem f13_t1_zeroE7Hom_injective_and_sl2 (X : H3ZornTKKLie) :
    Function.Injective zeroE7Hom ∧
    IsSl2Triple gradeCenterZ ePlus2 eMinus2 ∧
    ⁅zeroE7Hom X, gradeCenterZ⁆ = 0 ∧
    ⁅zeroE7Hom X, ePlus2⁆ = 0 ∧
    ⁅zeroE7Hom X, eMinus2⁆ = 0 :=
  ⟨zeroE7Hom_injective, freudenthalTKK5E8_sl2Triple,
    zeroE7Hom_comm_gradeCenterZ X, zeroE7Hom_comm_ePlus2 X, zeroE7Hom_comm_eMinus2 X⟩

theorem f13_t1_cartan_8d_abelian :
    Module.finrank ℝ tkk5E8Cartan = 8 ∧
    IsLieAbelian tkk5E8Cartan :=
  ⟨finrank_tkk5E8Cartan, tkk5E8Cartan_isLieAbelian⟩

theorem f13_t1_splitE8Lie_structural_agreement :
    Module.finrank ℝ FreudenthalTKK5E8 = Module.finrank ℝ SplitE8Lie ∧
    (Module.finrank ℝ tkk5E8CartanNoncompact : ℤ) - Module.finrank ℝ tkk5E8CartanCompact = 8 ∧
    (Module.finrank ℝ splitE8CartanNoncompact : ℤ) - Module.finrank ℝ splitE8CartanCompact = 8 :=
  ⟨by rw [finrank_freudenthalTKK5E8, finrank_splitE8Lie],
    freudenthalTKK5E8_cartan_signature_eq_pos_8, splitE8_signature_eq_pos_8⟩

theorem f13_t2_ePlus2_ad3_nilpotent_vs_bracket_eMinus2 :
    ⁅ePlus2, ⁅ePlus2, ⁅ePlus2, eMinus2⁆⁆⁆ = 0 ∧
    ⁅ePlus2, eMinus2⁆ ≠ 0 := by
  refine ⟨?_, ?_⟩
  · have hskew : ⁅ePlus2, gradeCenterZ⁆ = -⁅gradeCenterZ, ePlus2⁆ :=
      (lie_skew ePlus2 gradeCenterZ).symm
    rw [freudenthalTKK5E8_sl2Triple.lie_e_f, hskew,
      lie_neg, freudenthalTKK5E8_sl2Triple.lie_h_e_nsmul]
    simp [lie_self]
  · rw [freudenthalTKK5E8_sl2Triple.lie_e_f]
    exact freudenthalTKK5E8_sl2Triple.h_ne_zero

theorem f13_t2_Z_central_in_grade0_noncentral_in_e8 (X : H3ZornTKKLie)
    (Q : Charge) (hQ : Q ≠ 0) :
    ⁅gradeCenterZ, zeroE7Hom X⁆ = 0 ∧
    ⁅gradeCenterZ, ePlus2⁆ ≠ 0 ∧
    ⁅gradeCenterZ, injPlus1 Q⁆ ≠ 0 := by
  refine ⟨by rw [(lie_skew gradeCenterZ (zeroE7Hom X)).symm,
      zeroE7Hom_comm_gradeCenterZ X, neg_zero], ?_, ?_⟩
  · rw [freudenthalTKK5E8_sl2Triple.lie_h_e_nsmul]
    intro h0
    have he := congrArg FreudenthalTKK5E8.gPlus2 h0
    simp only [ePlus2, injPlus2] at he
    change (2 : ℕ) • (1 : ℝ) = 0 at he
    norm_num at he
  · intro h0
    have hbr : ⁅gradeCenterZ, injPlus1 Q⁆ = injPlus1 Q := by
      change bracket5LM gradeCenterZ (injPlus1 Q) = injPlus1 Q
      apply FreudenthalTKK5E8.ext <;>
        simp [bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
          bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2,
          gradeCenterZ, injZeroCenter, injPlus1]
    rw [hbr] at h0
    exact hQ (congrArg FreudenthalTKK5E8.gPlus1 h0)

theorem f13_t2_cartan_disjoint_nonzero_grades :
    (tkk5E8Cartan.toSubmodule ⊓ gGrade 1) = ⊥ ∧
    (tkk5E8Cartan.toSubmodule ⊓ gGrade (-1)) = ⊥ ∧
    (tkk5E8Cartan.toSubmodule ⊓ gGrade 2) = ⊥ ∧
    (tkk5E8Cartan.toSubmodule ⊓ gGrade (-2)) = ⊥ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [eq_bot_iff] <;> intro U ⟨hUc, hUg⟩
  · rcases (mem_tkk5E8Cartan_iff.mp hUc) with ⟨hm2, hm1, _, hp1, hp2⟩
    change U ∈ gGrade 1 at hUg
    rw [mem_gGrade_pos_one_iff] at hUg
    rcases hUg with ⟨_, _, hz7, hzc, _⟩
    exact FreudenthalTKK5E8.ext hm2 hm1 hz7 hzc hp1 hp2
  · rcases (mem_tkk5E8Cartan_iff.mp hUc) with ⟨hm2, hm1, _, hp1, hp2⟩
    change U ∈ gGrade (-1) at hUg
    rw [mem_gGrade_neg_one_iff] at hUg
    rcases hUg with ⟨_, hz7, hzc, _, _⟩
    exact FreudenthalTKK5E8.ext hm2 hm1 hz7 hzc hp1 hp2
  · rcases (mem_tkk5E8Cartan_iff.mp hUc) with ⟨hm2, hm1, _, hp1, hp2⟩
    change U ∈ gGrade 2 at hUg
    rw [mem_gGrade_pos_two_iff] at hUg
    rcases hUg with ⟨_, _, hz7, hzc, _⟩
    exact FreudenthalTKK5E8.ext hm2 hm1 hz7 hzc hp1 hp2
  · rcases (mem_tkk5E8Cartan_iff.mp hUc) with ⟨hm2, hm1, _, hp1, hp2⟩
    change U ∈ gGrade (-2) at hUg
    rw [mem_gGrade_neg_two_iff] at hUg
    rcases hUg with ⟨_, hz7, hzc, _, _⟩
    exact FreudenthalTKK5E8.ext hm2 hm1 hz7 hzc hp1 hp2

theorem f13_t2_signature_pos8_separates_compact_and_quaternionic :
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ FreudenthalTKK5E8) ∧
    IsEmpty (QuaternionicE8Lie ≃ₗ⁅ℝ⁆ FreudenthalTKK5E8) := by
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩
  · have hpos : 0 < Module.finrank ℝ tkk5E8CartanNoncompact := by
      rw [finrank_tkk5E8CartanNoncompact]; norm_num
    have hne : tkk5E8CartanNoncompact ≠ ⊥ := fun hb => by
      rw [hb, finrank_bot] at hpos; norm_num at hpos
    obtain ⟨Y, hYp, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hKpos : 0 < killingForm ℝ FreudenthalTKK5E8 Y Y :=
      lt_of_le_of_ne (tkk5_killingForm_cartanNoncompact_nonneg hYp)
        (fun h => hY0 ((tkk5_killingForm_cartanNoncompact_eq_zero_iff hYp).mp h.symm))
    have hKneg : killingForm ℝ CompactE8Lie (e.symm Y) (e.symm Y) ≤ 0 :=
      compactE8_killingForm_nonpos (e.symm Y)
    have heq := LieAlgebra.killingForm_of_equiv_apply e (e.symm Y) (e.symm Y)
    rw [e.apply_symm_apply] at heq
    linarith
  · let K' : Submodule ℝ FreudenthalTKK5E8 :=
      Submodule.map e.toLinearEquiv.toLinearMap quaternionicE8CartanCompact
    have hK'_fin : Module.finrank ℝ K' = 136 := by
      have heq := (e.toLinearEquiv.submoduleMap quaternionicE8CartanCompact).finrank_eq
      rw [← heq, finrank_quaternionicE8CartanCompact]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq K' tkk5E8CartanNoncompact
    have hle : Module.finrank ℝ (K' ⊔ tkk5E8CartanNoncompact : Submodule ℝ FreudenthalTKK5E8) ≤ 248 := by
      rw [← finrank_freudenthalTKK5E8]
      exact Submodule.finrank_le _
    have hinf : 0 < Module.finrank ℝ (K' ⊓ tkk5E8CartanNoncompact : Submodule ℝ FreudenthalTKK5E8) := by
      rw [hK'_fin, finrank_tkk5E8CartanNoncompact] at hsum
      omega
    have hne : (K' ⊓ tkk5E8CartanNoncompact : Submodule ℝ FreudenthalTKK5E8) ≠ ⊥ := fun hb => by
      rw [hb, finrank_bot] at hinf; norm_num at hinf
    obtain ⟨Y, hYmem, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rcases hYmem with ⟨hYK', hYp⟩
    have hKpos : 0 < killingForm ℝ FreudenthalTKK5E8 Y Y :=
      lt_of_le_of_ne (tkk5_killingForm_cartanNoncompact_nonneg hYp)
        (fun h => hY0 ((tkk5_killingForm_cartanNoncompact_eq_zero_iff hYp).mp h.symm))
    rcases Submodule.mem_map.mp hYK' with ⟨X, hXk, hXe⟩
    have hKneg : killingForm ℝ QuaternionicE8Lie X X ≤ 0 :=
      quaternionicE8_killingForm_k_nonpos hXk
    have heq := LieAlgebra.killingForm_of_equiv_apply e X X
    change killingForm ℝ FreudenthalTKK5E8 (e.toLinearEquiv.toLinearMap X)
      (e.toLinearEquiv.toLinearMap X) = killingForm ℝ QuaternionicE8Lie X X at heq
    rw [hXe] at heq
    linarith

theorem f13_t2_ideal_dichotomy (I : LieIdeal ℝ FreudenthalTKK5E8) :
    I = ⊥ ∨ I = ⊤ :=
  LieAlgebra.IsSimple.eq_bot_or_eq_top I

/-! =========================================================================
    TIER 3: CROSS-FEATURE COMBINATIONS (All 5 Major Pairs, 15 Theorems)
    ========================================================================= -/

/-! ### Pair 1 (`R1 ↔ R2`: `E₇` Serre ↔ `E₈` Serre) -/

theorem tier3_r1_r2_cartan_matrix_castSucc_eq (i j : Fin 7) :
    CartanMatrix.E 7 i j = CartanMatrix.E 8 i.castSucc j.castSucc :=
  cartanE7_eq_castSucc_E8 i j

theorem tier3_r1_r2_e7_embeds_into_e8_serre (i : Fin 7) :
    Function.Injective e7ToE8SerreHom ∧
    e7ToE8SerreHom (qE7H i) = qE8H i.castSucc ∧
    e7ToE8SerreHom (qE7E i) = qE8E i.castSucc ∧
    e7ToE8SerreHom (qE7F i) = qE8F i.castSucc := by
  refine ⟨?_, e7ToE8SerreHom_H i, e7ToE8SerreHom_E i, e7ToE8SerreHom_F i⟩
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top e7ToE8SerreHom.ker with hbot | htop
  · exact (LieHom.ker_eq_bot e7ToE8SerreHom).mp hbot
  · exfalso
    have hmem : qE7H 0 ∈ e7ToE8SerreHom.ker := by rw [htop]; trivial
    have hz : e7ToE8SerreHom (qE7H 0) = 0 := hmem
    rw [e7ToE8SerreHom_H] at hz
    have h1 := congrArg splitE8SerreEquiv hz
    rw [map_zero] at h1
    have hq : splitE8SerreEquiv (qE8H (0 : Fin 7).castSucc) = e8SimpleH 0 :=
      splitE8SerreQuotientMap_H 0
    rw [hq] at h1
    exact (e8Simple_isSl2Triple 0).h_ne_zero h1

theorem tier3_r1_r2_e7_strict_subalgebra_of_e8 (i : Fin 7) :
    Module.finrank ℝ (LieAlgebra.e₇ ℝ) < Module.finrank ℝ (LieAlgebra.e₈ ℝ) ∧
    IsSl2Triple (e7ToE8SerreHom (qE7H i)) (e7ToE8SerreHom (qE7E i)) (e7ToE8SerreHom (qE7F i)) := by
  refine ⟨by rw [finrank_e7_serre, finrank_e8_serre]; norm_num, ?_⟩
  rw [e7ToE8SerreHom_H, e7ToE8SerreHom_E, e7ToE8SerreHom_F]
  exact f6_t1_serre_equiv_sl2_triple i.castSucc

/-! ### Pair 2 (`R1 ↔ R4`: `E₇` Serre ↔ 5-Graded `E₈` & `56D` `repE7`) -/

theorem tier3_r1_r4_serre_e7_56d_rep_preserves_symplectic_and_quartic
    (x : LieAlgebra.e₇ ℝ) (Q₁ Q₂ : Charge) :
    let ρ := repE7.comp h3zornE7SerreEquiv.toLieHom
    symplecticForm (ρ x Q₁) Q₂ + symplecticForm Q₁ (ρ x Q₂) = 0 ∧
    HasDerivAt (fun t : ℝ => quarticInvariant (Q₁ + t • ρ x Q₁)) 0 0 :=
  ⟨repE7_symplecticForm_skew (h3zornE7SerreEquiv x) Q₁ Q₂,
    repE7_preserves_quarticInvariant_deriv (h3zornE7SerreEquiv x) Q₁⟩

theorem tier3_r1_r4_serre_e7_56d_rep_faithful :
    Function.Injective (repE7.comp h3zornE7SerreEquiv.toLieHom) := by
  let ρ := repE7.comp h3zornE7SerreEquiv.toLieHom
  rcases LieAlgebra.IsSimple.eq_bot_or_eq_top ρ.ker with hbot | htop
  · exact (LieHom.ker_eq_bot ρ).mp hbot
  · exfalso
    have hmem : qE7E 6 ∈ ρ.ker := by rw [htop]; trivial
    have hz : ρ (qE7E 6) = 0 := hmem
    have hx := congrArg (fun E : Module.End ℝ Charge => (E (scalarCharge 0 1)).x) hz
    change (repE7 (h3zornE7SerreEquiv (qE7E 6)) (scalarCharge 0 1)).x = 0 at hx
    have hq : h3zornE7SerreEquiv (qE7E 6) = negInj (h3ZornBasis 10) := by
      change h3zornE7SerreQuotientMap (qE7E 6) = _
      rw [h3zornE7SerreQuotientMap_E, e7SimpleE_six]
    have hn : (negInj (h3ZornBasis 10)).neg = h3ZornBasis 10 := rfl
    have hz' : (negInj (h3ZornBasis 10)).zero = 0 := rfl
    have hp : (negInj (h3ZornBasis 10)).pos = 0 := rfl
    have hqx : (scalarCharge 0 1).x = 0 := rfl
    have hqy : (scalarCharge 0 1).y = 0 := rfl
    have hqb : (scalarCharge 0 1).beta = 1 := rfl
    have hstr0 : strTrace (negInj (h3ZornBasis 10)).zero = 0 := by
      rw [hz']; exact map_zero strTrace
    have h00 : (negInj (h3ZornBasis 10)).zero.1 (0 : H3Zorn ℝ) = 0 := rfl
    have hcp0 : H3Zorn.crossProduct (0 : H3Zorn ℝ) 0 = 0 := by
      rw [H3Zorn.crossProduct, add_zero, sub_self, adjointQuad_zero, sub_zero]
    rw [hq, repE7_x, hn, hp, hqx, hqy, hqb, hcp0, hstr0, h00, one_smul,
      mul_zero, zero_smul, sub_zero, sub_zero, add_zero] at hx
    exact h3ZornBasis.ne_zero 10 ((smul_eq_zero.mp hx).resolve_left (by norm_num))

theorem tier3_r1_r4_serre_e7_embeds_in_tkk5_centralizing_sl2 (x : LieAlgebra.e₇ ℝ) :
    let ι := zeroE7Hom.comp h3zornE7SerreEquiv.toLieHom
    Function.Injective ι ∧
    ⁅ι x, gradeCenterZ⁆ = 0 ∧
    ⁅ι x, ePlus2⁆ = 0 ∧
    ⁅ι x, eMinus2⁆ = 0 :=
  ⟨zeroE7Hom_injective.comp h3zornE7SerreEquiv.injective,
    zeroE7Hom_comm_gradeCenterZ _, zeroE7Hom_comm_ePlus2 _, zeroE7Hom_comm_eMinus2 _⟩

/-! ### Pair 3 (`R2 ↔ R3`: `SplitE8` Serre ↔ `CompactE8` / `QuaternionicE8`) -/

theorem tier3_r2_r3_split_e8_serre_not_compact_or_quaternionic :
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ) ∧
    IsEmpty (QuaternionicE8Lie ≃ₗ⁅ℝ⁆ LieAlgebra.e₈ ℝ) :=
  ⟨⟨fun e => compactE8_not_lieEquiv_splitE8.false (e.trans splitE8SerreEquiv)⟩,
    ⟨fun e => quaternionicE8_not_lieEquiv_splitE8.false (e.trans splitE8SerreEquiv)⟩⟩

theorem tier3_r2_r3_all_three_real_forms_share_248_simple_killing :
    Module.finrank ℝ (LieAlgebra.e₈ ℝ) = 248 ∧
    Module.finrank ℝ QuaternionicE8Lie = 248 ∧
    Module.finrank ℝ CompactE8Lie = 248 ∧
    LieAlgebra.IsSimple ℝ (LieAlgebra.e₈ ℝ) ∧
    LieAlgebra.IsSimple ℝ QuaternionicE8Lie ∧
    LieAlgebra.IsSimple ℝ CompactE8Lie ∧
    LieAlgebra.IsKilling ℝ (LieAlgebra.e₈ ℝ) ∧
    LieAlgebra.IsKilling ℝ QuaternionicE8Lie ∧
    LieAlgebra.IsKilling ℝ CompactE8Lie :=
  ⟨finrank_e8_serre, finrank_quaternionicE8Lie, finrank_compactE8Lie,
    e8Serre_isSimple, quaternionicE8Lie_isSimple, compactE8Lie_isSimple,
    f6_t1_isKilling_and_center_bot.1, quaternionicE8Lie_isKilling, compactE8Lie_isKilling⟩

theorem tier3_r2_r3_complexifications_match_e8_serre :
    Nonempty (ℂ ⊗[ℝ] CompactE8Lie ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] LieAlgebra.e₈ ℝ) ∧
    Nonempty (ℂ ⊗[ℝ] QuaternionicE8Lie ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] LieAlgebra.e₈ ℝ) :=
  ⟨⟨compactE8BaseChangeEquiv.trans (extendScalarsLieEquiv splitE8SerreEquiv.symm)⟩,
    ⟨quaternionicE8BaseChangeEquiv.trans (extendScalarsLieEquiv splitE8SerreEquiv.symm)⟩⟩

/-! ### Pair 4 (`R2 ↔ R4`: `SplitE8` Serre ↔ 5-Graded `FreudenthalTKK5E8`) -/

theorem tier3_r2_r4_convergent_split_e8_invariants :
    Module.finrank ℝ (LieAlgebra.e₈ ℝ) = Module.finrank ℝ FreudenthalTKK5E8 ∧
    LieAlgebra.IsSimple ℝ (LieAlgebra.e₈ ℝ) ∧
    LieAlgebra.IsSimple ℝ FreudenthalTKK5E8 ∧
    LieAlgebra.IsKilling ℝ (LieAlgebra.e₈ ℝ) ∧
    LieAlgebra.IsKilling ℝ FreudenthalTKK5E8 :=
  ⟨by rw [finrank_e8_serre, finrank_freudenthalTKK5E8],
    e8Serre_isSimple, freudenthalTKK5E8_isSimple,
    f6_t1_isKilling_and_center_bot.1, freudenthalTKK5E8_isKilling⟩

theorem tier3_r2_r4_split_e8_serre_vs_tkk5_cartan_signatures :
    (Module.finrank ℝ splitE8CartanNoncompact : ℤ) - Module.finrank ℝ splitE8CartanCompact =
      (Module.finrank ℝ tkk5E8CartanNoncompact : ℤ) - Module.finrank ℝ tkk5E8CartanCompact ∧
    Module.finrank ℝ (LieAlgebra.e₈ ℝ) = 248 ∧
    Module.finrank ℝ FreudenthalTKK5E8 = 248 :=
  ⟨by rw [splitE8_signature_eq_pos_8, freudenthalTKK5E8_cartan_signature_eq_pos_8],
    finrank_e8_serre, finrank_freudenthalTKK5E8⟩

theorem tier3_r2_r4_split_e8_serre_cartan_rank8_and_killing_ortho :
    Module.finrank ℝ tkk5E8Cartan = 8 ∧
    Module.finrank ℝ splitE8Cartan = 8 ∧
    IsLieAbelian tkk5E8Cartan ∧
    IsLieAbelian splitE8Cartan ∧
    (∀ X ∈ splitE8CartanCompact, ∀ Y ∈ splitE8CartanNoncompact,
      killingForm ℝ SplitE8Lie X Y = 0) ∧
    (∀ U ∈ tkk5E8CartanCompact, ∀ V ∈ tkk5E8CartanNoncompact,
      killingForm ℝ FreudenthalTKK5E8 U V = 0) :=
  ⟨finrank_tkk5E8Cartan, finrank_splitE8Cartan, tkk5E8Cartan_isLieAbelian,
    splitE8Cartan_isLieAbelian,
    fun _ hX _ hY => splitE8_killingForm_k_p_ortho hX hY,
    fun _ hU _ hV => tkk5_killingForm_cartanCompact_noncompact_ortho hU hV⟩

/-! ### Pair 5 (`R3 ↔ R4`: `CompactE8MagicSquare` ↔ `H3ZornFreudenthalTKK5E8`) -/

theorem tier3_r3_r4_albert_real_form_divergence (x y : H3Octonion ℝ) :
    IsEmpty (H3Octonion ℝ ≃+* H3Zorn ℝ) ∧
    (x * x + y * y = 0 → x = 0 ∧ y = 0) ∧
    (∃ w : H3Zorn ℝ, w ≠ 0 ∧ w * w = 0) :=
  ⟨H3Octonion.no_jordanIso_H3Octonion_H3Zorn, H3Octonion.formal_reality x y,
    f9_t2_h3zorn_nilpotent_witness⟩

theorem tier3_r3_r4_e7_real_form_divergence_neg25_vs_tkk5_e7 :
    (Module.finrank ℝ h3OctonionCartanNoncompactSubmodule : ℤ) -
      Module.finrank ℝ h3OctonionCartanCompactSubalgebra = -25 ∧
    (Module.finrank ℝ e7Noncompact : ℤ) - Module.finrank ℝ e7Compact = 7 ∧
    Module.finrank ℝ H3OctonionTKKLie = Module.finrank ℝ H3ZornTKKLie := by
  refine ⟨h3OctonionCartan_signature_eq_neg_25, ?_, ?_⟩
  · rw [finrank_e7Noncompact, finrank_e7Compact]; norm_num
  · rw [finrank_H3OctonionTKKLie, finrank_H3ZornTKKLie]

theorem tier3_r3_r4_tkk5_e8_not_iso_compact_or_quaternionic :
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ FreudenthalTKK5E8) ∧
    IsEmpty (QuaternionicE8Lie ≃ₗ⁅ℝ⁆ FreudenthalTKK5E8) ∧
    (-248 : ℤ) ≠ 8 ∧
    (-24 : ℤ) ≠ 8 :=
  ⟨f13_t2_signature_pos8_separates_compact_and_quaternionic.1,
    f13_t2_signature_pos8_separates_compact_and_quaternionic.2,
    e8_real_form_signatures_pairwise_distinct.2.2,
    e8_real_form_signatures_pairwise_distinct.2.1⟩

/-! =========================================================================
    TIER 4: REAL-WORLD MATHEMATICAL APPLICATION SCENARIOS (Scenarios 1–6)
    ========================================================================= -/

theorem tier4_scenario1_e7_serre_to_tkk_to_56d_to_5graded_e8 :
    let X : H3ZornTKKLie := h3zornE7SerreEquiv (qE7E 6)
    let Q := scalarCharge 0 1
    X = negInj (h3ZornBasis 10) ∧
    symplecticForm (repE7 X Q) Q + symplecticForm Q (repE7 X Q) = 0 ∧
    HasDerivAt (fun t : ℝ => quarticInvariant (Q + t • repE7 X Q)) 0 0 ∧
    ⁅zeroE7Hom X, injPlus1 Q⁆ ∈ gGrade 1 ∧
    ⁅zeroE7Hom X, injPlus1 Q⁆ = injPlus1 (repE7 X Q) := by
  intro X Q
  have hX : X = negInj (h3ZornBasis 10) := by
    change h3zornE7SerreQuotientMap (qE7E 6) = _
    rw [h3zornE7SerreQuotientMap_E, e7SimpleE_six]
  have hz0 : zeroE7Hom X ∈ gGrade 0 := (mem_gGrade_zero_iff _).mpr ⟨rfl, rfl, rfl, rfl⟩
  have h1 : injPlus1 Q ∈ gGrade 1 := (mem_gGrade_pos_one_iff _).mpr ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hbr : ⁅zeroE7Hom X, injPlus1 Q⁆ = injPlus1 (repE7 X Q) := by
    change bracket5LM (zeroE7Hom X) (injPlus1 Q) = injPlus1 (repE7 X Q)
    apply FreudenthalTKK5E8.ext <;>
      simp [bracket5LM_gMinus2, bracket5LM_gMinus1, bracket5LM_gZeroE7,
        bracket5LM_gZeroCenter, bracket5LM_gPlus1, bracket5LM_gPlus2, zeroE7Hom, injZeroE7, injPlus1]
  exact ⟨hX, repE7_symplecticForm_skew X Q Q, repE7_preserves_quarticInvariant_deriv X Q,
    by simpa using gGrade_bracket_mem hz0 h1, hbr⟩

theorem tier4_scenario2_complete_e8_real_form_trichotomy :
    Module.finrank ℝ CompactE8Lie = 248 ∧
    Module.finrank ℝ QuaternionicE8Lie = 248 ∧
    Module.finrank ℝ SplitE8Lie = 248 ∧
    Module.finrank ℝ FreudenthalTKK5E8 = 248 ∧
    (Module.finrank ℝ compactE8CartanNoncompact : ℤ) - Module.finrank ℝ compactE8CartanCompact = -248 ∧
    (Module.finrank ℝ quaternionicE8CartanNoncompact : ℤ) - Module.finrank ℝ quaternionicE8CartanCompact = -24 ∧
    (Module.finrank ℝ splitE8CartanNoncompact : ℤ) - Module.finrank ℝ splitE8CartanCompact = 8 ∧
    (Module.finrank ℝ tkk5E8CartanNoncompact : ℤ) - Module.finrank ℝ tkk5E8CartanCompact = 8 ∧
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ QuaternionicE8Lie) ∧
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ SplitE8Lie) ∧
    IsEmpty (QuaternionicE8Lie ≃ₗ⁅ℝ⁆ SplitE8Lie) ∧
    IsEmpty (CompactE8Lie ≃ₗ⁅ℝ⁆ FreudenthalTKK5E8) ∧
    IsEmpty (QuaternionicE8Lie ≃ₗ⁅ℝ⁆ FreudenthalTKK5E8) ∧
    Nonempty (ℂ ⊗[ℝ] CompactE8Lie ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] SplitE8Lie) ∧
    Nonempty (ℂ ⊗[ℝ] QuaternionicE8Lie ≃ₗ⁅ℂ⁆ ℂ ⊗[ℝ] SplitE8Lie) :=
  ⟨finrank_compactE8Lie, finrank_quaternionicE8Lie, finrank_splitE8Lie, finrank_freudenthalTKK5E8,
    compactE8_signature_eq_neg_248, quaternionicE8_signature_eq_neg_24,
    splitE8_signature_eq_pos_8, freudenthalTKK5E8_cartan_signature_eq_pos_8,
    compactE8_not_lieEquiv_quaternionicE8, compactE8_not_lieEquiv_splitE8,
    quaternionicE8_not_lieEquiv_splitE8,
    f13_t2_signature_pos8_separates_compact_and_quaternionic.1,
    f13_t2_signature_pos8_separates_compact_and_quaternionic.2,
    ⟨compactE8BaseChangeEquiv⟩, ⟨quaternionicE8BaseChangeEquiv⟩⟩

theorem tier4_scenario3_magic_square_rows3_row4_ladder :
    Module.finrank ℝ CompactOctonionDerivations = 14 ∧
    Module.finrank ℝ H3OctonionF4Derivations = 52 ∧
    Module.finrank ℝ h3OctonionCubicStabilizer = 78 ∧
    Module.finrank ℝ H3OctonionTKKLie = 133 ∧
    Module.finrank ℝ CompactE8Lie = 248 ∧
    Module.finrank ℝ G2DerivationCarrier = 14 ∧
    Module.finrank ℝ F4DerivationCarrier = 52 ∧
    Module.finrank ℝ h3zornCubicStabilizer = 78 ∧
    Module.finrank ℝ H3ZornTKKLie = 133 ∧
    Module.finrank ℝ QuaternionicE8Lie = 248 ∧
    Module.finrank ℝ SplitE8Lie = 248 ∧
    (∀ D : CompactOctonionDerivations, LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) ≤ 0) ∧
    (∀ F : H3OctonionF4Derivations, LinearMap.trace ℝ (H3Octonion ℝ) (F.1 * F.1) ≤ 0) ∧
    LinearMap.trace ℝ (H3Zorn ℝ) (splitF4TracePosWitness.1 * splitF4TracePosWitness.1) = 3 / 2 :=
  ⟨finrank_compactOctonionDerivations, finrank_H3OctonionF4Derivations,
    finrank_h3OctonionCubicStabilizer, finrank_H3OctonionTKKLie, finrank_compactE8Lie,
    finrank_g2DerivationCarrier, finrank_f4DerivationCarrier,
    finrank_h3zornCubicStabilizer, finrank_H3ZornTKKLie,
    finrank_quaternionicE8Lie, finrank_splitE8Lie,
    compactG2_trace_sq_nonpos, compactF4_trace_sq_nonpos, splitF4TracePosWitness_trace_sq⟩

theorem tier4_scenario4_sl2_e7_heisenberg_parabolic_and_8d_cartan
    (x : LieAlgebra.e₇ ℝ) (U V W : FreudenthalTKK5E8) :
    IsSl2Triple gradeCenterZ ePlus2 eMinus2 ∧
    ⁅zeroE7Hom (h3zornE7SerreEquiv x), gradeCenterZ⁆ = 0 ∧
    ⁅zeroE7Hom (h3zornE7SerreEquiv x), ePlus2⁆ = 0 ∧
    ⁅zeroE7Hom (h3zornE7SerreEquiv x), eMinus2⁆ = 0 ∧
    Module.finrank ℝ tkk5E8Cartan = 8 ∧
    IsLieAbelian tkk5E8Cartan ∧
    Module.finrank ℝ (gGrade (-2)) + Module.finrank ℝ (gGrade (-1)) +
      Module.finrank ℝ (gGrade 0) + Module.finrank ℝ (gGrade 1) +
      Module.finrank ℝ (gGrade 2) = 248 ∧
    B₅ ⁅U, V⁆ W + B₅ V ⁅U, W⁆ = 0 ∧
    (cartanInner5 U U = 0 ↔ U = 0) := by
  refine ⟨freudenthalTKK5E8_sl2Triple, zeroE7Hom_comm_gradeCenterZ _,
    zeroE7Hom_comm_ePlus2 _, zeroE7Hom_comm_eMinus2 _,
    finrank_tkk5E8Cartan, tkk5E8Cartan_isLieAbelian, ?_,
    B₅_lieInvariant U V W, cartanInner5_eq_zero_iff U⟩
  rw [finrank_gGrade_neg_two, finrank_gGrade_neg_one, finrank_gGrade_zero,
    finrank_gGrade_pos_one, finrank_gGrade_pos_two]

theorem tier4_scenario5_exceptional_serre_tower_e6_e7_e8 :
    Function.Injective e6ToE7SerreHom ∧
    Function.Injective e7ToE8SerreHom ∧
    Module.finrank ℝ (LieAlgebra.e₆ ℝ) = 78 ∧
    Module.finrank ℝ (LieAlgebra.e₇ ℝ) = 133 ∧
    Module.finrank ℝ (LieAlgebra.e₈ ℝ) = 248 ∧
    LieAlgebra.IsSimple ℝ (LieAlgebra.e₆ ℝ) ∧
    LieAlgebra.IsSimple ℝ (LieAlgebra.e₇ ℝ) ∧
    LieAlgebra.IsSimple ℝ (LieAlgebra.e₈ ℝ) ∧
    LieAlgebra.IsKilling ℝ (LieAlgebra.e₆ ℝ) ∧
    LieAlgebra.IsKilling ℝ (LieAlgebra.e₇ ℝ) ∧
    LieAlgebra.IsKilling ℝ (LieAlgebra.e₈ ℝ) := by
  have hinj67 : Function.Injective e6ToE7SerreHom :=
    h3zornE7SerreEquiv.symm.injective.comp
      (h3zornCubicStabilizerToTKK_injective.comp h3zornE6SerreEquiv.injective)
  have hk6 : LieAlgebra.IsKilling ℝ (LieAlgebra.e₆ ℝ) :=
    LieEquiv.isKilling h3zornE6SerreEquiv.symm
  exact ⟨hinj67, (tier3_r1_r2_e7_embeds_into_e8_serre 0).1,
    finrank_e6_serre, finrank_e7_serre, finrank_e8_serre,
    e6Serre_isSimple, e7Serre_isSimple, e8Serre_isSimple,
    hk6, f3_t1_isKilling_and_center_bot.1, f6_t1_isKilling_and_center_bot.1⟩

theorem tier4_scenario6_quartic_symplectic_charge_orbits_in_e8 (X : H3ZornTKKLie) :
    let Q_reg := electricCharge 1 (1 : H3Zorn ℝ)
    let Q_bnd := scalarCharge 1 0
    let Q_sc := scalarCharge 0 1
    Regular Q_reg ∧
    quarticInvariant Q_reg = -4 ∧
    Boundary Q_bnd ∧
    quarticInvariant Q_bnd = 0 ∧
    symplecticForm Q_bnd Q_sc = 1 ∧
    HasDerivAt (fun t : ℝ => quarticInvariant (Q_reg + t • repE7 X Q_reg)) 0 0 ∧
    HasDerivAt (fun t : ℝ => quarticInvariant (Q_bnd + t • repE7 X Q_bnd)) 0 0 ∧
    ⁅injPlus1 Q_bnd, injMinus1 Q_sc⁆ =
      injZeroE7 (K Q_bnd Q_sc) + injZeroCenter (-(1 / 2 : ℝ)) ∧
    K Q_bnd Q_sc ≠ 0 ∧
    ⁅injPlus1 Q_bnd, injPlus1 Q_sc⁆ = ePlus2 := by
  intro Q_reg Q_bnd Q_sc
  have hsymp : symplecticForm Q_bnd Q_sc = 1 := by
    rw [symplecticForm_expanded]; simp [Q_bnd, Q_sc, scalarCharge]
  have hheis := (f12_t1_heisenberg_brackets Q_bnd Q_sc).1
  rw [hsymp, mul_one] at hheis
  refine ⟨f11_t2_charge_orbits_regular_boundary_scalar.1, unit_electric_quartic,
    f11_t2_charge_orbits_regular_boundary_scalar.2.1,
    f11_t2_charge_orbits_regular_boundary_scalar.2.2,
    hsymp,
    repE7_preserves_quarticInvariant_deriv X Q_reg,
    repE7_preserves_quarticInvariant_deriv X Q_bnd,
    hheis,
    f12_t2_heisenberg_nonzero_K_projection.2,
    f12_t2_boundary_charges_jacobi_and_grade.2.1⟩

/-! =========================================================================
    TIER 5: ADVERSARIAL COVERAGE HARDENING (T1–T10)
    ========================================================================= -/

/-! ### T1: Serre Quotient Kernel Triviality (`ker = ⊥`) & `.symm` Round-Trips -/

theorem t5_t1_e7_serre_quotient_ker_bot_and_roundtrip
    (x : LieAlgebra.e₇ ℝ) (y : H3ZornTKKLie) :
    LinearMap.ker h3zornE7SerreQuotientMap.toLinearMap = ⊥ ∧
    h3zornE7SerreEquiv.symm (h3zornE7SerreEquiv x) = x ∧
    h3zornE7SerreEquiv (h3zornE7SerreEquiv.symm y) = y :=
  ⟨LinearMap.ker_eq_bot.mpr h3zornE7SerreQuotientMap_injective,
    h3zornE7SerreEquiv.symm_apply_apply x,
    h3zornE7SerreEquiv.apply_symm_apply y⟩

theorem t5_t1_e8_serre_quotient_ker_bot_and_roundtrip
    (x : LieAlgebra.e₈ ℝ) (y : SplitE8Lie) :
    LinearMap.ker splitE8SerreQuotientMap.toLinearMap = ⊥ ∧
    splitE8SerreEquiv.symm (splitE8SerreEquiv x) = x ∧
    splitE8SerreEquiv (splitE8SerreEquiv.symm y) = y :=
  ⟨LinearMap.ker_eq_bot.mpr splitE8SerreQuotientMap_injective,
    splitE8SerreEquiv.symm_apply_apply x,
    splitE8SerreEquiv.apply_symm_apply y⟩

/-! ### T2: Missing Central `E₈` Edges `(2,3), (3,4), (4,5)` & Universal `(i, j)` Serre Identities -/

theorem t5_t2_e8_central_spine_serre_E :
    ⁅e8SimpleE 2, ⁅e8SimpleE 2, e8SimpleE 3⁆⁆ = 0 ∧
    ⁅e8SimpleE 3, ⁅e8SimpleE 3, e8SimpleE 4⁆⁆ = 0 ∧
    ⁅e8SimpleE 4, ⁅e8SimpleE 4, e8SimpleE 5⁆⁆ = 0 := by
  have h23 := e8Simple_serre_E (i := (2 : Fin 8)) (j := 3) (by decide)
  have h34 := e8Simple_serre_E (i := (3 : Fin 8)) (j := 4) (by decide)
  have h45 := e8Simple_serre_E (i := (4 : Fin 8)) (j := 5) (by decide)
  rw [splitE8_cartan_eq_mathlib] at h23 h34 h45
  have c23 : (1 - CartanMatrix.E 8 2 3).toNat = 2 := by decide
  have c34 : (1 - CartanMatrix.E 8 3 4).toNat = 2 := by decide
  have c45 : (1 - CartanMatrix.E 8 4 5).toNat = 2 := by decide
  rw [c23] at h23; rw [c34] at h34; rw [c45] at h45
  exact ⟨by simpa using h23, by simpa using h34, by simpa using h45⟩

theorem t5_t2_e8_central_spine_serre_F :
    ⁅e8SimpleF 2, ⁅e8SimpleF 2, e8SimpleF 3⁆⁆ = 0 ∧
    ⁅e8SimpleF 3, ⁅e8SimpleF 3, e8SimpleF 4⁆⁆ = 0 ∧
    ⁅e8SimpleF 4, ⁅e8SimpleF 4, e8SimpleF 5⁆⁆ = 0 := by
  have h23 := e8Simple_serre_F (i := (2 : Fin 8)) (j := 3) (by decide)
  have h34 := e8Simple_serre_F (i := (3 : Fin 8)) (j := 4) (by decide)
  have h45 := e8Simple_serre_F (i := (4 : Fin 8)) (j := 5) (by decide)
  rw [splitE8_cartan_eq_mathlib] at h23 h34 h45
  have c23 : (1 - CartanMatrix.E 8 2 3).toNat = 2 := by decide
  have c34 : (1 - CartanMatrix.E 8 3 4).toNat = 2 := by decide
  have c45 : (1 - CartanMatrix.E 8 4 5).toNat = 2 := by decide
  rw [c23] at h23; rw [c34] at h34; rw [c45] at h45
  exact ⟨by simpa using h23, by simpa using h34, by simpa using h45⟩

theorem t5_t2_e7_universal_serre (i j : Fin 7) (hij : i ≠ j) :
    (Nat.iterate (fun x => ⁅e7SimpleE i, x⁆)
      (1 - CartanMatrix.E 7 i j).toNat) (e7SimpleE j) = 0 ∧
    (Nat.iterate (fun x => ⁅e7SimpleF i, x⁆)
      (1 - CartanMatrix.E 7 i j).toNat) (e7SimpleF j) = 0 := by
  have hE := e7Simple_serre_E hij
  have hF := e7Simple_serre_F hij
  rw [h3zornE7_cartan_eq_mathlib] at hE hF
  exact ⟨hE, hF⟩

theorem t5_t2_e8_universal_serre (i j : Fin 8) (hij : i ≠ j) :
    (Nat.iterate (fun x => ⁅e8SimpleE i, x⁆)
      (1 - CartanMatrix.E 8 i j).toNat) (e8SimpleE j) = 0 ∧
    (Nat.iterate (fun x => ⁅e8SimpleF i, x⁆)
      (1 - CartanMatrix.E 8 i j).toNat) (e8SimpleF j) = 0 := by
  have hE := e8Simple_serre_E hij
  have hF := e8Simple_serre_F hij
  rw [splitE8_cartan_eq_mathlib] at hE hF
  exact ⟨hE, hF⟩

/-! ### T3: Universal `∀ X ≠ 0` Killing Sign Definiteness Across All Forms -/

theorem t5_t3_compactG2_trace_sq_strictly_neg
    (D : CompactOctonionDerivations) (hD : D ≠ 0) :
    LinearMap.trace ℝ (CompactOctonion ℝ) (D.1 * D.1) < 0 :=
  lt_of_le_of_ne (compactG2_trace_sq_nonpos D)
    (fun h => hD ((compactG2_trace_sq_eq_zero_iff D).mp h))

theorem t5_t3_compactE8_killingForm_strictly_neg
    (X : CompactE8Lie) (hX : X ≠ 0) :
    killingForm ℝ CompactE8Lie X X < 0 :=
  lt_of_le_of_ne (compactE8_killingForm_nonpos X)
    (fun h => hX ((compactE8_killingForm_eq_zero_iff X).mp h))

theorem t5_t3_quaternionicE8_killingForm_k_neg_p_pos :
    (∀ {X : QuaternionicE8Lie}, X ∈ quaternionicE8CartanCompact → X ≠ 0 →
      killingForm ℝ QuaternionicE8Lie X X < 0) ∧
    (∀ {Y : QuaternionicE8Lie}, Y ∈ quaternionicE8CartanNoncompact → Y ≠ 0 →
      0 < killingForm ℝ QuaternionicE8Lie Y Y) :=
  ⟨fun hXk hX0 => lt_of_le_of_ne (quaternionicE8_killingForm_k_nonpos hXk)
      (fun h => hX0 ((quaternionicE8_killingForm_k_eq_zero_iff hXk).mp h)),
   fun hYp hY0 => lt_of_le_of_ne (quaternionicE8_killingForm_p_nonneg hYp)
      (fun h => hY0 ((quaternionicE8_killingForm_p_eq_zero_iff hYp).mp h.symm))⟩

theorem t5_t3_splitE8_killingForm_k_neg_p_pos :
    (∀ {X : SplitE8Lie}, X ∈ splitE8CartanCompact → X ≠ 0 →
      killingForm ℝ SplitE8Lie X X < 0) ∧
    (∀ {Y : SplitE8Lie}, Y ∈ splitE8CartanNoncompact → Y ≠ 0 →
      0 < killingForm ℝ SplitE8Lie Y Y) :=
  ⟨fun hXk hX0 => lt_of_le_of_ne (splitE8_killingForm_k_nonpos hXk)
      (fun h => hX0 ((splitE8_killingForm_k_eq_zero_iff hXk).mp h)),
   fun hYp hY0 => lt_of_le_of_ne (splitE8_killingForm_p_nonneg hYp)
      (fun h => hY0 ((splitE8_killingForm_p_eq_zero_iff hYp).mp h.symm))⟩

theorem t5_t3_tkk5E8_killingForm_k_neg_p_pos :
    (∀ {X : FreudenthalTKK5E8}, X ∈ tkk5E8CartanCompact → X ≠ 0 →
      killingForm ℝ FreudenthalTKK5E8 X X < 0) ∧
    (∀ {Y : FreudenthalTKK5E8}, Y ∈ tkk5E8CartanNoncompact → Y ≠ 0 →
      0 < killingForm ℝ FreudenthalTKK5E8 Y Y) :=
  ⟨fun hXk hX0 => lt_of_le_of_ne (tkk5_killingForm_cartanCompact_nonpos hXk)
      (fun h => hX0 ((tkk5_killingForm_cartanCompact_eq_zero_iff hXk).mp h)),
   fun hYp hY0 => lt_of_le_of_ne (tkk5_killingForm_cartanNoncompact_nonneg hYp)
      (fun h => hY0 ((tkk5_killingForm_cartanNoncompact_eq_zero_iff hYp).mp h.symm))⟩

/-! ### T4: Magic Square `(3, -6, 1)` `(g2, mixed, f4)` Coefficients & Sector Orthogonality -/

theorem t5_t4_magicInvBilin_sector_coeffs_and_ortho
    {O₀ G₂ J₀ F₄ : Type}
    [AddCommGroup O₀] [Module ℝ O₀] [LieRing G₂] [LieAlgebra ℝ G₂]
    [AddCommGroup J₀] [Module ℝ J₀] [LieRing F₄] [LieAlgebra ℝ F₄]
    (O : OctonionMagicDatum O₀ G₂) (J : JordanMagicDatum J₀ F₄)
    (D₁ D₂ : G₂) (m₁ m₂ : O₀ ⊗[ℝ] J₀) (F₁ F₂ : F₄) :
    magicInvBilin O J (msEmbedG2LM O J D₁) (msEmbedG2LM O J D₂) = 3 * O.g2Bilin D₁ D₂ ∧
    magicInvBilin O J (msEmbedMixed O J m₁) (msEmbedMixed O J m₂) =
      -6 * magicMixedBilin O J m₁ m₂ ∧
    magicInvBilin O J (msEmbedF4LM O J F₁) (msEmbedF4LM O J F₂) = J.f4Bilin F₁ F₂ ∧
    magicInvBilin O J (msEmbedG2LM O J D₁) (msEmbedF4LM O J F₁) = 0 ∧
    magicInvBilin O J (msEmbedG2LM O J D₁) (msEmbedMixed O J m₁) = 0 ∧
    magicInvBilin O J (msEmbedF4LM O J F₁) (msEmbedMixed O J m₁) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [magicInvBilin_apply]

theorem t5_t4_splitE8InvBilin_sector_coeffs_and_ortho
    (D₁ D₂ : G2DerivationCarrier)
    (m₁ m₂ : splitOctonionTraceZero ⊗[ℝ] h3TraceZero)
    (F₁ F₂ : F4DerivationCarrier) :
    splitE8InvBilin ⟨D₁, 0, 0⟩ ⟨D₂, 0, 0⟩ = 3 * splitOctonionDatum.g2Bilin D₁ D₂ ∧
    splitE8InvBilin ⟨0, m₁, 0⟩ ⟨0, m₂, 0⟩ =
      -6 * magicMixedBilin splitOctonionDatum h3ZornJordanDatum m₁ m₂ ∧
    splitE8InvBilin ⟨0, 0, F₁⟩ ⟨0, 0, F₂⟩ = h3ZornJordanDatum.f4Bilin F₁ F₂ ∧
    splitE8InvBilin ⟨D₁, 0, 0⟩ ⟨0, 0, F₁⟩ = 0 ∧
    splitE8InvBilin ⟨D₁, 0, 0⟩ ⟨0, m₁, 0⟩ = 0 ∧
    splitE8InvBilin ⟨0, 0, F₁⟩ ⟨0, m₁, 0⟩ = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change magicInvBilin splitOctonionDatum h3ZornJordanDatum
      (msEmbedG2LM splitOctonionDatum h3ZornJordanDatum D₁)
      (msEmbedG2LM splitOctonionDatum h3ZornJordanDatum D₂) = _
    simp [magicInvBilin_apply]
  · change magicInvBilin splitOctonionDatum h3ZornJordanDatum
      (msEmbedMixed splitOctonionDatum h3ZornJordanDatum m₁)
      (msEmbedMixed splitOctonionDatum h3ZornJordanDatum m₂) = _
    simp [magicInvBilin_apply]
  · change magicInvBilin splitOctonionDatum h3ZornJordanDatum
      (msEmbedF4LM splitOctonionDatum h3ZornJordanDatum F₁)
      (msEmbedF4LM splitOctonionDatum h3ZornJordanDatum F₂) = _
    simp [magicInvBilin_apply]
  · change magicInvBilin splitOctonionDatum h3ZornJordanDatum
      (msEmbedG2LM splitOctonionDatum h3ZornJordanDatum D₁)
      (msEmbedF4LM splitOctonionDatum h3ZornJordanDatum F₁) = 0
    simp [magicInvBilin_apply]
  · change magicInvBilin splitOctonionDatum h3ZornJordanDatum
      (msEmbedG2LM splitOctonionDatum h3ZornJordanDatum D₁)
      (msEmbedMixed splitOctonionDatum h3ZornJordanDatum m₁) = 0
    simp [magicInvBilin_apply]
  · change magicInvBilin splitOctonionDatum h3ZornJordanDatum
      (msEmbedF4LM splitOctonionDatum h3ZornJordanDatum F₁)
      (msEmbedMixed splitOctonionDatum h3ZornJordanDatum m₁) = 0
    simp [magicInvBilin_apply]

/-! ### T5: Cartan Involution Homomorphisms & Compact Triviality -/

theorem t5_t5_cartan_involutions_hom_and_compact_trivial
    (X Y : CompactE8Lie) (U V : QuaternionicE8Lie) (A B : SplitE8Lie) :
    compactE8CartanInvolution X = X ∧
    compactE8CartanInvolution ⁅X, Y⁆ =
      ⁅compactE8CartanInvolution X, compactE8CartanInvolution Y⁆ ∧
    quaternionicE8CartanInvolution ⁅U, V⁆ =
      ⁅quaternionicE8CartanInvolution U, quaternionicE8CartanInvolution V⁆ ∧
    splitE8CartanInvolution ⁅A, B⁆ =
      ⁅splitE8CartanInvolution A, splitE8CartanInvolution B⁆ :=
  ⟨rfl, compactE8CartanInvolution.map_lie X Y,
    quaternionicE8CartanInvolution.map_lie U V,
    splitE8CartanInvolution.map_lie A B⟩

/-! ### T6: 5-Grade TKK `E₈` Structural Invariants (`K`, `B₅`, `B_E7`, `θ₅`, `θE7`) -/

theorem t5_t6_tkk5_K_and_triple_invariants
    (X : H3ZornTKKLie) (Q₁ Q₂ Q₃ : Charge) :
    K Q₁ Q₂ = K Q₂ Q₁ ∧
    ⁅X, K Q₁ Q₂⁆ = K (repE7 X Q₁) Q₂ + K Q₁ (repE7 X Q₂) ∧
    repE7 (K Q₁ Q₂) Q₃ - repE7 (K Q₃ Q₂) Q₁ =
      (1 / 2 : ℝ) • (symplecticForm Q₁ Q₂ • Q₃ - symplecticForm Q₃ Q₂ • Q₁) +
        symplecticForm Q₁ Q₃ • Q₂ :=
  ⟨K_symm Q₁ Q₂, K_equivariant X Q₁ Q₂, triple_identity_p1_m1_p1 Q₁ Q₂ Q₃⟩

theorem t5_t6_tkk5_bilinear_and_involutions
    (U V : FreudenthalTKK5E8) (X Y Z : H3ZornTKKLie) :
    B₅ (θ₅ U) (θ₅ V) = B₅ U V ∧
    B_E7 ⁅Z, X⁆ Y + B_E7 X ⁅Z, Y⁆ = 0 ∧
    θ₅ ⁅U, V⁆ = ⁅θ₅ U, θ₅ V⁆ ∧
    θ₅ (θ₅ U) = U ∧
    θE7 ⁅X, Y⁆ = ⁅θE7 X, θE7 Y⁆ ∧
    θE7 (θE7 X) = X :=
  ⟨B₅_θ₅ U V, B_E7_lieInvariant Z X Y, θ₅.map_lie U V, θ₅_involutive U,
    θE7.map_lie X Y, θE7_involutive X⟩

/-! ### T7: Regular Charge `scalarCharge 1 1` Quartic Invariance & Nontrivial Action -/

theorem t5_t7_regular_scalarCharge_1_1_quartic_invariance :
    let Q := scalarCharge 1 1
    quarticInvariant Q = 1 ∧
    quarticInvariant Q ≠ 0 ∧
    repE7 (posInj 1) Q ≠ 0 ∧
    HasDerivAt (fun t : ℝ => quarticInvariant (Q + t • repE7 (posInj 1) Q)) 0 0 := by
  intro Q
  have hq : quarticInvariant Q = 1 := by
    change quarticInvariant (scalarCharge 1 1) = 1
    rw [quarticInvariant_scalarCharge]
    norm_num
  have hnz : repE7 (posInj 1) Q ≠ 0 := by
    intro h0
    have hy := congrArg (fun C : Charge => C.y.α₁) h0
    have hy1 : (repE7 (posInj 1) Q).y.α₁ = 1 := by
      rw [repE7_y]
      have hp0 : (posInj (1 : H3Zorn ℝ)).neg = 0 := rfl
      have hz0 : (posInj (1 : H3Zorn ℝ)).zero = 0 := rfl
      have hpp : (posInj (1 : H3Zorn ℝ)).pos = 1 := rfl
      have hstr0 : strTrace (0 : h3zornTKKDatum.str) = 0 := map_zero strTrace
      have hcp0 : H3Zorn.crossProduct (0 : H3Zorn ℝ) 0 = 0 := by
        rw [H3Zorn.crossProduct, add_zero, sub_self, adjointQuad_zero, sub_zero]
      have hqx : Q.x = 0 := rfl
      have hqy : Q.y = 0 := rfl
      have hqa : Q.alpha = 1 := rfl
      rw [hp0, hz0, hpp, hstr0, hqx, hqy, hqa, hcp0, map_zero, neg_zero, smul_zero,
        mul_zero, zero_smul, add_zero, zero_add, zero_add, one_smul]
      rfl
    rw [hy1, show (0 : Charge).y.α₁ = 0 from rfl] at hy
    norm_num at hy
  exact ⟨hq, by rw [hq]; norm_num, hnz, repE7_preserves_quarticInvariant_deriv (posInj 1) Q⟩

/-! ### T8: Mixed-Grade Jacobi Identities `(g₊₂, g₋₁, g₋₁)` and `(g₀, g₊₁, g₋₁)` -/

theorem t5_t8_mixed_grade_jacobi (P₁ P₂ : Charge) (X : H3ZornTKKLie) :
    ⁅injPlus2 1, ⁅injMinus1 P₁, injMinus1 P₂⁆⁆ +
      ⁅injMinus1 P₁, ⁅injMinus1 P₂, injPlus2 1⁆⁆ +
      ⁅injMinus1 P₂, ⁅injPlus2 1, injMinus1 P₁⁆⁆ = 0 ∧
    ⁅injZeroE7 X, ⁅injPlus1 P₁, injMinus1 P₂⁆⁆ +
      ⁅injPlus1 P₁, ⁅injMinus1 P₂, injZeroE7 X⁆⁆ +
      ⁅injMinus1 P₂, ⁅injZeroE7 X, injPlus1 P₁⁆⁆ = 0 :=
  ⟨lie_jacobi (injPlus2 1) (injMinus1 P₁) (injMinus1 P₂),
    lie_jacobi (injZeroE7 X) (injPlus1 P₁) (injMinus1 P₂)⟩

/-! ### T9: Cartan Subalgebra Self-Normalizing Instances (`E₇`, `SplitE8`, `TKK5E8`) -/

theorem t5_t9_cartan_subalgebras :
    h3zornE7Cartan.IsCartanSubalgebra ∧
    splitE8Cartan.IsCartanSubalgebra ∧
    tkk5E8Cartan.IsCartanSubalgebra ∧
    tkk5E8Cartan.normalizer = tkk5E8Cartan :=
  ⟨h3zornE7Cartan_isCartanSubalgebra, splitE8Cartan_isCartanSubalgebra,
    tkk5E8Cartan_isCartanSubalgebra, tkk5E8Cartan_self_normalizing⟩

/-! ### T10: Serre Chevalley Involutions (`e7SerreChevalleyInv`, `e8SerreChevalleyInv`) -/

theorem t5_t10_e7_chevalley_involution (i : Fin 7) (x y : LieAlgebra.e₇ ℝ) :
    e7SerreChevalleyInv (qE7H i) = -qE7H i ∧
    e7SerreChevalleyInv (qE7E i) = qE7F i ∧
    e7SerreChevalleyInv (qE7F i) = qE7E i ∧
    e7SerreChevalleyInv ⁅x, y⁆ = ⁅e7SerreChevalleyInv x, e7SerreChevalleyInv y⁆ ∧
    e7SerreChevalleyInv (e7SerreChevalleyInv x) = x :=
  ⟨e7SerreChevalleyInv_H i, e7SerreChevalleyInv_E i, e7SerreChevalleyInv_F i,
    e7SerreChevalleyInv.map_lie x y, e7SerreChevalleyInv_involutive x⟩

theorem t5_t10_e8_chevalley_involution (i : Fin 8) (x y : LieAlgebra.e₈ ℝ) :
    e8SerreChevalleyInv (qE8H i) = -qE8H i ∧
    e8SerreChevalleyInv (qE8E i) = qE8F i ∧
    e8SerreChevalleyInv (qE8F i) = qE8E i ∧
    e8SerreChevalleyInv ⁅x, y⁆ = ⁅e8SerreChevalleyInv x, e8SerreChevalleyInv y⁆ ∧
    e8SerreChevalleyInv (e8SerreChevalleyInv x) = x :=
  ⟨e8SerreChevalleyInv_H i, e8SerreChevalleyInv_E i, e8SerreChevalleyInv_F i,
    e8SerreChevalleyInv.map_lie x y, e8SerreChevalleyInv_involutive x⟩

end InfoGeometry.Tests.E7E8Tier2
