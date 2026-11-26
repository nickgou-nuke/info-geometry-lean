/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornE7RootSystem
import InfoGeometry.Algebra.H3ZornE6Simplicity
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Simplicity, `IsKilling`, and `E₇` `RootSystem` for `𝔈₇(7)` (`H3ZornTKKLie`)

Proves natively (without `sorry` or custom axioms) that the 133-dimensional split real
exceptional Lie algebra `H3ZornTKKLie` (`𝔈₇(7)`) is simple (`LieAlgebra.IsSimple`), hence
semisimple (`LieAlgebra.IsSemisimple`), has trivial radical (`LieAlgebra.HasTrivialRadical`),
no nonzero abelian ideals, trivial center, and non-degenerate Killing form
(`LieAlgebra.IsKilling`).

Constructs the Mathlib root system `h3zornE7RootSystem := LieAlgebra.IsKilling.rootSystem
h3zornE7Cartan`, establishes `IsRootSystem`, `IsCrystallographic`, `IsReduced`, and
`IsIrreducible`, constructs the exact 126-root bijection `Fin 126 ≃ h3zornE7Cartan.root`,
and builds an explicit `RootPairing.Base` whose Cartan matrix equals `CartanMatrix.E 7`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn
open InfoGeometry.Canonical.H3ZornBasis
open InfoGeometry.Canonical.H3ZornTKKLieAlgebra
open InfoGeometry.Exceptional.CFSGPort.Chevalley

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

instance instModuleFiniteH3ZornTKKLie : Module.Finite ℝ H3ZornTKKLie :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_H3ZornTKKLie]; decide)

section Simplicity

private theorem e7_cartan_transpose_mulVec_ne_zero {a : Fin 7 → ℝ}
    (ha : (∑ i : Fin 7, a i • e7SimpleH i) ≠ 0) :
    ∃ j : Fin 7, ∑ i : Fin 7, a i * (Tag.cartan .E7 i j : ℝ) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0; have h1 := hcon 1; have h2 := hcon 2; have h3 := hcon 3
  have h4 := hcon 4; have h5 := hcon 5; have h6 := hcon 6
  have hcZ : ∀ i j : Fin 7, Tag.cartan .E7 i j =
      match i.val, j.val with
      | 0, 0 => 2 | 0, 2 => -1
      | 1, 1 => 2 | 1, 3 => -1
      | 2, 0 => -1 | 2, 2 => 2 | 2, 3 => -1
      | 3, 1 => -1 | 3, 2 => -1 | 3, 3 => 2 | 3, 4 => -1
      | 4, 3 => -1 | 4, 4 => 2 | 4, 5 => -1
      | 5, 4 => -1 | 5, 5 => 2 | 5, 6 => -1
      | 6, 5 => -1 | 6, 6 => 2
      | _, _ => 0 := by
    intro i j; fin_cases i <;> fin_cases j <;> decide
  simp only [Fin.sum_univ_seven, hcZ] at h0 h1 h2 h3 h4 h5 h6
  norm_num [Fin.val] at h0 h1 h2 h3 h4 h5 h6
  have ha0 : a 0 = 0 := by linarith
  have ha1 : a 1 = 0 := by linarith
  have ha2 : a 2 = 0 := by linarith
  have ha3 : a 3 = 0 := by linarith
  have ha4 : a 4 = 0 := by linarith
  have ha5 : a 5 = 0 := by linarith
  have ha6 : a 6 = 0 := by linarith
  exact ha (Finset.sum_eq_zero fun i _ => by
    fin_cases i <;> simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6])

private theorem e6_nonzero_mem_ideal_imp_top (I : LieIdeal ℝ H3ZornTKKLie)
    (x : h3zornCubicStabilizer) (hx0 : x ≠ 0)
    (hxI : h3zornCubicStabilizerToTKK x ∈ I) : I = ⊤ := by
  let I₀ : LieIdeal ℝ h3zornCubicStabilizer :=
    { carrier := {y | h3zornCubicStabilizerToTKK y ∈ I}
      zero_mem' := by simp
      add_mem' := fun hx hy => by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact I.add_mem hx hy
      smul_mem' := fun c _ hx => by
        simp only [Set.mem_ofPred_eq, map_smul] at *
        exact I.smul_mem c hx
      lie_mem := fun {a _} hy => by
        change h3zornCubicStabilizerToTKK ⁅a, _⁆ ∈ I
        rw [LieHom.map_lie]
        exact I.lie_mem hy }
  have hI0_ne : I₀ ≠ ⊥ := by
    intro hbot
    have hxmem : x ∈ I₀ := hxI
    rw [hbot, LieSubmodule.mem_bot] at hxmem
    exact hx0 hxmem
  have hI0_top : I₀ = ⊤ :=
    (h3zornCubicStabilizer_isSimple.eq_bot_or_eq_top I₀).resolve_left hI0_ne
  have hall_e6 : ∀ y : h3zornCubicStabilizer, h3zornCubicStabilizerToTKK y ∈ I := by
    intro y
    have hy : y ∈ I₀ := hI0_top ▸ LieSubmodule.mem_top y
    exact hy
  have hH_lt6 : ∀ i : Fin 6, e7SimpleH i.castSucc ∈ I := by
    intro i
    rw [e7SimpleH_castSucc]
    exact hall_e6 (e6SimpleH i)
  have hE6 : e7SimpleE 6 ∈ I := by
    have hbr : ⁅e7SimpleH 5, e7SimpleE 6⁆ ∈ I := by
      rw [← lie_skew]
      exact I.neg_mem (I.lie_mem (hH_lt6 5))
    rw [e7Simple_bracket_HE] at hbr
    have hc : Tag.cartan .E7 (5 : Fin 7) (6 : Fin 7) = -1 := by decide
    rw [hc] at hbr
    have hbr' : (-1 : ℝ) • e7SimpleE 6 ∈ I := by simpa using hbr
    simpa using I.neg_mem hbr'
  have hH6 : e7SimpleH 6 ∈ I := by
    rw [← e7Simple_bracket_EF_same 6, ← lie_skew]
    exact I.neg_mem (I.lie_mem hE6)
  have hH_mem : ∀ i : Fin 7, e7SimpleH i ∈ I := by
    intro i
    by_cases hi : i.val < 6
    · have hi' : i = (⟨i.val, hi⟩ : Fin 6).castSucc := Fin.ext rfl
      rw [hi']; exact hH_lt6 ⟨i.val, hi⟩
    · have hi6 : i = 6 := Fin.ext (by omega)
      rw [hi6]; exact hH6
  have hgrade : h3zornTKKGradeOp ∈ I := by
    rw [h3zornTKKGradeOp_eq_linear_comb]
    refine I.add_mem (I.add_mem (I.add_mem (I.add_mem (I.add_mem (I.add_mem
      (hH_mem 0) (I.smul_mem _ (hH_mem 1))) (I.smul_mem _ (hH_mem 2)))
      (I.smul_mem _ (hH_mem 3))) (I.smul_mem _ (hH_mem 4)))
      (I.smul_mem _ (hH_mem 5))) (I.smul_mem _ (hH_mem 6))
  have hR_mem : ∀ r : Fin 126, e7RootVec r ∈ I := by
    intro r
    by_cases hr0 : r.val < 72
    · have hrv : e7RootVec r = h3zornCubicStabilizerToTKK (e6RootVec ⟨r.val, hr0⟩) := by
        simp [e7RootVec, hr0]
      rw [hrv]
      exact hall_e6 (e6RootVec ⟨r.val, hr0⟩)
    · by_cases hr1 : r.val < 99
      · have hrv : e7RootVec r = negInj (h3ZornBasis ⟨r.val - 72, by omega⟩) := by
          simp [e7RootVec, hr0, hr1]
        rw [hrv, ← h3zornTKKGradeOp_bracket_neg, ← lie_skew]
        exact I.neg_mem (I.lie_mem hgrade)
      · have hrv : e7RootVec r =
            posInj (h3ZornBasis (traceDualIdx ⟨r.val - 99, by omega⟩)) := by
          simp [e7RootVec, hr0, hr1]
        rw [hrv]
        have hbr : ⁅h3zornTKKGradeOp,
            posInj (h3ZornBasis (traceDualIdx ⟨r.val - 99, by omega⟩))⁆ ∈ I := by
          rw [← lie_skew]
          exact I.neg_mem (I.lie_mem hgrade)
        rw [h3zornTKKGradeOp_bracket_pos] at hbr
        simpa using I.neg_mem hbr
  rw [eq_top_iff]
  intro z _
  have hrep := e7ChevalleyBasis.sum_repr z
  rw [← hrep, Fintype.sum_sum_type]
  simp only [e7ChevalleyBasis_inl, e7ChevalleyBasis_inr]
  exact I.add_mem (I.sum_mem fun i _ => I.smul_mem _ (hH_mem i))
    (I.sum_mem fun r _ => I.smul_mem _ (hR_mem r))

private theorem cartan_ne_zero_mem_ideal_imp_top (I : LieIdeal ℝ H3ZornTKKLie)
    (h : H3ZornTKKLie) (hh : h ∈ h3zornE7Cartan) (hne : h ≠ 0) (hI : h ∈ I) : I = ⊤ := by
  change h ∈ Submodule.span ℝ (Set.range e7SimpleH) at hh
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hh
  obtain ⟨j, hj⟩ := e7_cartan_transpose_mulVec_ne_zero hne
  have hbr : ⁅∑ i : Fin 7, a i • e7SimpleH i, e7SimpleE j⁆ ∈ I := by
    rw [← lie_skew]
    exact I.neg_mem (I.lie_mem hI)
  have heq : ⁅∑ i : Fin 7, a i • e7SimpleH i, e7SimpleE j⁆ =
      (∑ i : Fin 7, a i * (Tag.cartan .E7 i j : ℝ)) • e7SimpleE j := by
    rw [sum_lie]
    simp only [smul_lie, e7Simple_bracket_HE, smul_smul, Finset.sum_smul]
  rw [heq] at hbr
  have hej : e7SimpleE j ∈ I := by
    have hs := I.smul_mem (∑ i : Fin 7, a i * (Tag.cartan .E7 i j : ℝ))⁻¹ hbr
    rw [smul_smul, inv_mul_cancel₀ hj, one_smul] at hs
    exact hs
  by_cases hj6 : j.val < 6
  · have hj' : j = (⟨j.val, hj6⟩ : Fin 6).castSucc := Fin.ext rfl
    rw [hj', e7SimpleE_castSucc] at hej
    have hne6 : e6SimpleE ⟨j.val, hj6⟩ ≠ 0 := by
      rw [show e6SimpleE ⟨j.val, hj6⟩ = e6RootVec (eSimpleIdx ⟨j.val, hj6⟩) from rfl]
      exact e6RootVec_ne_zero _
    exact e6_nonzero_mem_ideal_imp_top I _ hne6 hej
  · have hj_eq : j = 6 := Fin.ext (by omega)
    rw [hj_eq] at hej
    have hh6 : e7SimpleH 6 ∈ I := by
      rw [← e7Simple_bracket_EF_same 6, ← lie_skew]
      exact I.neg_mem (I.lie_mem hej)
    have he5 : e7SimpleE 5 ∈ I := by
      have hbr5 : ⁅e7SimpleH 6, e7SimpleE 5⁆ ∈ I := by
        rw [← lie_skew]
        exact I.neg_mem (I.lie_mem hh6)
      rw [e7Simple_bracket_HE] at hbr5
      have hc : Tag.cartan .E7 (6 : Fin 7) (5 : Fin 7) = -1 := by decide
      rw [hc] at hbr5
      have hbr5' : (-1 : ℝ) • e7SimpleE 5 ∈ I := by simpa using hbr5
      simpa using I.neg_mem hbr5'
    have he5' : h3zornCubicStabilizerToTKK (e6SimpleE 5) ∈ I := by
      rwa [← e7SimpleE_castSucc 5]
    have hne5 : e6SimpleE (5 : Fin 6) ≠ 0 := by
      rw [show e6SimpleE (5 : Fin 6) = e6RootVec (eSimpleIdx 5) from rfl]
      exact e6RootVec_ne_zero _
    exact e6_nonzero_mem_ideal_imp_top I _ hne5 he5'

/-- **Unconditional Simplicity of Split `𝔈₇(7)`**:
`H3ZornTKKLie` is a simple 133-dimensional real Lie algebra. -/
instance h3zornTKKLie_isSimple : LieAlgebra.IsSimple ℝ H3ZornTKKLie where
  eq_bot_or_eq_top I := by
    by_cases hbot : I = ⊥
    · exact Or.inl hbot
    · right
      have hne : ∃ x ∈ I, x ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hbot
        rw [eq_bot_iff]
        intro x hx
        exact hall x hx
      obtain ⟨x, hxI, hxne⟩ := hne
      have hrep := e7ChevalleyBasis.sum_repr x
      rw [Fintype.sum_sum_type] at hrep
      simp only [e7ChevalleyBasis_inl, e7ChevalleyBasis_inr] at hrep
      have hhpart : (∑ i : Fin 7, e7ChevalleyBasis.repr x (Sum.inl i) • e7SimpleH i) ∈
          h3zornE7Cartan :=
        Submodule.sum_mem _ fun i _ => h3zornE7Cartan.smul_mem _ (e7SimpleH_mem_h3zornE7Cartan i)
      have hkill := e7_cartan_weight_kill_mem I.toSubmodule (fun i y hy => I.lie_mem hy)
        Finset.univ (∑ i : Fin 7, e7ChevalleyBasis.repr x (Sum.inl i) • e7SimpleH i) hhpart
        (fun r => e7ChevalleyBasis.repr x (Sum.inr r)) (by rw [hrep]; exact hxI)
      by_cases hhp0 : (∑ i : Fin 7, e7ChevalleyBasis.repr x (Sum.inl i) • e7SimpleH i) = 0
      · have hex : ∃ r : Fin 126, e7ChevalleyBasis.repr x (Sum.inr r) ≠ 0 := by
          by_contra hall
          push Not at hall
          have hs0 : (∑ r : Fin 126, e7ChevalleyBasis.repr x (Sum.inr r) • e7RootVec r) = 0 :=
            Finset.sum_eq_zero fun r _ => by rw [hall r, zero_smul]
          apply hxne
          rw [← hrep, hhp0, hs0, add_zero]
        obtain ⟨r, hr⟩ := hex
        have hrI : e7RootVec r ∈ I := by
          have hs := I.smul_mem (e7ChevalleyBasis.repr x (Sum.inr r))⁻¹
            (hkill.2 r (Finset.mem_univ r))
          rw [smul_smul, inv_mul_cancel₀ hr, one_smul] at hs
          exact hs
        by_cases hr0 : r.val < 72
        · have hrv : e7RootVec r = h3zornCubicStabilizerToTKK (e6RootVec ⟨r.val, hr0⟩) := by
            simp [e7RootVec, hr0]
          rw [hrv] at hrI
          exact e6_nonzero_mem_ideal_imp_top I _ (e6RootVec_ne_zero _) hrI
        · by_cases hr1 : r.val < 99
          · let k : Fin 27 := ⟨r.val - 72, by omega⟩
            have hrv : e7RootVec r = negInj (h3ZornBasis k) := by
              simp [e7RootVec, hr0, hr1, k]
            rw [hrv] at hrI
            have hmemI : ⁅negInj (h3ZornBasis k),
                posInj (h3ZornBasis (traceDualIdx k))⁆ ∈ I := by
              rw [← lie_skew]
              exact I.neg_mem (I.lie_mem hrI)
            exact cartan_ne_zero_mem_ideal_imp_top I _
              (negInj_bracket_posInj_traceDual_mem_cartan k)
              (negInj_bracket_posInj_traceDual_ne_zero k) hmemI
          · let k : Fin 27 := ⟨r.val - 99, by omega⟩
            have hrv : e7RootVec r = posInj (h3ZornBasis (traceDualIdx k)) := by
              simp [e7RootVec, hr0, hr1, k]
            rw [hrv] at hrI
            have hmemI : ⁅negInj (h3ZornBasis k),
                posInj (h3ZornBasis (traceDualIdx k))⁆ ∈ I := I.lie_mem hrI
            exact cartan_ne_zero_mem_ideal_imp_top I _
              (negInj_bracket_posInj_traceDual_mem_cartan k)
              (negInj_bracket_posInj_traceDual_ne_zero k) hmemI
      · exact cartan_ne_zero_mem_ideal_imp_top I _ hhpart hhp0 hkill.1
  non_abelian := by
    intro hab
    exact h3zornE7_noncomm_witness (hab.trivial (e7SimpleH 0) (e7SimpleE 0))

instance h3zornTKKLie_isSemisimple : LieAlgebra.IsSemisimple ℝ H3ZornTKKLie :=
  inferInstance

instance h3zornTKKLie_hasTrivialRadical : LieAlgebra.HasTrivialRadical ℝ H3ZornTKKLie :=
  inferInstance

theorem h3zornTKKLie_no_abelian_ideal (I : LieIdeal ℝ H3ZornTKKLie)
    [IsLieAbelian I] : I = ⊥ :=
  (LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals ℝ H3ZornTKKLie).mp
    h3zornTKKLie_hasTrivialRadical I inferInstance

instance h3zornTKKLie_isKilling : LieAlgebra.IsKilling ℝ H3ZornTKKLie := by
  have : IsNoetherian ℝ H3ZornTKKLie := (IsNoetherian.iff_fg).2 inferInstance
  exact inferInstance

theorem center_h3zornTKKLie_eq_bot : LieAlgebra.center ℝ H3ZornTKKLie = ⊥ :=
  le_antisymm (LieAlgebra.center_le_radical ℝ H3ZornTKKLie |>.trans (by simp)) bot_le

theorem h3zornTKKLie_killingForm_nondegenerate :
    (killingForm ℝ H3ZornTKKLie).Nondegenerate :=
  LieAlgebra.IsKilling.killingForm_nondegenerate ℝ H3ZornTKKLie

end Simplicity

section E7RootSystem

/-- The Mathlib `RootPairing` of split `𝔈₇(7)` (`H3ZornTKKLie`) relative to `h3zornE7Cartan`. -/
noncomputable def h3zornE7RootSystem :
    RootPairing h3zornE7Cartan.root ℝ (Module.Dual ℝ h3zornE7Cartan) h3zornE7Cartan :=
  LieAlgebra.IsKilling.rootSystem h3zornE7Cartan

instance h3zornE7RootSystem_isRootSystem : h3zornE7RootSystem.IsRootSystem :=
  show (LieAlgebra.IsKilling.rootSystem h3zornE7Cartan).IsRootSystem from inferInstance

instance h3zornE7RootSystem_isCrystallographic : h3zornE7RootSystem.IsCrystallographic :=
  show (LieAlgebra.IsKilling.rootSystem h3zornE7Cartan).IsCrystallographic from inferInstance

instance h3zornE7RootSystem_isReduced : h3zornE7RootSystem.IsReduced :=
  show (LieAlgebra.IsKilling.rootSystem h3zornE7Cartan).IsReduced from inferInstance

instance h3zornE7RootSystem_isIrreducible : h3zornE7RootSystem.IsIrreducible :=
  LieAlgebra.IsKilling.isSimple_iff_isIrreducible.mpr h3zornTKKLie_isSimple

/-- Package the `r`-th root weight `h3zornE7RootWeight r` as a Mathlib `LieModule.Weight`. -/
def e7MathlibWeight (r : Fin 126) :
    LieModule.Weight ℝ h3zornE7Cartan H3ZornTKKLie where
  toFun := h3zornE7RootWeight r
  genWeightSpace_ne_bot' := e7RootSpace_ne_bot r

/-- Package the `r`-th root weight as a nonzero root in `h3zornE7Cartan.root`. -/
def e7MathlibRoot (r : Fin 126) : h3zornE7Cartan.root :=
  ⟨e7MathlibWeight r, by
    simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h0
    apply h3zornE7RootWeight_ne_zero r
    ext H
    exact congrFun h0 H⟩

theorem e7MathlibRoot_injective : Function.Injective e7MathlibRoot := by
  intro r₁ r₂ h
  apply h3zornE7RootWeight_injective
  ext H
  exact congrFun (congrArg (fun x : h3zornE7Cartan.root => (x.1 : h3zornE7Cartan → ℝ)) h) H

theorem e7MathlibRoot_surjective : Function.Surjective e7MathlibRoot := by
  intro α
  let S : Set (h3zornE7Cartan → ℝ) :=
    insert 0 (Set.range (fun r : Fin 126 => (h3zornE7RootWeight r : h3zornE7Cartan → ℝ)))
  have hs : (⨆ ψ ∈ S, LieAlgebra.rootSpace h3zornE7Cartan ψ) = ⊤ := by
    rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule]
    simp only [LieSubmodule.iSup_toSubmodule]
    apply (Submodule.eq_top_iff_forall_basis_mem e7ChevalleyBasis).mpr
    rintro (i | r)
    · apply Submodule.mem_iSup_of_mem (0 : h3zornE7Cartan → ℝ)
      apply Submodule.mem_iSup_of_mem (Set.mem_insert 0 _)
      rw [e7ChevalleyBasis_inl]
      exact LieAlgebra.toLieSubmodule_le_rootSpace_zero ℝ H3ZornTKKLie h3zornE7Cartan
        (e7SimpleH_mem_h3zornE7Cartan i)
    · apply Submodule.mem_iSup_of_mem (h3zornE7RootWeight r : h3zornE7Cartan → ℝ)
      apply Submodule.mem_iSup_of_mem (Set.mem_insert_of_mem 0 (Set.mem_range_self r))
      rw [e7ChevalleyBasis_inr]
      exact e7RootVec_mem_rootSpace r
  have hmem : (α.1 : h3zornE7Cartan → ℝ) ∈ S :=
    (LieModule.iSupIndep_genWeightSpace ℝ h3zornE7Cartan H3ZornTKKLie).mem_of_biSup_eq_top
      hs α.1.genWeightSpace_ne_bot
  rcases hmem with h0 | ⟨r, hr⟩
  · exfalso
    exact (LieSubalgebra.isNonZero_coe_root α) h0
  · refine ⟨r, ?_⟩
    apply Subtype.ext
    ext H
    exact congrFun hr H

/-- Explicit bijection `Fin 126 ≃ h3zornE7Cartan.root`. -/
noncomputable def e7MathlibRootEquiv : Fin 126 ≃ h3zornE7Cartan.root :=
  Equiv.ofBijective e7MathlibRoot ⟨e7MathlibRoot_injective, e7MathlibRoot_surjective⟩

/-- Canonical bijection between `CFSGPort` `E₇` roots and Mathlib `h3zornE7Cartan.root`. -/
noncomputable def e7RootSystemEquiv :
    {v : Fin 7 → ℤ // IsRoot .E7 v} ≃ h3zornE7Cartan.root :=
  e7RootEquiv.symm.trans e7MathlibRootEquiv

theorem card_h3zornE7Cartan_root : Fintype.card h3zornE7Cartan.root = 126 := by
  rw [← Fintype.card_fin 126]
  exact (Fintype.card_congr e7MathlibRootEquiv).symm

theorem h3zornE7Cartan_root_card : h3zornE7Cartan.root.card = 126 := by
  rw [← Fintype.card_coe h3zornE7Cartan.root]
  exact card_h3zornE7Cartan_root

theorem h3zornE7_cartan_eq_mathlib :
    Tag.cartan .E7 = CartanMatrix.E 7 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem e7RootEigenvalue_simpleE (i j : Fin 7) :
    e7RootEigenvalue i (e7ESimpleIdx j) = Tag.cartan .E7 i j := by
  have hchk : (List.finRange 7).all (fun i => (List.finRange 7).all (fun j =>
      e7RootEigenvalue i (e7ESimpleIdx j) == Tag.cartan .E7 i j)) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact hchk i j

private theorem e7RootCoord_fSimple (i : Fin 7) :
    e7RootCoord (e7FSimpleIdx i) = -e7RootCoord (e7ESimpleIdx i) := by
  have hchk : (List.finRange 7).all (fun i =>
      List.ofFn (e7RootCoord (e7FSimpleIdx i)) ==
        List.ofFn (-e7RootCoord (e7ESimpleIdx i))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hchk
  exact List.ofFn_injective (hchk i)

private theorem e7RootCoord_sign_uniform (r : Fin 126) :
    (∀ i : Fin 7, 0 ≤ e7RootCoord r i) ∨ (∀ i : Fin 7, e7RootCoord r i ≤ 0) := by
  have hchk : (List.finRange 126).all (fun r =>
      (List.finRange 7).all (fun i => decide (0 ≤ e7RootCoord r i)) ||
      (List.finRange 7).all (fun i => decide (e7RootCoord r i ≤ 0))) = true := by
    decide
  simp only [List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    decide_eq_true_eq] at hchk
  exact hchk r

private theorem h3zornE7RootWeight_eq_sum_simple (r : Fin 126) :
    h3zornE7RootWeight r =
      ∑ j : Fin 7, (e7RootCoord r j : ℝ) • h3zornE7RootWeight (e7ESimpleIdx j) := by
  apply e7CartanBasis.ext
  intro i
  rw [LinearMap.sum_apply]
  have he7 : (e7CartanBasis i : h3zornE7Cartan) =
      ⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩ :=
    Subtype.ext (e7CartanBasis_apply i)
  rw [he7, h3zornE7RootWeight_simpleH]
  simp_rw [LinearMap.smul_apply, smul_eq_mul, h3zornE7RootWeight_simpleH, e7RootEigenvalue_simpleE]
  rw [e7RootEigenvalue]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The 7 simple roots in `h3zornE7Cartan.root`. -/
def e7SimpleMathlibRoot (i : Fin 7) : h3zornE7Cartan.root :=
  e7MathlibRoot (e7ESimpleIdx i)

private theorem e7ESimpleIdx_injective : Function.Injective e7ESimpleIdx := by
  intro i j h
  have heq := congrArg (e7RootCoord ·) h
  have hi : e7RootCoord (e7ESimpleIdx i) i = 1 := by
    fin_cases i <;> decide
  have hj : ∀ a b : Fin 7, a ≠ b → e7RootCoord (e7ESimpleIdx a) b = 0 := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | contradiction | decide
  by_contra hne
  have h1 := congrFun heq i
  rw [hi, hj j i (Ne.symm hne)] at h1
  omega

private theorem e7SimpleMathlibRoot_injective : Function.Injective e7SimpleMathlibRoot :=
  e7MathlibRoot_injective.comp e7ESimpleIdx_injective

private theorem e7SimpleMathlibRoot_linearIndepOn :
    LinearIndepOn ℝ h3zornE7RootSystem.root (Set.range e7SimpleMathlibRoot) := by
  classical
  rw [linearIndepOn_iff'']
  intro s c hs_sub hsupp hsum i hi
  have hc0 : ∀ x : h3zornE7Cartan.root, x ∈ Set.range e7SimpleMathlibRoot → c x = 0 := by
    let a : Fin 7 → ℝ := fun j =>
      if e7SimpleMathlibRoot j ∈ s then c (e7SimpleMathlibRoot j) else 0
    have hsum7 : ∑ j : Fin 7, a j • h3zornE7RootWeight (e7ESimpleIdx j) = 0 := by
      have hconv : ∑ x ∈ s, c x • h3zornE7RootSystem.root x =
          ∑ x ∈ Finset.image e7SimpleMathlibRoot Finset.univ,
            (if x ∈ s then c x else 0) • h3zornE7RootSystem.root x := by
        simp_rw [ite_smul, zero_smul]
        rw [← Finset.sum_filter]
        refine Finset.sum_congr (by
          ext x
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨fun hx => ⟨hs_sub hx, hx⟩, fun h => h.2⟩) fun x _ => rfl
      rw [hconv, Finset.sum_image (fun x _ y _ hxy => e7SimpleMathlibRoot_injective hxy)] at hsum
      exact hsum
    have hzero : ∀ j : Fin 7, a j = 0 := by
      have hev : ∀ k : Fin 7, ∑ j : Fin 7, a j * (Tag.cartan .E7 j k : ℝ) = 0 := by
        intro k
        have hk := congrArg (fun f : Module.Dual ℝ h3zornE7Cartan =>
          f ⟨e7SimpleH k, e7SimpleH_mem_h3zornE7Cartan k⟩) hsum7
        rw [LinearMap.sum_apply, LinearMap.zero_apply] at hk
        simp only [LinearMap.smul_apply, smul_eq_mul, h3zornE7RootWeight_simpleH,
          e7RootEigenvalue_simpleE] at hk
        have hsymm : ∀ j : Fin 7, Tag.cartan .E7 k j = Tag.cartan .E7 j k := by
          intro j; fin_cases k <;> fin_cases j <;> decide
        simpa [hsymm] using hk
      have hne0 : (∑ j : Fin 7, a j • e7SimpleH j) = 0 := by
        by_contra hcon
        obtain ⟨k, hk⟩ := e7_cartan_transpose_mulVec_ne_zero hcon
        exact hk (hev k)
      exact Fintype.linearIndependent_iff.mp e7SimpleH_linearIndependent a hne0
    intro x hx
    rcases hx with ⟨j, rfl⟩
    by_cases hjs : e7SimpleMathlibRoot j ∈ s
    · have hj0 := hzero j
      simpa [a, hjs] using hj0
    · exact hsupp (e7SimpleMathlibRoot j) hjs
  exact hc0 i (hs_sub hi)

private theorem e7SimpleMathlibRoot_mem_or_neg_mem (α : h3zornE7Cartan.root) :
    h3zornE7RootSystem.root α ∈
        AddSubmonoid.closure (h3zornE7RootSystem.root '' Set.range e7SimpleMathlibRoot) ∨
      -h3zornE7RootSystem.root α ∈
        AddSubmonoid.closure (h3zornE7RootSystem.root '' Set.range e7SimpleMathlibRoot) := by
  obtain ⟨r, hr⟩ := e7MathlibRoot_surjective α
  have hwt : h3zornE7RootSystem.root α = h3zornE7RootWeight r := by
    rw [← hr]
    rfl
  rw [hwt, h3zornE7RootWeight_eq_sum_simple r]
  have hmem_gen : ∀ j : Fin 7, h3zornE7RootWeight (e7ESimpleIdx j) ∈
      AddSubmonoid.closure (h3zornE7RootSystem.root '' Set.range e7SimpleMathlibRoot) := by
    intro j
    apply AddSubmonoid.subset_closure
    exact ⟨e7SimpleMathlibRoot j, ⟨j, rfl⟩, rfl⟩
  rcases e7RootCoord_sign_uniform r with hpos | hneg
  · left
    have hns : (∑ j : Fin 7, (e7RootCoord r j : ℝ) • h3zornE7RootWeight (e7ESimpleIdx j)) =
        ∑ j : Fin 7, (e7RootCoord r j).toNat • h3zornE7RootWeight (e7ESimpleIdx j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      congr 1
      exact_mod_cast (Int.toNat_of_nonneg (hpos j)).symm
    rw [hns]
    exact AddSubmonoid.sum_mem _ fun j _ => AddSubmonoid.nsmul_mem _ (hmem_gen j) _
  · right
    have hns : -(∑ j : Fin 7, (e7RootCoord r j : ℝ) • h3zornE7RootWeight (e7ESimpleIdx j)) =
        ∑ j : Fin 7, (-e7RootCoord r j).toNat • h3zornE7RootWeight (e7ESimpleIdx j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h0 : 0 ≤ -e7RootCoord r j := neg_nonneg.mpr (hneg j)
      rw [← Nat.cast_smul_eq_nsmul ℝ, ← Int.cast_natCast, Int.toNat_of_nonneg h0,
        Int.cast_neg, neg_smul]
    rw [hns]
    exact AddSubmonoid.sum_mem _ fun j _ => AddSubmonoid.nsmul_mem _ (hmem_gen j) _

/-- Explicit `RootPairing.Base` for `h3zornE7RootSystem` supported on the 7 simple roots. -/
noncomputable def h3zornE7RootSystemBase : h3zornE7RootSystem.Base :=
  RootPairing.Base.mk' h3zornE7RootSystem (Set.range e7SimpleMathlibRoot)
    e7SimpleMathlibRoot_linearIndepOn e7SimpleMathlibRoot_mem_or_neg_mem

/-- Bijection between `Fin 7` and `h3zornE7RootSystemBase.support`. -/
noncomputable def h3zornE7BaseSupportEquiv : Fin 7 ≃ h3zornE7RootSystemBase.support :=
  Equiv.ofBijective
    (fun i => ⟨e7SimpleMathlibRoot i, by
      change e7SimpleMathlibRoot i ∈ (Set.toFinite (Set.range e7SimpleMathlibRoot)).toFinset
      rw [Set.Finite.mem_toFinset]
      exact ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => e7SimpleMathlibRoot_injective (congrArg Subtype.val h),
     fun ⟨α, hα⟩ => by
       change α ∈ (Set.toFinite (Set.range e7SimpleMathlibRoot)).toFinset at hα
       rw [Set.Finite.mem_toFinset] at hα
       rcases hα with ⟨i, rfl⟩
       exact ⟨i, rfl⟩⟩

theorem e7Simple_isSl2Triple (i : Fin 7) :
    IsSl2Triple (e7SimpleH i) (e7SimpleE i) (e7SimpleF i) where
  h_ne_zero := by
    intro h0
    have hc := Fintype.linearIndependent_iff.mp e7SimpleH_linearIndependent
      (fun j => if j = i then 1 else 0) (by simp [h0]) i
    norm_num at hc
  lie_e_f := e7Simple_bracket_EF_same i
  lie_h_e_nsmul := by
    rw [e7Simple_bracket_HE]
    have hc : Tag.cartan .E7 i i = 2 := by fin_cases i <;> decide
    rw [hc, ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  lie_h_f_nsmul := by
    rw [e7Simple_bracket_HF]
    have hc : Tag.cartan .E7 i i = 2 := by fin_cases i <;> decide
    rw [hc, ← Nat.cast_smul_eq_nsmul ℝ, ← neg_smul]
    norm_num

private theorem e7SimpleE_mem_rootSpace (i : Fin 7) :
    e7SimpleE i ∈ LieAlgebra.rootSpace h3zornE7Cartan (e7SimpleMathlibRoot i).1 := by
  rw [e7SimpleE_eq_rootVec]
  exact e7RootVec_mem_rootSpace (e7ESimpleIdx i)

private theorem e7SimpleF_mem_neg_rootSpace (i : Fin 7) :
    e7SimpleF i ∈ LieAlgebra.rootSpace h3zornE7Cartan (-(e7SimpleMathlibRoot i).1) := by
  rw [LieAlgebra.rootSpace, LieModule.mem_genWeightSpace]
  intro H
  refine ⟨1, ?_⟩
  rw [pow_one]
  change ⁅(H : H3ZornTKKLie), e7SimpleF i⁆ - (-(e7SimpleMathlibRoot i).1) H • e7SimpleF i = 0
  rw [e7SimpleF_eq_rootVec, lie_smul, e7RootVec_bracket_cartan H (e7FSimpleIdx i), smul_smul]
  have hwt : h3zornE7RootWeight (e7FSimpleIdx i) H = -((e7SimpleMathlibRoot i).1 H) := by
    have hrep := e7CartanBasis.sum_repr H
    conv_lhs => rw [← hrep]
    conv_rhs => rw [← hrep]
    simp only [map_sum, map_smul, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : h3zornE7RootWeight (e7FSimpleIdx i) (e7CartanBasis j) =
        -((e7SimpleMathlibRoot i).1 (e7CartanBasis j)) := by
      have he7 : (e7CartanBasis j : h3zornE7Cartan) =
          ⟨e7SimpleH j, e7SimpleH_mem_h3zornE7Cartan j⟩ :=
        Subtype.ext (e7CartanBasis_apply j)
      rw [he7]
      change h3zornE7RootWeight (e7FSimpleIdx i) ⟨e7SimpleH j, e7SimpleH_mem_h3zornE7Cartan j⟩ =
        -h3zornE7RootWeight (e7ESimpleIdx i) ⟨e7SimpleH j, e7SimpleH_mem_h3zornE7Cartan j⟩
      rw [h3zornE7RootWeight_simpleH, h3zornE7RootWeight_simpleH]
      simp only [e7RootEigenvalue, e7RootCoord_fSimple, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib, Int.cast_neg]
    rw [hj]
    ring
  have hneg_app : (-(e7SimpleMathlibRoot i).1) H = -((e7SimpleMathlibRoot i).1 H) := rfl
  rw [hwt, hneg_app, smul_smul, mul_comm, sub_self]

theorem e7Simple_coroot_eq (i : Fin 7) :
    (LieAlgebra.IsKilling.coroot (e7SimpleMathlibRoot i).1 : H3ZornTKKLie) = e7SimpleH i :=
  ((e7Simple_isSl2Triple i).h_eq_coroot
    (LieSubalgebra.isNonZero_coe_root (e7SimpleMathlibRoot i))
    (e7SimpleE_mem_rootSpace i) (e7SimpleF_mem_neg_rootSpace i)).symm

theorem e7Simple_coroot_subtype_eq (i : Fin 7) :
    LieAlgebra.IsKilling.coroot (e7SimpleMathlibRoot i).1 =
      ⟨e7SimpleH i, e7SimpleH_mem_h3zornE7Cartan i⟩ :=
  Subtype.ext (e7Simple_coroot_eq i)

theorem h3zornE7RootSystem_pairing_simple (i j : Fin 7) :
    h3zornE7RootSystem.pairing (e7SimpleMathlibRoot i) (e7SimpleMathlibRoot j) =
      (CartanMatrix.E 7 i j : ℝ) := by
  change (LieAlgebra.IsKilling.rootSystem h3zornE7Cartan).pairing
    (e7SimpleMathlibRoot i) (e7SimpleMathlibRoot j) = (CartanMatrix.E 7 i j : ℝ)
  rw [LieAlgebra.IsKilling.rootSystem_pairing_apply, e7Simple_coroot_subtype_eq j]
  change h3zornE7RootWeight (e7ESimpleIdx i) ⟨e7SimpleH j, e7SimpleH_mem_h3zornE7Cartan j⟩ =
    (CartanMatrix.E 7 i j : ℝ)
  rw [h3zornE7RootWeight_simpleH, e7RootEigenvalue_simpleE, h3zornE7_cartan_eq_mathlib]
  have hsymm : CartanMatrix.E 7 j i = CartanMatrix.E 7 i j := by
    have ht := congrFun (congrFun (CartanMatrix.E_transpose 7) i) j
    simpa [Matrix.transpose_apply] using ht
  rw [hsymm]

theorem h3zornE7RootSystemBase_cartanMatrix_eq :
    h3zornE7RootSystemBase.cartanMatrix.reindex
      h3zornE7BaseSupportEquiv.symm h3zornE7BaseSupportEquiv.symm = CartanMatrix.E 7 := by
  ext i j
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  change h3zornE7RootSystem.pairing (h3zornE7BaseSupportEquiv i : h3zornE7Cartan.root)
    (h3zornE7BaseSupportEquiv j : h3zornE7Cartan.root) = algebraMap ℤ ℝ (CartanMatrix.E 7 i j)
  change h3zornE7RootSystem.pairing (e7SimpleMathlibRoot i) (e7SimpleMathlibRoot j) =
    (CartanMatrix.E 7 i j : ℝ)
  exact h3zornE7RootSystem_pairing_simple i j

end E7RootSystem

end InfoGeometry.Algebra
