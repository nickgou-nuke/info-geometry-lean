/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.GrassmannProductQuotientAndMasterAtlas
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Grassmann Subspace Shadows, Exterior Polynomial Resultant, Normal Subspaces & Hadamard Inequality

Wave IV Module 1 formalization of the remaining mathematical sub-claims across Editorial Notes
1–70 and Seligman's Notes in `hmath019-endmatter.pdf`:

1. **`GA₂₄` (`Editorial Note 29, Theorems 1–5, pp. 338–339`)**:
   - Theorem 1 (`note29_thm1_regressive_blades_decomposable`): regressive product of two blades of
     combined order `> n` is again decomposable.
   - Theorem 2 (`note29_thm2_hodge_blade_decomposable_and_support`): the Hodge supplement of a
     decomposable `m`-blade is a decomposable `(n - m)`-blade whose `bladeSupport` is the exact
     `extInner b`-orthogonal complement `(span v)ᗮ`.
   - Theorem 3 (`note29_thm3_exists_regressive_quotient_blade`): converse of `No. 79B` — whenever
     `span v ≤ span w`, there exists a blade `C` with `regressive b B C = A`.
   - Theorems 4–5 (`note29_thm4_thm5_hodge_subordination_and_incidence`): Hodge supplement reverses
     subspace inclusion (`span v ≤ span w ↔ bladeSupport (★B) ≤ bladeSupport (★A)`) and preserves
     incidence.
2. **`GA₂₅` (`Editorial Note 39, pp. 345–346`)**:
   Exact sign-cancellation laws equating Grassmann's 1862 (`A₂`) progressive and regressive shadows
   with his 1844 (`A₁`) conventions (`note39_progressive_shadow_sign_cancellation`,
   `note39_regressive_shadow_sign_cancellation`).
3. **`GA₂₆` (`Editorial Note 44, p. 347`)**:
   Rank-deficient / underdetermined exterior Cramer affine solution parameterization
   (`note44_underdetermined_exterior_cramer`).
4. **`GA₂₇` (`Grassmann No. 136`, `Editorial Note 9 pp. 332–333`, `Seligman p. 395`)**:
   Exterior product of `(m + n)` shifted Sylvester polynomial vectors equals
   `Polynomial.resultant f g m n • volume` over any `[CommRing R]`, together with coprimality and
   common-root vanishing criteria over fields (`grassmann_no136_exterior_resultant`,
   `grassmann_no136_exterior_resultant_eq_zero_iff`).
5. **`GA₂₈` (`Editorial Notes 49, 52, 53, pp. 350–353`, `Nos. 149, 152`)**:
   Unit factor inner-product cancellation (`note49_extInner_unit_factor_cancel`), equivalence
   between complete normality and supplement containment (`notes52_53_completely_normal_theorems`),
   and the `ℝ³` `[countermodel_found]` separating `No. 152` normality from complete normality
   (`notes52_53_normal_not_completely_normal_dim3`).
6. **`GA₂₉` (`Editorial Note 62, pp. 354–355`)**:
   Uniqueness of complete orthonormal systems preserving the supplement (`hodge a = hodge e`
   when `e.det a = 1`, `note62_hodge_eq_iff_orthonormal`).
7. **`GA₃₁` (`Editorial Note 69, pp. 358–359`)**:
   Constructive orthonormal subspace basis adaptation and Grassmann's exterior Hadamard inequality
   `‖v₁ ∧ ⋯ ∧ v_m‖² ≤ ∏ ‖v_i‖²` with equality-iff-pairwise-orthogonality
   (`note69_exterior_hadamard_inequality`).
8. **`GA₃₀` (`Editorial Notes 68 & 70, pp. 357–359`)**:
   Adapted oriented orthonormal basis extension preserving `hodge`, `regressive`, and `extInner`,
   and the unequal-order normal shadow cosine equality `cos² ∠AA' = cos² ∠B'B` plus
   `‖A * ★B‖² ≤ ‖A‖² ‖B‖²` (`notes68_70_unequal_grade_normal_shadow_angles`).
-/

noncomputable section

namespace InfoGeometry.Projective.GrassmannSubspaceShadowsResultantAndHadamard

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.ExteriorBladeIncidence
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
open InfoGeometry.Canonical.GrassmannPfaffianDarbouxAlgebra
open InfoGeometry.Canonical.GrassmannPfaffianSyzygyAndNormalForms
open InfoGeometry.Canonical.GrassmannProductQuotientAndMasterAtlas
open scoped Matrix Polynomial

/-- Closed non-commutativity witness inherited directly from `exterior_clifford_noncommutative_witness`. -/
theorem grassmann_wave4_mod1_noncommutative_witness :
    ¬ Commute
      (ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 0))
      (ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 1)) :=
  exterior_clifford_noncommutative_witness

/-! ## Shared Helpers -/

theorem toDualEquiv_eq_extInner_pub {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (b : Module.Basis (Fin n) K V) (u v : V) :
    (b.toDualEquiv u) v = extInner b (ExteriorAlgebra.ι K u) (ExteriorAlgebra.ι K v) := by
  have h1_eval : extInner b 1 (1 : ExteriorAlgebra K V) = 1 := by
    calc
      extInner b 1 (1 : ExteriorAlgebra K V) =
          extInner b (b.ExteriorAlgebra ∅) (b.ExteriorAlgebra ∅) := by
            simp only [basis_empty]
      _ = 1 := by rw [extInner_basis, ite_eq_left rfl]
  have h := extInner_ι_mul_left b u 1 (ExteriorAlgebra.ι K v)
  rw [mul_one, CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one,
    extInner_smul_right, h1_eval, mul_one] at h
  exact h.symm

private theorem ιMulti_rescale_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : ℕ} (hm : 0 < m) (c : K) (z : Fin m → V) :
    ExteriorAlgebra.ιMulti K m (Function.update z ⟨0, hm⟩ (c • z ⟨0, hm⟩)) =
      c • ExteriorAlgebra.ιMulti K m z := by
  rw [(ExteriorAlgebra.ιMulti K m).map_update_smul, Function.update_eq_self]

private theorem ιMulti_fin_append_congr' {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {r s m : ℕ} (hrs : r + s = m) (v : Fin r → V) (w : Fin s → V) :
    ExteriorAlgebra.ιMulti K m ((Fin.append v w) ∘ (finCongr hrs).symm) =
      ExteriorAlgebra.ιMulti K r v * ExteriorAlgebra.ιMulti K s w := by
  subst hrs
  have hcomp : ((Fin.append v w) ∘ (finCongr rfl).symm) = Fin.append v w := rfl
  rw [hcomp, ExteriorAlgebra.ιMulti_mul_ιMulti]

private theorem disjoint_compl_right_sub {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Finset α} (h : s ⊆ t) : Disjoint s tᶜ :=
  Finset.disjoint_left.mpr fun _ hx hxc => Finset.mem_compl.mp hxc (h hx)

private theorem disjoint_compl_left_sub {α : Type*} [Fintype α] [DecidableEq α]
    {s t : Finset α} (h : s ⊆ t) : Disjoint tᶜ s :=
  (disjoint_compl_right_sub h).symm

private theorem exteriorAlgebra_basis_ofCard {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {n m : ℕ} (f : Module.Basis (Fin n) K M) {s : Finset (Fin n)} (hs : s.card = m) :
    ExteriorAlgebra.ιMulti K m
        (fun i => f (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hs) i)) =
      f.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply_ofCard f hs]
  rfl

private theorem regressive_sum_right {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) {ι : Type*} (s : Finset ι)
    (a : ExteriorAlgebra K V) (f : ι → ExteriorAlgebra K V) :
    regressive b a (∑ i ∈ s, f i) = ∑ i ∈ s, regressive b a (f i) := by
  apply (hodge b).injective
  simp only [hodge_regressive, map_sum, Finset.mul_sum]

private theorem regressive_sum_left {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) {ι : Type*} (s : Finset ι)
    (f : ι → ExteriorAlgebra K V) (c : ExteriorAlgebra K V) :
    regressive b (∑ i ∈ s, f i) c = ∑ i ∈ s, regressive b (f i) c := by
  apply (hodge b).injective
  simp only [hodge_regressive, map_sum, Finset.sum_mul]

theorem volCoord_eq_zero_of_mem_exteriorPower_lt {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {n k : ℕ} (b : Module.Basis (Fin n) K V) (hk : k < n)
    {z : ExteriorAlgebra K V} (hz : z ∈ ⋀[K]^k V) :
    volCoord b z = 0 := by
  let z' : ⋀[K]^k V := ⟨z, hz⟩
  have hval := congrArg Subtype.val ((b.exteriorPower k).sum_repr z').symm
  change z = ((Submodule.subtype (⋀[K]^k V)) _) at hval
  rw [map_sum] at hval
  have hsum : z = ∑ s : Set.powersetCard (Fin n) k,
      (b.exteriorPower k).repr z' s • b.ExteriorAlgebra s.val := by
    refine hval.trans (Finset.sum_congr rfl fun s _ => ?_)
    rw [map_smul, Submodule.coe_subtype, ← ExteriorAlgebra.basis_eq_coe_basis b s]
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hne : s.val ≠ Finset.univ := fun h => by
    have hcard := congrArg Finset.card h
    rw [s.2, Finset.card_fin] at hcard
    exact Nat.ne_of_lt hk hcard
  rw [LinearMap.map_smul, volCoord, b.ExteriorAlgebra.coord_apply, b.ExteriorAlgebra.repr_self,
    Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero]

theorem volCoord_change_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b b' : Module.Basis (Fin n) K V) (x : ExteriorAlgebra K V) :
    volCoord b x = b.det b' * volCoord b' x := by
  have hx : x = ∑ s : Finset (Fin n), b'.ExteriorAlgebra.repr x s • b'.ExteriorAlgebra s :=
    (b'.ExteriorAlgebra.sum_repr x).symm
  conv_lhs => rw [hx, map_sum]
  conv_rhs => rw [hx, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s = Finset.univ
  · subst hs
    have hvol : b'.ExteriorAlgebra Finset.univ = volume b' := rfl
    rw [hvol, LinearMap.map_smul, LinearMap.map_smul, volCoord_volume b',
      volume_change_basis b b', LinearMap.map_smul, volCoord_volume b, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one, mul_comm]
  · have hcard_lt : s.card < n := by
      have hss : s ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hs
      simpa [Finset.card_fin] using Finset.card_lt_card hss
    have hmem : b'.ExteriorAlgebra s ∈ ⋀[K]^s.card V := basis_mem_exteriorPower b' s
    simp only [LinearMap.map_smul, volCoord_eq_zero_of_mem_exteriorPower_lt b hcard_lt hmem,
      volCoord_eq_zero_of_mem_exteriorPower_lt b' hcard_lt hmem, smul_zero, mul_zero]

theorem volCoord_eq_of_det_eq_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b b' : Module.Basis (Fin n) K V) (hdet : b.det b' = 1) (x : ExteriorAlgebra K V) :
    volCoord b' x = volCoord b x := by
  have h := volCoord_change_basis b b' x
  rw [hdet, one_mul] at h
  exact h.symm

/-! ## 1. Editorial Note 29, Theorems 1–5: Blade Closure & Duality (`pp. 338–339`) -/

section Note29BladeTheorems

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Editorial Note 29, Theorem 1 (`p. 338`)**:
for any two blades of orders `r, s` with `n < r + s`, their regressive product is again a
decomposable `(r + s - n)`-blade `ιMulti K (r + s - n) z`. -/
theorem note29_thm1_regressive_blades_decomposable {n r s : ℕ} (b : Module.Basis (Fin n) K V)
    (v : Fin r → V) (w : Fin s → V) (hrs : n < r + s) :
    ∃ z : Fin (r + s - n) → V,
      regressive b (ExteriorAlgebra.ιMulti K r v) (ExteriorAlgebra.ιMulti K s w) =
        ExteriorAlgebra.ιMulti K (r + s - n) z := by
  have hpos : 0 < r + s - n := Nat.sub_pos_of_lt hrs
  by_cases hv : LinearIndependent K v
  · by_cases hw : LinearIndependent K w
    · by_cases hsup : Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w) = ⊤
      · let U := Submodule.span K (Set.range v)
        let W := Submodule.span K (Set.range w)
        let I := U ⊓ W
        have : Module.Finite K V := Module.Finite.of_basis b
        obtain ⟨U₁', hU₁'⟩ := (I.comap U.subtype).exists_isCompl
        obtain ⟨W₁', hW₁'⟩ := (I.comap W.subtype).exists_isCompl
        let U₁ := U₁'.map U.subtype
        let W₁ := W₁'.map W.subtype
        have hIU_disj : Disjoint I U₁ := by
          rw [disjoint_iff_inf_le]
          rintro x ⟨hxI, y, hyU₁, rfl⟩
          have hbot := hU₁'.disjoint.le_bot ⟨(hxI : y ∈ I.comap U.subtype), hyU₁⟩
          rw [Submodule.mem_bot] at hbot
          simp [hbot]
        have hIW_disj : Disjoint I W₁ := by
          rw [disjoint_iff_inf_le]
          rintro x ⟨hxI, y, hyW₁, rfl⟩
          have hbot := hW₁'.disjoint.le_bot ⟨(hxI : y ∈ I.comap W.subtype), hyW₁⟩
          rw [Submodule.mem_bot] at hbot
          simp [hbot]
        have hIU_sup : I ⊔ U₁ = U := by
          apply le_antisymm (sup_le inf_le_left (Submodule.map_subtype_le _ _))
          intro x hxU
          have hmem : (⟨x, hxU⟩ : U) ∈ (I.comap U.subtype) ⊔ U₁' :=
            hU₁'.codisjoint.eq_top.symm ▸ Submodule.mem_top
          obtain ⟨a, ha, b₁, hb₁, hab⟩ := Submodule.mem_sup.mp hmem
          have hx_eq : x = (a : V) + (b₁ : V) := congrArg Subtype.val hab.symm
          rw [hx_eq]
          exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
            (Submodule.mem_sup_right ⟨b₁, hb₁, rfl⟩)
        have hIW_sup : I ⊔ W₁ = W := by
          apply le_antisymm (sup_le inf_le_right (Submodule.map_subtype_le _ _))
          intro x hxW
          have hmem : (⟨x, hxW⟩ : W) ∈ (I.comap W.subtype) ⊔ W₁' :=
            hW₁'.codisjoint.eq_top.symm ▸ Submodule.mem_top
          obtain ⟨a, ha, b₁, hb₁, hab⟩ := Submodule.mem_sup.mp hmem
          have hx_eq : x = (a : V) + (b₁ : V) := congrArg Subtype.val hab.symm
          rw [hx_eq]
          exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
            (Submodule.mem_sup_right ⟨b₁, hb₁, rfl⟩)
        have hUW₁_disj : Disjoint U W₁ := by
          rw [disjoint_iff_inf_le]
          intro x ⟨hxU, hxW₁⟩
          exact hIW_disj.le_bot ⟨⟨hxU, Submodule.map_subtype_le _ _ hxW₁⟩, hxW₁⟩
        have hUW₁_sup : U ⊔ W₁ = ⊤ := by
          have h2 : U ⊔ W ≤ U ⊔ (I ⊔ W₁) := sup_le_sup_left hIW_sup.ge U
          have h3 : U ⊔ (I ⊔ W₁) = (U ⊔ I) ⊔ W₁ := (sup_assoc _ _ _).symm
          have h4 : U ⊔ I = U := sup_of_le_left inf_le_left
          rw [hsup, h3, h4, top_le_iff] at h2
          exact h2
        let k := Module.finrank K I
        let p := Module.finrank K U₁
        let q := Module.finrank K W₁
        have hfinI : k = r + s - n := by
          have hsi := Submodule.finrank_sup_add_finrank_inf_eq U W
          have hfinV : Module.finrank K V = n := by
            rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
          have hfinU : Module.finrank K U = r := by rw [finrank_span_eq_card hv, Fintype.card_fin]
          have hfinW : Module.finrank K W = s := by rw [finrank_span_eq_card hw, Fintype.card_fin]
          have hsupUW : U ⊔ W = ⊤ := hsup
          rw [hsupUW, finrank_top, hfinV, hfinU, hfinW] at hsi
          change Module.finrank K ↥(U ⊓ W) = r + s - n
          rw [← hsi, Nat.add_sub_cancel_left]
        let bI := Module.finBasisOfFinrankEq K I hfinI
        let bU₁ := Module.finBasis K U₁
        let bW₁ := Module.finBasis K W₁
        let c : Fin (r + s - n) → V := fun i => (bI i : V)
        let a₁ : Fin p → V := fun i => (bU₁ i : V)
        let b₁ : Fin q → V := fun i => (bW₁ i : V)
        have hc_li : LinearIndependent K c :=
          bI.linearIndependent.map' I.subtype (Submodule.ker_subtype I)
        have ha₁_li : LinearIndependent K a₁ :=
          bU₁.linearIndependent.map' U₁.subtype (Submodule.ker_subtype U₁)
        have hb₁_li : LinearIndependent K b₁ :=
          bW₁.linearIndependent.map' W₁.subtype (Submodule.ker_subtype W₁)
        have hspan_c : Submodule.span K (Set.range c) = I := by
          rw [show Set.range c = I.subtype '' Set.range bI from Set.range_comp _ _,
            ← Submodule.map_span, bI.span_eq, Submodule.map_subtype_top]
        have hspan_a₁ : Submodule.span K (Set.range a₁) = U₁ := by
          rw [show Set.range a₁ = U₁.subtype '' Set.range bU₁ from Set.range_comp _ _,
            ← Submodule.map_span, bU₁.span_eq, Submodule.map_subtype_top]
        have hspan_b₁ : Submodule.span K (Set.range b₁) = W₁ := by
          rw [show Set.range b₁ = W₁.subtype '' Set.range bW₁ from Set.range_comp _ _,
            ← Submodule.map_span, bW₁.span_eq, Submodule.map_subtype_top]
        have hca_li : LinearIndependent K (Fin.append c a₁) := by
          rw [linearIndependent_append_iff_disjoint c a₁ hc_li ha₁_li, hspan_c, hspan_a₁]
          exact hIU_disj
        have hcb_li : LinearIndependent K (Fin.append c b₁) := by
          rw [linearIndependent_append_iff_disjoint c b₁ hc_li hb₁_li, hspan_c, hspan_b₁]
          exact hIW_disj
        have hspan_ca : Submodule.span K (Set.range (Fin.append c a₁)) = U := by
          rw [range_fin_append, Submodule.span_union, hspan_c, hspan_a₁, hIU_sup]
        have hspan_cb : Submodule.span K (Set.range (Fin.append c b₁)) = W := by
          rw [range_fin_append, Submodule.span_union, hspan_c, hspan_b₁, hIW_sup]
        have hcab_li : LinearIndependent K (Fin.append (Fin.append c a₁) b₁) := by
          rw [linearIndependent_append_iff_disjoint (Fin.append c a₁) b₁ hca_li hb₁_li,
            hspan_ca, hspan_b₁]
          exact hUW₁_disj
        have hspan_cab : Submodule.span K (Set.range (Fin.append (Fin.append c a₁) b₁)) = ⊤ := by
          rw [range_fin_append, Submodule.span_union, hspan_ca, hspan_b₁, hUW₁_sup]
        have hkp : (r + s - n) + p = r := by
          have h1 := finrank_span_eq_card hca_li
          have h2 := finrank_span_eq_card hv
          rw [hspan_ca] at h1
          change Module.finrank K U = _ at h2
          rw [h1, Fintype.card_fin, Fintype.card_fin] at h2
          omega
        have hkq : (r + s - n) + q = s := by
          have h1 := finrank_span_eq_card hcb_li
          have h2 := finrank_span_eq_card hw
          rw [hspan_cb] at h1
          change Module.finrank K W = _ at h2
          rw [h1, Fintype.card_fin, Fintype.card_fin] at h2
          omega
        have hkpq : (r + s - n) + p + q = n := by
          have h1 := finrank_span_eq_card hcab_li
          have h2 : Module.finrank K V = n := by
            rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
          rw [hspan_cab, finrank_top, Fintype.card_fin] at h1
          omega
        let ca' : Fin r → V := (Fin.append c a₁) ∘ (finCongr hkp).symm
        let cb' : Fin s → V := (Fin.append c b₁) ∘ (finCongr hkq).symm
        have hca'_li : LinearIndependent K ca' := hca_li.comp _ (finCongr hkp).symm.injective
        have hcb'_li : LinearIndependent K cb' := hcb_li.comp _ (finCongr hkq).symm.injective
        have hspan_ca' : Submodule.span K (Set.range ca') = U := by
          rw [show Set.range ca' = Set.range (Fin.append c a₁) by
            rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ], hspan_ca]
        have hspan_cb' : Submodule.span K (Set.range cb') = W := by
          rw [show Set.range cb' = Set.range (Fin.append c b₁) by
            rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ], hspan_cb]
        obtain ⟨cU, hcU⟩ := (plucker_span_eq_iff_proportional v ca' hv hca'_li).mp hspan_ca'.symm
        obtain ⟨cW, hcW⟩ := (plucker_span_eq_iff_proportional w cb' hw hcb'_li).mp hspan_cb'.symm
        have hιv : ExteriorAlgebra.ιMulti K r v =
            (cU : K) • (ExteriorAlgebra.ιMulti K (r + s - n) c * ExteriorAlgebra.ιMulti K p a₁) := by
          rw [hcU, ← ιMulti_fin_append_congr' hkp c a₁]
        have hιw : ExteriorAlgebra.ιMulti K s w =
            (cW : K) • (ExteriorAlgebra.ιMulti K (r + s - n) c * ExteriorAlgebra.ιMulti K q b₁) := by
          rw [hcW, ← ιMulti_fin_append_congr' hkq c b₁]
        have hno103 := grassmann_no103_blade b hkpq c
          (ExteriorAlgebra.ιMulti_range K p ⟨a₁, rfl⟩)
          (ExteriorAlgebra.ιMulti_range K q ⟨b₁, rfl⟩)
        let scalar : K := (cU : K) * (cW : K) *
          volCoord b (ExteriorAlgebra.ιMulti K (r + s - n) c *
            ExteriorAlgebra.ιMulti K p a₁ * ExteriorAlgebra.ιMulti K q b₁)
        refine ⟨Function.update c ⟨0, hpos⟩ (scalar • c ⟨0, hpos⟩), ?_⟩
        dsimp only [scalar]
        rw [ιMulti_rescale_zero hpos _ c, hιv, hιw, smul_regressive, regressive_smul, hno103,
          smul_smul, smul_smul]
      · refine ⟨0, ?_⟩
        rw [regressive_ιMulti_eq_zero_of_sup_ne_top b v w hsup,
          (ExteriorAlgebra.ιMulti K (r + s - n)).map_coord_zero ⟨0, hpos⟩ rfl]
    · refine ⟨0, ?_⟩
      rw [(ιMulti_eq_zero_iff w).mpr hw, regressive_zero,
        (ExteriorAlgebra.ιMulti K (r + s - n)).map_coord_zero ⟨0, hpos⟩ rfl]
  · refine ⟨0, ?_⟩
    rw [(ιMulti_eq_zero_iff v).mpr hv, zero_regressive,
      (ExteriorAlgebra.ιMulti K (r + s - n)).map_coord_zero ⟨0, hpos⟩ rfl]

/-- **Editorial Note 29, Theorem 2 (`p. 338`)**:
the Hodge supplement `hodge b (ιMulti K m v)` of any linearly independent `m`-blade is
decomposable as a linearly independent `(n - m)`-blade, and its annihilator support `bladeSupport`
is the exact `extInner b`-orthogonal complement of `span (range v)`. -/
theorem note29_thm2_hodge_blade_decomposable_and_support {n m : ℕ} (b : Module.Basis (Fin n) K V)
    (v : Fin m → V) (hv : LinearIndependent K v) :
    (∃ (c : Kˣ) (w : Fin (n - m) → V),
      LinearIndependent K w ∧
        hodge b (ExteriorAlgebra.ιMulti K m v) = (c : K) • ExteriorAlgebra.ιMulti K (n - m) w) ∧
      (1 ≤ n - m →
        ∃ w : Fin (n - m) → V,
          LinearIndependent K w ∧
            hodge b (ExteriorAlgebra.ιMulti K m v) = ExteriorAlgebra.ιMulti K (n - m) w) ∧
      ∀ x : V,
        x ∈ bladeSupport (hodge b (ExteriorAlgebra.ιMulti K m v)) ↔
          ∀ y ∈ Submodule.span K (Set.range v),
            extInner b (ExteriorAlgebra.ι K y) (ExteriorAlgebra.ι K x) = 0 := by
  let d : Fin m → Module.Dual K V := fun i => b.toDualEquiv (v i)
  have hd_li : LinearIndependent K d :=
    hv.map' b.toDualEquiv.toLinearMap (LinearEquiv.ker b.toDualEquiv)
  have : Module.Finite K V := Module.Finite.of_basis b
  have : Module.Finite K (Module.Dual K V) := Module.Finite.of_basis b.dualBasis
  let sD := Module.Basis.sumExtend hd_li
  have : Finite (Fin m ⊕ Module.Basis.sumExtendIndex hd_li) := Module.Finite.finite_basis sD
  have : Fintype (Fin m ⊕ Module.Basis.sumExtendIndex hd_li) := Fintype.ofFinite _
  have hfinD : Fintype.card (Fin m ⊕ Module.Basis.sumExtendIndex hd_li) = n := by
    rw [← Module.finrank_eq_card_basis sD, Module.finrank_eq_card_basis b.dualBasis, Fintype.card_fin]
  let eIdx := Fintype.equivFinOfCardEq hfinD
  let D : Module.Basis (Fin n) K (Module.Dual K V) := sD.reindex eIdx
  let f : Fin m → Fin n := fun i => eIdx (Sum.inl i)
  have hf_inj : Function.Injective f := fun i j h => Sum.inl.inj (eIdx.injective h)
  have hDf : ∀ i : Fin m, D (f i) = d i := fun i => by
    dsimp [D, f]
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    dsimp [sD, Module.Basis.sumExtend]
    rw [Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
    rfl
  obtain ⟨b', hb'_dual⟩ : ∃ b' : Module.Basis (Fin n) K V, b'.dualBasis = D := by
    let b' : Module.Basis (Fin n) K V := D.dualBasis.map (Module.evalEquiv K V).symm
    refine ⟨b', ?_⟩
    ext1 j
    apply b'.ext
    intro i
    have h1 : b'.dualBasis j (b' i) = if i = j then 1 else 0 := b'.dualBasis_apply_self j i
    have h2 : (D j) (b' i) = D.dualBasis i (D j) := by
      change (Module.evalEquiv K V ((Module.evalEquiv K V).symm (D.dualBasis i))) (D j) = _
      rw [(Module.evalEquiv K V).apply_symm_apply]
    have h3 : D.dualBasis i (D j) = if j = i then 1 else 0 := D.dualBasis_apply_self i j
    rw [h1, h2, h3]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  let s : Finset (Fin n) := Finset.univ.map ⟨f, hf_inj⟩
  have hs_card : s.card = m := by simp [s]
  have hsc_card : sᶜ.card = n - m := by rw [Finset.card_compl, Fintype.card_fin, hs_card]
  let g := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) hs_card)
  have hspan_df : Submodule.span K (Set.range (fun i => b'.dualBasis (g i))) =
      Submodule.span K (Set.range d) := by
    have hrng : Set.range (fun i => b'.dualBasis (g i)) = Set.range d := by
      ext φ
      constructor
      · rintro ⟨i, rfl⟩
        have hmem : g i ∈ s :=
          (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
            (Set.powersetCard.ofCard (s := s) hs_card) (g i)).1 ⟨i, rfl⟩
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hmem
        have hj' : f j = g i := hj
        refine ⟨j, ?_⟩
        dsimp only
        rw [hb'_dual, ← hj', hDf j]
      · rintro ⟨j, rfl⟩
        have hmem : f j ∈ s := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
        obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
          (Set.powersetCard.ofCard (s := s) hs_card) (f j)).2 hmem
        refine ⟨i, ?_⟩
        dsimp only
        rw [hb'_dual, hi, hDf j]
    rw [hrng]
  have hdg_li : LinearIndependent K (fun i => b'.dualBasis (g i)) :=
    b'.dualBasis.linearIndependent.comp g g.injective
  obtain ⟨cD, hcD⟩ := (plucker_span_eq_iff_proportional d (fun i => b'.dualBasis (g i)) hd_li hdg_li).mp
    hspan_df.symm
  have hdt : dualTransferEquiv b (ExteriorAlgebra.ιMulti K m v) =
      ExteriorAlgebra.ιMulti K m d := by
    change ExteriorAlgebra.map b.toDualEquiv.toLinearMap (ExteriorAlgebra.ιMulti K m v) = _
    rw [ExteriorAlgebra.map_apply_ιMulti]
    rfl
  let dbU : Kˣ := (b.isUnit_det b').unit
  let cU : Kˣ := cD * dbU⁻¹ * orientationUnit (K := K) s
  have hh_eq : hodge b (ExteriorAlgebra.ιMulti K m v) = (cU : K) • b'.ExteriorAlgebra sᶜ := by
    have hpe : hodge b (ExteriorAlgebra.ιMulti K m v) =
        poincareEval b (ExteriorAlgebra.ιMulti K m d) := by
      have h1 := LinearMap.congr_fun (poincareEval_comp_dualTransferEquiv b)
        (ExteriorAlgebra.ιMulti K m v)
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hdt] using h1.symm
    have hbs : ExteriorAlgebra.ιMulti K m (fun i => b'.dualBasis (g i)) =
        b'.dualBasis.ExteriorAlgebra s := by
      change ExteriorAlgebra.ιMulti K m (fun i => b'.dualBasis
        (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) hs_card) i)) =
        b'.dualBasis.ExteriorAlgebra s
      exact exteriorAlgebra_basis_ofCard b'.dualBasis hs_card
    have hpe_inv : ∀ α : ExteriorAlgebra K (Module.Dual K V),
        poincareEval b α = (dbU⁻¹ : Kˣ) • poincareEval b' α := fun α => by
      have hcb := poincareEval_change_basis b b' α
      have hcb' : (dbU : K) • poincareEval b α = poincareEval b' α := hcb.symm
      have hcon := congrArg ((dbU⁻¹ : Kˣ) • ·) hcb'
      simpa only [Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_smul] using hcon
    have hcU_val : (cU : K) = (cD : K) * (dbU⁻¹ : Kˣ) * (orientationUnit (K := K) s : K) := by
      simp [cU]
    rw [hpe, hcD, hbs, LinearMap.map_smul, hpe_inv, poincareEval_dualBasis b' s,
      hodge_basis b' s, Units.smul_def, smul_smul, smul_smul, ← hcU_val]
  let gc := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := sᶜ) hsc_card)
  let w : Fin (n - m) → V := fun k => b' (gc k)
  have hw_li : LinearIndependent K w := b'.linearIndependent.comp gc gc.injective
  have hw_eq : b'.ExteriorAlgebra sᶜ = ExteriorAlgebra.ιMulti K (n - m) w :=
    ExteriorAlgebra.basis_apply_ofCard b' hsc_card
  rw [hw_eq] at hh_eq
  refine ⟨⟨cU, w, hw_li, hh_eq⟩, fun hpos => ?_, fun x => ?_⟩
  · let w' : Fin (n - m) → V := Function.update w ⟨0, hpos⟩ ((cU : K) • w ⟨0, hpos⟩)
    have hres : ExteriorAlgebra.ιMulti K (n - m) w' =
        (cU : K) • ExteriorAlgebra.ιMulti K (n - m) w := ιMulti_rescale_zero hpos (cU : K) w
    have hw'_ne : ExteriorAlgebra.ιMulti K (n - m) w' ≠ 0 := by
      rw [hres]
      exact smul_ne_zero cU.ne_zero (ιMulti_ne_zero_of_linearIndependent w hw_li)
    exact ⟨w', not_not.mp ((ιMulti_eq_zero_iff w').not.mp hw'_ne), hh_eq.trans hres.symm⟩
  · rw [hh_eq, bladeSupport_smul _ cU.ne_zero, bladeSupport_ιMulti w hw_li]
    have hmem_iff : ∀ z : V, z ∈ Submodule.span K (Set.range w) ↔ ∀ i : Fin m, d i z = 0 := by
      intro z
      constructor
      · intro hz
        refine Submodule.span_induction (p := fun z _ => ∀ i : Fin m, d i z = 0)
          ?_ ?_ ?_ ?_ hz
        · rintro _ ⟨k, rfl⟩ i
          have hmem_gc : gc k ∈ sᶜ :=
            (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
              (Set.powersetCard.ofCard (s := sᶜ) hsc_card) (gc k)).1 ⟨k, rfl⟩
          have hne : gc k ≠ f i := fun h =>
            Finset.mem_compl.mp hmem_gc (h ▸ Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
          rw [← hDf i, ← hb'_dual, b'.dualBasis_apply_self, ite_eq_right hne]
        · intro i; exact map_zero (d i)
        · intro a c _ _ ha hc i; simp [ha i, hc i]
        · intro r a _ ha i; simp [ha i]
      · intro hz
        have hz_rep : z = ∑ j : Fin n, b'.repr z j • b' j := (b'.sum_repr z).symm
        have hvan : ∀ j : Fin n, j ∈ s → b'.repr z j = 0 := fun j hj => by
          obtain ⟨i, _, hij⟩ := Finset.mem_map.mp hj
          change f i = j at hij
          rw [← hij, ← b'.dualBasis_apply (f i) z, hb'_dual, hDf i]
          exact hz i
        have hdiff : Finset.univ \ s = sᶜ := by
          ext y; simp
        have hsum_sc : z = ∑ j ∈ sᶜ, b'.repr z j • b' j := by
          conv_lhs => rw [hz_rep]
          rw [← Finset.sum_sdiff (Finset.subset_univ s), hdiff]
          have hsz : ∑ j ∈ s, b'.repr z j • b' j = 0 := Finset.sum_eq_zero fun j hj => by
            rw [hvan j hj, zero_smul]
          rw [hsz, add_zero]
        rw [hsum_sc]
        refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
        obtain ⟨k, hk⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
          (Set.powersetCard.ofCard (s := sᶜ) hsc_card) j).2 hj
        exact Submodule.subset_span ⟨k, congrArg b' hk⟩
    rw [hmem_iff x]
    constructor
    · intro hx y hy
      refine Submodule.span_induction (p := fun y _ =>
        extInner b (ExteriorAlgebra.ι K y) (ExteriorAlgebra.ι K x) = 0) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩
        rw [← toDualEquiv_eq_extInner_pub b (v i) x]
        exact hx i
      · simp
      · intro a c _ _ ha hc; rw [map_add, map_add, LinearMap.add_apply, ha, hc, add_zero]
      · intro r a _ ha; simp [ha]
    · intro hx i
      rw [show d i x = extInner b (ExteriorAlgebra.ι K (v i)) (ExteriorAlgebra.ι K x) from
        toDualEquiv_eq_extInner_pub b (v i) x]
      exact hx (v i) (Submodule.subset_span ⟨i, rfl⟩)

/-- **Editorial Note 29, Theorem 3 (`p. 338`, converse of `No. 79B`)**:
if `A = ιMulti K α v` and `B = ιMulti K β w` are independent blades with `span v ≤ span w`
and `1 ≤ α + (n - β)`, there exists an independent `(α + (n - β))`-blade `C = ιMulti K _ z`
satisfying `regressive b B C = A`. -/
theorem note29_thm3_exists_regressive_quotient_blade {n α β : ℕ} (b : Module.Basis (Fin n) K V)
    (v : Fin α → V) (w : Fin β → V) (hv : LinearIndependent K v) (hw : LinearIndependent K w)
    (hpos : 1 ≤ α + (n - β))
    (hle : Submodule.span K (Set.range v) ≤ Submodule.span K (Set.range w)) :
    ∃ z : Fin (α + (n - β)) → V,
      LinearIndependent K z ∧
        regressive b (ExteriorAlgebra.ιMulti K β w)
          (ExteriorAlgebra.ιMulti K (α + (n - β)) z) = ExteriorAlgebra.ιMulti K α v := by
  let U := Submodule.span K (Set.range v)
  let W := Submodule.span K (Set.range w)
  have : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨U₁', hU₁'⟩ := (U.comap W.subtype).exists_isCompl
  obtain ⟨W', hW'⟩ := W.exists_isCompl
  let U₁ := U₁'.map W.subtype
  have hUU₁_disj : Disjoint U U₁ := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨hxU, y, hyU₁, rfl⟩
    have hbot := hU₁'.disjoint.le_bot ⟨(hxU : y ∈ U.comap W.subtype), hyU₁⟩
    rw [Submodule.mem_bot] at hbot
    simp [hbot]
  have hUU₁_sup : U ⊔ U₁ = W := by
    apply le_antisymm (sup_le hle (Submodule.map_subtype_le _ _))
    intro x hxW
    have hmem : (⟨x, hxW⟩ : W) ∈ (U.comap W.subtype) ⊔ U₁' :=
      hU₁'.codisjoint.eq_top.symm ▸ Submodule.mem_top
    obtain ⟨a, ha, b₁, hb₁, hab⟩ := Submodule.mem_sup.mp hmem
    have hx_eq : x = (a : V) + (b₁ : V) := congrArg Subtype.val hab.symm
    rw [hx_eq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
      (Submodule.mem_sup_right ⟨b₁, hb₁, rfl⟩)
  let p := Module.finrank K U₁
  let q := Module.finrank K W'
  have hfinV : Module.finrank K V = n := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hfinU : Module.finrank K U = α := by rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hfinW : Module.finrank K W = β := by rw [finrank_span_eq_card hw, Fintype.card_fin]
  have hβ : β ≤ n := by
    have hleV : Module.finrank K W ≤ Module.finrank K V := Submodule.finrank_le W
    omega
  have hq : q = n - β := by
    have hadd := Submodule.finrank_add_eq_of_isCompl hW'
    omega
  have hp : α + p = β := by
    have hsi := Submodule.finrank_sup_add_finrank_inf_eq U U₁
    rw [hUU₁_disj.eq_bot, finrank_bot, add_zero, hUU₁_sup, hfinU, hfinW] at hsi
    omega
  let bU₁ := Module.finBasis K U₁
  let bW' := Module.finBasisOfFinrankEq K W' hq
  let u₁ : Fin p → V := fun i => (bU₁ i : V)
  let w' : Fin (n - β) → V := fun j => (bW' j : V)
  have hu₁_li : LinearIndependent K u₁ :=
    bU₁.linearIndependent.map' U₁.subtype (Submodule.ker_subtype U₁)
  have hw'_li : LinearIndependent K w' :=
    bW'.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hspan_u₁ : Submodule.span K (Set.range u₁) = U₁ := by
    rw [show Set.range u₁ = U₁.subtype '' Set.range bU₁ from Set.range_comp _ _,
      ← Submodule.map_span, bU₁.span_eq, Submodule.map_subtype_top]
  have hspan_w' : Submodule.span K (Set.range w') = W' := by
    rw [show Set.range w' = W'.subtype '' Set.range bW' from Set.range_comp _ _,
      ← Submodule.map_span, bW'.span_eq, Submodule.map_subtype_top]
  have hvu_li : LinearIndependent K (Fin.append v u₁) := by
    rw [linearIndependent_append_iff_disjoint v u₁ hv hu₁_li, hspan_u₁]
    exact hUU₁_disj
  have hspan_vu : Submodule.span K (Set.range (Fin.append v u₁)) = W := by
    rw [range_fin_append, Submodule.span_union, hspan_u₁, hUU₁_sup]
  have hUW'_disj : Disjoint U W' := hW'.disjoint.mono_left hle
  have hvw'_li : LinearIndependent K (Fin.append v w') := by
    rw [linearIndependent_append_iff_disjoint v w' hv hw'_li, hspan_w']
    exact hUW'_disj
  have hvuw_li : LinearIndependent K (Fin.append (Fin.append v u₁) w') := by
    rw [linearIndependent_append_iff_disjoint (Fin.append v u₁) w' hvu_li hw'_li,
      hspan_vu, hspan_w']
    exact hW'.disjoint
  let vu' : Fin β → V := (Fin.append v u₁) ∘ (finCongr hp).symm
  have hvu'_li : LinearIndependent K vu' := hvu_li.comp _ (finCongr hp).symm.injective
  have hspan_vu' : Submodule.span K (Set.range vu') = W := by
    rw [show Set.range vu' = Set.range (Fin.append v u₁) by
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ], hspan_vu]
  obtain ⟨cW, hcW⟩ := (plucker_span_eq_iff_proportional w vu' hw hvu'_li).mp hspan_vu'.symm
  have hιw : ExteriorAlgebra.ιMulti K β w =
      (cW : K) • (ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K p u₁) := by
    rw [hcW, ← ιMulti_fin_append_congr' hp v u₁]
  have hdeg : α + p + (n - β) = n := by omega
  have hno103 := grassmann_no103_blade b hdeg v
    (ExteriorAlgebra.ιMulti_range K p ⟨u₁, rfl⟩)
    (ExteriorAlgebra.ιMulti_range K (n - β) ⟨w', rfl⟩)
  have htop_prod : ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K p u₁ *
      ExteriorAlgebra.ιMulti K (n - β) w' =
      ExteriorAlgebra.ιMulti K (α + p + (n - β)) (Fin.append (Fin.append v u₁) w') := by
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti]
  have htop_ne : ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K p u₁ *
      ExteriorAlgebra.ιMulti K (n - β) w' ≠ 0 := by
    rw [htop_prod]
    exact ιMulti_ne_zero_of_linearIndependent _ hvuw_li
  have htop_mem : ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K p u₁ *
      ExteriorAlgebra.ιMulti K (n - β) w' ∈ ⋀[K]^n V := by
    have hmem : ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K p u₁ *
        ExteriorAlgebra.ιMulti K (n - β) w' ∈ ⋀[K]^(α + p + (n - β)) V := by
      rw [htop_prod]
      exact ExteriorAlgebra.ιMulti_range K _ ⟨_, rfl⟩
    simpa [hdeg] using hmem
  have hvol_ne : volCoord b (ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K p u₁ *
      ExteriorAlgebra.ιMulti K (n - β) w') ≠ 0 := by
    intro h0
    apply htop_ne
    have hsm := eq_volCoord_smul_volume b htop_mem
    rwa [h0, zero_smul] at hsm
  let denom : K := (cW : K) * volCoord b (ExteriorAlgebra.ιMulti K α v *
    ExteriorAlgebra.ιMulti K p u₁ * ExteriorAlgebra.ιMulti K (n - β) w')
  have hdenom_ne : denom ≠ 0 := mul_ne_zero cW.ne_zero hvol_ne
  let z₀ : Fin (α + (n - β)) → V := Fin.append v w'
  let z : Fin (α + (n - β)) → V := Function.update z₀ ⟨0, hpos⟩ (denom⁻¹ • z₀ ⟨0, hpos⟩)
  have hres : ExteriorAlgebra.ιMulti K (α + (n - β)) z =
      denom⁻¹ • (ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K (n - β) w') := by
    dsimp [z, z₀]
    rw [ιMulti_rescale_zero hpos denom⁻¹ (Fin.append v w'), ExteriorAlgebra.ιMulti_mul_ιMulti]
  have hz_ne : ExteriorAlgebra.ιMulti K (α + (n - β)) z ≠ 0 := by
    rw [hres]
    have hmul_z₀ : ExteriorAlgebra.ιMulti K (α + (n - β)) z₀ =
        ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K (n - β) w' := by
      dsimp [z₀]
      rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
    exact smul_ne_zero (inv_ne_zero hdenom_ne) (hmul_z₀ ▸ ιMulti_ne_zero_of_linearIndependent z₀ hvw'_li)
  refine ⟨z, not_not.mp ((ιMulti_eq_zero_iff z).not.mp hz_ne), ?_⟩
  rw [hres, hιw, smul_regressive, regressive_smul, hno103, smul_smul, smul_smul]
  have hsc : (cW : K) * denom⁻¹ *
      volCoord b (ExteriorAlgebra.ιMulti K α v * ExteriorAlgebra.ιMulti K p u₁ *
        ExteriorAlgebra.ιMulti K (n - β) w') = 1 := by
    dsimp [denom]
    field_simp [cW.ne_zero, hvol_ne]
  rw [hsc, one_smul]

/-- **Editorial Note 29, Theorems 4 & 5 (`pp. 338–339`)**:
the Hodge supplement reverses subspace subordination and preserves subspace incidence. -/
theorem note29_thm4_thm5_hodge_subordination_and_incidence {n α β : ℕ}
    (b : Module.Basis (Fin n) K V) (v : Fin α → V) (w : Fin β → V)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    (Submodule.span K (Set.range v) ≤ Submodule.span K (Set.range w) ↔
        bladeSupport (hodge b (ExteriorAlgebra.ιMulti K β w)) ≤
          bladeSupport (hodge b (ExteriorAlgebra.ιMulti K α v))) ∧
      ((Submodule.span K (Set.range v) ≤ Submodule.span K (Set.range w) ∨
          Submodule.span K (Set.range w) ≤ Submodule.span K (Set.range v)) ↔
        (bladeSupport (hodge b (ExteriorAlgebra.ιMulti K β w)) ≤
            bladeSupport (hodge b (ExteriorAlgebra.ιMulti K α v)) ∨
          bladeSupport (hodge b (ExteriorAlgebra.ιMulti K α v)) ≤
            bladeSupport (hodge b (ExteriorAlgebra.ιMulti K β w)))) := by
  have hsub_iff : ∀ {r s : ℕ} (a : Fin r → V) (c : Fin s → V),
      LinearIndependent K a → LinearIndependent K c →
      (Submodule.span K (Set.range a) ≤ Submodule.span K (Set.range c) ↔
        bladeSupport (hodge b (ExteriorAlgebra.ιMulti K s c)) ≤
          bladeSupport (hodge b (ExteriorAlgebra.ιMulti K r a))) := by
    intro r s a c ha hc
    have hsup_a := (note29_thm2_hodge_blade_decomposable_and_support b a ha).2.2
    have hsup_c := (note29_thm2_hodge_blade_decomposable_and_support b c hc).2.2
    constructor
    · intro hac x hx
      rw [hsup_a x]
      intro y hy
      exact (hsup_c x).mp hx y (hac hy)
    · intro hle x hx
      by_contra hxn
      let W := Submodule.span K (Set.range c)
      have hq_ne : W.mkQ x ≠ 0 := by
        intro h0
        exact hxn ((Submodule.Quotient.mk_eq_zero W).mp h0)
      obtain ⟨dq, hdq⟩ := Module.Projective.exists_dual_eq_one K hq_ne
      let d : Module.Dual K V := dq.comp W.mkQ
      let z : V := b.toDualEquiv.symm d
      have hdz : ∀ y : V, extInner b (ExteriorAlgebra.ι K y) (ExteriorAlgebra.ι K z) = d y := fun y => by
        rw [← toDualEquiv_eq_extInner_pub b y z]
        have hsym := extInner_symm b (ExteriorAlgebra.ι K y) (ExteriorAlgebra.ι K z)
        rw [toDualEquiv_eq_extInner_pub b y z, hsym, ← toDualEquiv_eq_extInner_pub b z y]
        change b.toDualEquiv (b.toDualEquiv.symm d) y = d y
        rw [LinearEquiv.apply_symm_apply]
      have hzW : z ∈ bladeSupport (hodge b (ExteriorAlgebra.ιMulti K s c)) := by
        rw [hsup_c z]
        intro y hy
        rw [hdz y]
        change dq (Submodule.Quotient.mk y) = 0
        rw [(Submodule.Quotient.mk_eq_zero W).mpr hy, map_zero]
      have hzA := hle hzW
      rw [hsup_a z] at hzA
      have h0 := hzA x hx
      rw [hdz x] at h0
      have h1 : d x = 1 := hdq
      exact one_ne_zero (h1.symm.trans h0)
  have hvw := hsub_iff v w hv hw
  have hwv := hsub_iff w v hw hv
  refine ⟨hvw, ?_⟩
  rw [hvw, hwv]

end Note29BladeTheorems

/-! ## 2. Editorial Note 39: `A₁` (1844) vs. `A₂` (1862) Shadow Sign-Cancellation (`pp. 345–346`) -/

section Note39ShadowSignCancellation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Editorial Note 39 (`pp. 345–346`), Progressive Shadow Equivalence**:
for `p ≤ m ≤ n`, `A ∈ ⋀^p V`, `G ∈ ⋀^m V`, `L ∈ ⋀^(n-m) V`,
1. `regressive b G (A * L) = (-1)^(m(n-m)) • regressive b (L * A) G`, and
2. `volCoord b (L * G) • regressive b G (A * L) = volCoord b (G * L) • regressive b (L * A) G`. -/
theorem note39_progressive_shadow_sign_cancellation {n p m : ℕ} (b : Module.Basis (Fin n) K V)
    (hpm : p ≤ m) (hmn : m ≤ n) {A G L : ExteriorAlgebra K V}
    (hA : A ∈ ⋀[K]^p V) (hG : G ∈ ⋀[K]^m V) (hL : L ∈ ⋀[K]^(n - m) V) :
    regressive b G (A * L) =
        ((-1 : K) ^ (m * (n - m))) • regressive b (L * A) G ∧
      volCoord b (L * G) • regressive b G (A * L) =
        volCoord b (G * L) • regressive b (L * A) G := by
  have hLA_deg : L * A ∈ ⋀[K]^(n - m + p) V := by
    rw [ExteriorAlgebra.exteriorPower, pow_add]
    exact Submodule.mul_mem_mul hL hA
  have hG_c : hodge b G ∈ ⋀[K]^(n - m) V := hodge_mem_exteriorPower b hG
  have hLA_c : hodge b (L * A) ∈ ⋀[K]^(n - (n - m + p)) V := hodge_mem_exteriorPower b hLA_deg
  have hAL_comm : A * L = ((-1 : K) ^ (p * (n - m))) • (L * A) := exteriorPower_mul_comm hA hL
  have hreg_comm : hodge b G * hodge b (L * A) =
      ((-1 : K) ^ ((n - m) * (n - (n - m + p)))) • (hodge b (L * A) * hodge b G) :=
    exteriorPower_mul_comm hG_c hLA_c
  have hmain : regressive b G (A * L) = ((-1 : K) ^ (m * (n - m))) • regressive b (L * A) G := by
    apply (hodge b).injective
    rw [hodge_regressive, hAL_comm, map_smul, mul_smul_comm, hreg_comm, smul_smul,
      map_smul, hodge_regressive, ← pow_add]
    congr 1
    have hle : n - m + p ≤ n := by omega
    have hnat : p * (n - m) + (n - m) * (n - (n - m + p)) = m * (n - m) := by
      zify [hpm, hmn, hle]
      ring
    rw [hnat]
  refine ⟨hmain, ?_⟩
  have hGL : G * L = ((-1 : K) ^ (m * (n - m))) • (L * G) := exteriorPower_mul_comm hG hL
  rw [hmain, smul_smul, hGL, LinearMap.map_smul, smul_eq_mul, mul_comm (volCoord b (L * G)) _]

/-- **Editorial Note 39 (`pp. 345–346`), Regressive Shadow Equivalence**:
for `m ≤ p ≤ n`, `A ∈ ⋀^p V`, `G ∈ ⋀^m V`, `L ∈ ⋀^(n-m) V`,
1. `G * regressive b A L = (-1)^(m(n-m)) • (regressive b L A * G)`, and
2. `volCoord b (L * G) • (G * regressive b A L) = volCoord b (G * L) • (regressive b L A * G)`. -/
theorem note39_regressive_shadow_sign_cancellation {n m p : ℕ} (b : Module.Basis (Fin n) K V)
    (hmp : m ≤ p) (hpn : p ≤ n) {A G L : ExteriorAlgebra K V}
    (hA : A ∈ ⋀[K]^p V) (hG : G ∈ ⋀[K]^m V) (hL : L ∈ ⋀[K]^(n - m) V) :
    G * regressive b A L =
        ((-1 : K) ^ (m * (n - m))) • (regressive b L A * G) ∧
      volCoord b (L * G) • (G * regressive b A L) =
        volCoord b (G * L) • (regressive b L A * G) := by
  have hA_c : hodge b A ∈ ⋀[K]^(n - p) V := hodge_mem_exteriorPower b hA
  have hL_c : hodge b L ∈ ⋀[K]^(n - (n - m)) V := hodge_mem_exteriorPower b hL
  have hLA_deg : regressive b L A ∈ ⋀[K]^(p - m) V := by
    have hrw : p - m = n - (n - (n - m) + (n - p)) := by omega
    rw [hrw]
    dsimp [regressive]
    refine hodge_symm_mem_exteriorPower b ?_
    rw [ExteriorAlgebra.exteriorPower, pow_add]
    exact Submodule.mul_mem_mul hL_c hA_c
  have hreg_comm : regressive b A L = ((-1 : K) ^ ((n - p) * (n - (n - m)))) • regressive b L A := by
    apply (hodge b).injective
    rw [hodge_regressive, map_smul, hodge_regressive]
    exact exteriorPower_mul_comm hA_c hL_c
  have hG_comm : G * regressive b L A = ((-1 : K) ^ (m * (p - m))) • (regressive b L A * G) :=
    exteriorPower_mul_comm hG hLA_deg
  have hmain : G * regressive b A L =
      ((-1 : K) ^ (m * (n - m))) • (regressive b L A * G) := by
    rw [hreg_comm, mul_smul_comm, hG_comm, smul_smul, ← pow_add]
    congr 1
    have hmn : m ≤ n := hmp.trans hpn
    rw [Nat.sub_sub_self hmn]
    have hnat : (n - p) * m + m * (p - m) = m * (n - m) := by
      zify [hmp, hpn, hmn]
      ring
    rw [hnat]
  refine ⟨hmain, ?_⟩
  have hGL : G * L = ((-1 : K) ^ (m * (n - m))) • (L * G) := exteriorPower_mul_comm hG hL
  rw [hmain, smul_smul, hGL, LinearMap.map_smul, smul_eq_mul, mul_comm (volCoord b (L * G)) _]

end Note39ShadowSignCancellation

/-! ## 3. Editorial Note 44: Underdetermined Exterior Cramer System (`p. 347`) -/

section Note44UnderdeterminedCramer

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Editorial Note 44 (`p. 347`) — Rank-Deficient / Underdetermined Exterior Cramer Rule**:
given independent pivot columns `a₀ : Fin r → V`, dependent tail columns `a₁ : Fin s → V` inside
`U = span a₀`, complementary frame `w : Fin s → V` (`IsCompl U W`), and RHS `y ∈ U`:
every tail assignment `x_free : Fin s → K` uniquely determines pivot coefficients `x_piv : Fin r → K`
via Grassmann's exterior volume ratios solving `∑ i, x_piv i • a₀ i + ∑ k, x_free k • a₁ k = y`. -/
theorem note44_underdetermined_exterior_cramer {n r s : ℕ} (b : Module.Basis (Fin n) K V)
    (a₀ : Fin r → V) (ha₀ : LinearIndependent K a₀)
    (a₁ : Fin s → V) (ha₁ : ∀ k : Fin s, a₁ k ∈ Submodule.span K (Set.range a₀))
    (w : Fin s → V) (hw : LinearIndependent K w)
    (hCompl : IsCompl (Submodule.span K (Set.range a₀)) (Submodule.span K (Set.range w)))
    (y : V) (hy : y ∈ Submodule.span K (Set.range a₀)) :
    let D := volCoord b (ExteriorAlgebra.ιMulti K r a₀ * ExteriorAlgebra.ιMulti K s w)
    D ≠ 0 ∧
      (∀ x_free : Fin s → K,
        let y_rem := y - ∑ k : Fin s, x_free k • a₁ k
        let x_piv : Fin r → K := fun i =>
          volCoord b (ExteriorAlgebra.ιMulti K r (Function.update a₀ i y_rem) *
            ExteriorAlgebra.ιMulti K s w) / D
        (∑ i : Fin r, x_piv i • a₀ i) + (∑ k : Fin s, x_free k • a₁ k) = y) ∧
      (∀ (z_piv : Fin r → K) (x_free : Fin s → K),
        ((∑ i : Fin r, z_piv i • a₀ i) + (∑ k : Fin s, x_free k • a₁ k) = y) ↔
          ∀ i : Fin r, z_piv i =
            volCoord b (ExteriorAlgebra.ιMulti K r (Function.update a₀ i
              (y - ∑ k : Fin s, x_free k • a₁ k)) * ExteriorAlgebra.ιMulti K s w) / D) := by
  intro D
  have h129 := grassmann_no129_exterior_projection b a₀ w ha₀ hw hCompl
  have hD_ne : D ≠ 0 := h129.2.1
  have hupdate : ∀ (z : Fin r → K) (i : Fin r),
      ExteriorAlgebra.ιMulti K r (Function.update a₀ i (∑ j : Fin r, z j • a₀ j)) *
          ExteriorAlgebra.ιMulti K s w =
        z i • (ExteriorAlgebra.ιMulti K r a₀ * ExteriorAlgebra.ιMulti K s w) := fun z i => by
    rw [exterior_cramer_ιMulti a₀ z i, smul_mul_assoc]
  refine ⟨hD_ne, ?_, ?_⟩
  · intro x_free y_rem x_piv
    have hy_rem : y_rem ∈ Submodule.span K (Set.range a₀) :=
      Submodule.sub_mem _ hy (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (ha₁ k))
    rw [Submodule.mem_span_range_iff_exists_fun] at hy_rem
    obtain ⟨c, hc⟩ := hy_rem
    have hcoeff : ∀ i : Fin r, x_piv i = c i := fun i => by
      dsimp [x_piv]
      rw [← hc, hupdate c i, LinearMap.map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hD_ne]
    calc
      (∑ i : Fin r, x_piv i • a₀ i) + ∑ k : Fin s, x_free k • a₁ k
          = (∑ i : Fin r, c i • a₀ i) + ∑ k : Fin s, x_free k • a₁ k := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hcoeff i]
      _ = y_rem + ∑ k : Fin s, x_free k • a₁ k := by rw [hc]
      _ = y := sub_add_cancel y _
  · intro z_piv x_free
    let y_rem := y - ∑ k : Fin s, x_free k • a₁ k
    have hy_rem : y_rem ∈ Submodule.span K (Set.range a₀) :=
      Submodule.sub_mem _ hy (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (ha₁ k))
    rw [Submodule.mem_span_range_iff_exists_fun] at hy_rem
    obtain ⟨c, hc⟩ := hy_rem
    have hcoeff : ∀ i : Fin r,
        volCoord b (ExteriorAlgebra.ιMulti K r (Function.update a₀ i y_rem) *
          ExteriorAlgebra.ιMulti K s w) / D = c i := fun i => by
      rw [← hc, hupdate c i, LinearMap.map_smul, smul_eq_mul, mul_div_cancel_right₀ _ hD_ne]
    constructor
    · intro hsum i
      have hdiff : ∑ j : Fin r, (z_piv j - c j) • a₀ j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, hc]
        exact sub_eq_zero.mpr (eq_sub_of_add_eq hsum)
      have h0 : z_piv i - c i = 0 := Fintype.linearIndependent_iff.mp ha₀ (fun j => z_piv j - c j) hdiff i
      exact (sub_eq_zero.mp h0).trans (hcoeff i).symm
    · intro hz
      calc
        (∑ i : Fin r, z_piv i • a₀ i) + ∑ k : Fin s, x_free k • a₁ k
            = (∑ i : Fin r, c i • a₀ i) + ∑ k : Fin s, x_free k • a₁ k := by
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hz i, hcoeff i]
        _ = y_rem + ∑ k : Fin s, x_free k • a₁ k := by rw [hc]
        _ = y := sub_add_cancel y _

end Note44UnderdeterminedCramer

/-! ## 4. Grassmann No. 136: Exterior Polynomial Resultant (`Editorial Note 9`, `Seligman p. 395`) -/

section GrassmannNo136Resultant

/-- Truncated coefficient vector of a polynomial `P` in dimensions `0, ..., N - 1`. -/
def polyTruncVec {R : Type*} [Semiring R] (N : ℕ) (P : R[X]) : Fin N → R :=
  fun i => P.coeff i.val

/-- The `(m + n)` shifted polynomial multiples `{X^i g}_{i < m} ++ {X^j f}_{j < n}` as vectors in
`Fin (m + n) → R` (`Grassmann No. 136`, matching Mathlib's `Polynomial.sylvester` columns). -/
def sylvesterColumns {R : Type*} [Semiring R] (f g : R[X]) (m n : ℕ) :
    Fin (m + n) → (Fin (m + n) → R) :=
  Fin.addCases
    (fun j₁ : Fin m => polyTruncVec (m + n) (Polynomial.X ^ j₁.val * g))
    (fun j₂ : Fin n => polyTruncVec (m + n) (Polynomial.X ^ j₂.val * f))

/-- **Grassmann No. 136 (`Seligman p. 395`, `Editorial Note 9 pp. 332–333`)**:
over ANY commutative ring `R`, for `f.natDegree ≤ m` and `g.natDegree ≤ n`, the `(m + n)`-fold
exterior product of the shifted Sylvester columns equals `Polynomial.resultant f g m n` times the
canonical top volume blade of `R^{m+n}`. -/
theorem grassmann_no136_exterior_resultant {R : Type*} [CommRing R] (f g : R[X]) {m n : ℕ}
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    ExteriorAlgebra.ιMulti R (m + n) (sylvesterColumns f g m n) =
      Polynomial.resultant f g m n •
        (Pi.basisFun R (Fin (m + n))).ExteriorAlgebra Finset.univ := by
  let b := Pi.basisFun R (Fin (m + n))
  have hmat : b.toMatrix (sylvesterColumns f g m n) = Polynomial.sylvester f g m n := by
    ext i j
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    induction j using Fin.addCases with
    | left j₁ =>
      simp only [Polynomial.sylvester, sylvesterColumns, polyTruncVec, Fin.addCases_left,
        Matrix.of_apply, Polynomial.coeff_X_pow_mul', Set.mem_Icc]
      by_cases hi : j₁.val ≤ i.val <;> by_cases hin : i.val ≤ j₁.val + n <;> simp [hi, hin]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hg.trans_lt (by omega))
    | right j₂ =>
      simp only [Polynomial.sylvester, sylvesterColumns, polyTruncVec, Fin.addCases_right,
        Matrix.of_apply, Polynomial.coeff_X_pow_mul', Set.mem_Icc]
      by_cases hi : j₂.val ≤ i.val <;> by_cases him : i.val ≤ j₂.val + m <;> simp [hi, him]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hf.trans_lt (by omega))
  have hι := ιMulti_eq_det_smul_volume b (sylvesterColumns f g m n)
  rw [Module.Basis.det_apply, hmat] at hι
  exact hι

/-- Over ANY field `K`:
1. At exact polynomial degrees `(f.natDegree, g.natDegree)`, the exterior product of the
   Sylvester columns vanishes iff `f` and `g` fail to be coprime (and are not both zero).
2. At arbitrary degree bounds `f.natDegree ≤ m`, `g.natDegree ≤ n` with `0 < m ∨ 0 < n`, if `f`
   and `g` share a root `r : K`, the exterior product `ιMulti K (m + n) (sylvesterColumns f g m n)`
   vanishes. -/
theorem grassmann_no136_exterior_resultant_eq_zero_iff {K : Type*} [Field K] (f g : K[X]) :
    (ExteriorAlgebra.ιMulti K (f.natDegree + g.natDegree)
        (sylvesterColumns f g f.natDegree g.natDegree) = 0 ↔
      (f ≠ 0 ∨ g ≠ 0) ∧ ¬ IsCoprime f g) ∧
      ∀ {m n : ℕ}, f.natDegree ≤ m → g.natDegree ≤ n → (m ≠ 0 ∨ n ≠ 0) →
        ∀ r : K, Polynomial.IsRoot f r → Polynomial.IsRoot g r →
          ExteriorAlgebra.ιMulti K (m + n) (sylvesterColumns f g m n) = 0 := by
  refine ⟨?_, ?_⟩
  · let b := Pi.basisFun K (Fin (f.natDegree + g.natDegree))
    rw [grassmann_no136_exterior_resultant f g le_rfl le_rfl,
      smul_eq_zero_iff_left (b.ExteriorAlgebra.ne_zero Finset.univ)]
    exact Polynomial.resultant_eq_zero_iff
  · intro m n hf hg hmn r hfr hgr
    rw [grassmann_no136_exterior_resultant f g hf hg]
    suffices hres : Polynomial.resultant f g m n = 0 by rw [hres, zero_smul]
    obtain ⟨p, q, _, _, he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hmn
    have hev := congrArg (Polynomial.eval r) he
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.IsRoot.def.mp hfr, Polynomial.IsRoot.def.mp hgr, zero_mul, add_zero] at hev
    exact hev.symm

end GrassmannNo136Resultant

/-! ## 5. Notes 49, 52, 53: Unit Cancellation (`No. 149`) & Normal vs. Completely Normal Subspaces -/

section Notes49_52_53NormalSubspaces

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **Editorial Note 49 (`No. 149, p. 350`) — Unit Factor Inner-Product Cancellation**:
1. Basis-unit form: if `sE` is disjoint from both `sF` and `sG`,
   `[e_E ∧ e_F | e_E ∧ e_G] = [e_F | e_G]`.
2. General orthogonal-vector form: if `u` is `extInner b`-orthogonal to every coordinate of `X`
   (`contractLeft (b.toDualEquiv u) X = 0`), then `[ι u * X | ι u * Y] = [u | u] * [X | Y]`. -/
theorem note49_extInner_unit_factor_cancel {n : ℕ} (b : Module.Basis (Fin n) K V) :
    (∀ sE sF sG : Finset (Fin n), Disjoint sE sF → Disjoint sE sG →
      extInner b (b.ExteriorAlgebra sE * b.ExteriorAlgebra sF)
          (b.ExteriorAlgebra sE * b.ExteriorAlgebra sG) =
        extInner b (b.ExteriorAlgebra sF) (b.ExteriorAlgebra sG)) ∧
      (∀ (u : V) (X Y : ExteriorAlgebra K V),
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b.toDualEquiv u) X = 0 →
          extInner b (ExteriorAlgebra.ι K u * X) (ExteriorAlgebra.ι K u * Y) =
            extInner b (ExteriorAlgebra.ι K u) (ExteriorAlgebra.ι K u) * extInner b X Y) := by
  refine ⟨?_, ?_⟩
  · intro sE sF sG hEF hEG
    let pE := Set.powersetCard.ofCard (s := sE) rfl
    let pF := Set.powersetCard.ofCard (s := sF) rfl
    let pG := Set.powersetCard.ofCard (s := sG) rfl
    have hEF' : Disjoint (pE : Finset (Fin n)) (pF : Finset (Fin n)) := hEF
    have hEG' : Disjoint (pE : Finset (Fin n)) (pG : Finset (Fin n)) := hEG
    have hm1 := ExteriorAlgebra.basis_mul_of_disjoint b pE pF hEF'
    have hm2 := ExteriorAlgebra.basis_mul_of_disjoint b pE pG hEG'
    have hu1 : b.ExteriorAlgebra (Set.powersetCard.disjUnion hEF') =
        b.ExteriorAlgebra (sE.disjUnion sF hEF) := rfl
    have hu2 : b.ExteriorAlgebra (Set.powersetCard.disjUnion hEG') =
        b.ExteriorAlgebra (sE.disjUnion sG hEG) := rfl
    change extInner b (b.ExteriorAlgebra ↑pE * b.ExteriorAlgebra ↑pF)
      (b.ExteriorAlgebra ↑pE * b.ExteriorAlgebra ↑pG) = _
    rw [hm1, hm2, hu1, hu2, Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul K,
      ← Int.cast_smul_eq_zsmul K, extInner_smul_left, extInner_smul_right,
      extInner_basis, extInner_basis]
    have hiff : sE.disjUnion sF hEF = sE.disjUnion sG hEG ↔ sF = sG := by
      constructor
      · intro h
        ext x
        by_cases hx : x ∈ sE
        · have hxF : x ∉ sF := Finset.disjoint_left.mp hEF hx
          have hxG : x ∉ sG := Finset.disjoint_left.mp hEG hx
          simp [hxF, hxG]
        · have hmem := Finset.ext_iff.mp h x
          simpa [Finset.mem_disjUnion, hx] using hmem
      · intro h; subst h; rfl
    by_cases hFG : sF = sG
    · subst hFG
      rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
      have hperm : Set.powersetCard.permOfDisjoint hEG' = Set.powersetCard.permOfDisjoint hEF' := rfl
      rw [hperm, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    · have hne : sE.disjUnion sF hEF ≠ sE.disjUnion sG hEG := fun h => hFG (hiff.mp h)
      rw [ite_eq_right hne, ite_eq_right hFG, mul_zero, mul_zero]
  · intro u X Y hcX
    rw [extInner_ι_mul_left b u X (ExteriorAlgebra.ι K u * Y)]
    have hι0 : CliffordAlgebra.ι (0 : QuadraticForm K V) u = ExteriorAlgebra.ι K u := rfl
    have hcl := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm K V))
      (b.toDualEquiv u) u Y
    rw [hι0] at hcl
    rw [hcl, map_sub, extInner_smul_right, toDualEquiv_eq_extInner_pub b u u]
    have hzero : extInner b X
        (ExteriorAlgebra.ι K u * CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V))
          (b.toDualEquiv u) Y) = 0 := by
      rw [extInner_symm, extInner_ι_mul_left, hcX, LinearMap.map_zero]
    rw [hzero, sub_zero]

/-- Two frames are **completely normal** (`Notes 52–53, p. 351`) when every vector in `span u`
is `extInner b`-orthogonal to every vector in `span v`. -/
def IsCompletelyNormal {n m q : ℕ} (b : Module.Basis (Fin n) K V)
    (u : Fin m → V) (v : Fin q → V) : Prop :=
  ∀ x ∈ Submodule.span K (Set.range u), ∀ y ∈ Submodule.span K (Set.range v),
    extInner b (ExteriorAlgebra.ι K x) (ExteriorAlgebra.ι K y) = 0

/-- Two frames are **normal in the sense of No. 152** when `ιMulti m u * ★(ιMulti q v) = 0`. -/
def IsNormalNo152 {n m q : ℕ} (b : Module.Basis (Fin n) K V)
    (u : Fin m → V) (v : Fin q → V) : Prop :=
  ExteriorAlgebra.ιMulti K m u * hodge b (ExteriorAlgebra.ιMulti K q v) = 0

/-- **Editorial Notes 52 & 53 (`pp. 351–353`), Theorems 1–3**:
1. **Theorem 2**: `IsCompletelyNormal b u v ↔ span u ≤ bladeSupport (hodge b (ιMulti K q v))`.
2. **Theorem 1**: for `1 ≤ m`, `IsCompletelyNormal b u v → IsNormalNo152 b u v`.
3. **Theorem 3**: for `m = 1` (vector–blade pair), `IsNormalNo152 b u v ↔ IsCompletelyNormal b u v`. -/
theorem notes52_53_completely_normal_theorems {n m q : ℕ} (b : Module.Basis (Fin n) K V)
    (u : Fin m → V) (v : Fin q → V) (hv : LinearIndependent K v) :
    (IsCompletelyNormal b u v ↔
        Submodule.span K (Set.range u) ≤ bladeSupport (hodge b (ExteriorAlgebra.ιMulti K q v))) ∧
      (1 ≤ m → IsCompletelyNormal b u v → IsNormalNo152 b u v) ∧
      (m = 1 → (IsNormalNo152 b u v ↔ IsCompletelyNormal b u v)) := by
  have hsup := (note29_thm2_hodge_blade_decomposable_and_support b v hv).2.2
  have h2 : IsCompletelyNormal b u v ↔
      Submodule.span K (Set.range u) ≤ bladeSupport (hodge b (ExteriorAlgebra.ιMulti K q v)) := by
    constructor
    · intro hcn x hx
      rw [hsup x]
      intro y hy
      rw [extInner_symm]
      exact hcn x hx y hy
    · intro hle x hx y hy
      rw [extInner_symm]
      exact (hsup x).mp (hle hx) y hy
  have h1 : ∀ (m' : ℕ) (u' : Fin m' → V), 1 ≤ m' →
      IsCompletelyNormal b u' v → IsNormalNo152 b u' v := fun m' u' hm' hcn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm')
    have hle : Submodule.span K (Set.range u') ≤
        bladeSupport (hodge b (ExteriorAlgebra.ιMulti K q v)) := by
      intro x hx
      rw [hsup x]
      intro y hy
      rw [extInner_symm]
      exact hcn x hx y hy
    have h0mem : u' 0 ∈ bladeSupport (hodge b (ExteriorAlgebra.ιMulti K q v)) :=
      hle (Submodule.subset_span ⟨0, rfl⟩)
    rw [mem_bladeSupport] at h0mem
    have hcomm := exteriorPower_mul_comm (ExteriorAlgebra.ιMulti_range K k ⟨Matrix.vecTail u', rfl⟩)
      (hodge_mem_exteriorPower b (ExteriorAlgebra.ιMulti_range K q ⟨v, rfl⟩))
    have hswap : ExteriorAlgebra.ιMulti K k (Matrix.vecTail u') *
        hodge b (ExteriorAlgebra.ιMulti K q v) =
        ((-1 : K) ^ (k * (n - q))) •
          (hodge b (ExteriorAlgebra.ιMulti K q v) *
            ExteriorAlgebra.ιMulti K k (Matrix.vecTail u')) := hcomm
    dsimp [IsNormalNo152]
    rw [ExteriorAlgebra.ιMulti_succ_apply, mul_assoc, hswap, mul_smul_comm, ← mul_assoc, h0mem,
      zero_mul, smul_zero]
  refine ⟨h2, fun hm hcn => h1 m u hm hcn, fun hm => ?_⟩
  subst hm
  refine ⟨fun hnorm => h2.mpr ?_, fun hcn => h1 1 u le_rfl hcn⟩
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Fin.eq_zero i, SetLike.mem_coe, mem_bladeSupport]
  have hu1 : ExteriorAlgebra.ιMulti K 1 u = ExteriorAlgebra.ι K (u 0) := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rwa [IsNormalNo152, hu1] at hnorm

/-- **`[countermodel_found]` — Editorial Notes 52–53 (`pp. 351–353`)**:
in `ℝ³`, `A = e₀ ∧ e₁` and `B = e₀ ∧ e₂` satisfy `[A | B] = 0` and `IsNormalNo152 b u v`
(`A * ★B = 0`), yet are NOT completely normal (`e₀` lies in both planes with `[e₀ | e₀] = 1 ≠ 0`). -/
theorem notes52_53_normal_not_completely_normal_dim3 :
    let b := Pi.basisFun ℝ (Fin 3)
    let u : Fin 2 → (Fin 3 → ℝ) := ![b 0, b 1]
    let v : Fin 2 → (Fin 3 → ℝ) := ![b 0, b 2]
    extInner b (ExteriorAlgebra.ιMulti ℝ 2 u) (ExteriorAlgebra.ιMulti ℝ 2 v) = 0 ∧
      IsNormalNo152 b u v ∧ ¬ IsCompletelyNormal b u v := by
  intro b u v
  have h01 : ExteriorAlgebra.ιMulti ℝ 2 u = ExteriorAlgebra.ι ℝ (b 0) * ExteriorAlgebra.ι ℝ (b 1) := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl
  have h02 : ExteriorAlgebra.ιMulti ℝ 2 v = ExteriorAlgebra.ι ℝ (b 0) * ExteriorAlgebra.ι ℝ (b 2) := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl
  have hdeg01 : ExteriorAlgebra.ιMulti ℝ 2 u ∈ ⋀[ℝ]^2 (Fin 3 → ℝ) :=
    ExteriorAlgebra.ιMulti_range ℝ 2 ⟨u, rfl⟩
  have hdeg02 : ExteriorAlgebra.ιMulti ℝ 2 v ∈ ⋀[ℝ]^2 (Fin 3 → ℝ) :=
    ExteriorAlgebra.ιMulti_range ℝ 2 ⟨v, rfl⟩
  have hb00 : extInner b (ExteriorAlgebra.ι ℝ (b 0)) (ExteriorAlgebra.ι ℝ (b 0)) = 1 := by
    rw [← toDualEquiv_eq_extInner_pub b (b 0) (b 0)]
    have hd : b.toDualEquiv (b 0) = b.dualBasis 0 := b.map_apply b.toDualEquiv 0
    rw [hd, b.dualBasis_apply_self, ite_eq_left rfl]
  have hb_orth : ∀ i j : Fin 3, i ≠ j →
      extInner b (ExteriorAlgebra.ι ℝ (b i)) (ExteriorAlgebra.ι ℝ (b j)) = 0 := fun i j hij => by
    rw [← toDualEquiv_eq_extInner_pub b (b i) (b j)]
    have hd : b.toDualEquiv (b i) = b.dualBasis i := b.map_apply b.toDualEquiv i
    rw [hd, b.dualBasis_apply_self, ite_eq_right (Ne.symm hij)]
  have hinner0 : extInner b (ExteriorAlgebra.ιMulti ℝ 2 u) (ExteriorAlgebra.ιMulti ℝ 2 v) = 0 := by
    rw [h01, h02, note69_binet_cauchy_two_blades, hb00, hb_orth 1 2 (by decide),
      hb_orth 0 2 (by decide), mul_zero, zero_mul, sub_zero]
  have hnorm : IsNormalNo152 b u v := by
    dsimp [IsNormalNo152]
    have hhc : hodge b (ExteriorAlgebra.ιMulti ℝ 2 v) ∈ ⋀[ℝ]^1 (Fin 3 → ℝ) := by
      simpa using hodge_mem_exteriorPower b hdeg02
    have htop : ExteriorAlgebra.ιMulti ℝ 2 u * hodge b (ExteriorAlgebra.ιMulti ℝ 2 v) ∈
        ⋀[ℝ]^3 (Fin 3 → ℝ) := by
      change ExteriorAlgebra.ιMulti ℝ 2 u * hodge b (ExteriorAlgebra.ιMulti ℝ 2 v) ∈
        (LinearMap.range (ExteriorAlgebra.ι ℝ)) ^ (2 + 1)
      rw [pow_add]
      exact Submodule.mul_mem_mul hdeg01 hhc
    have hsm := eq_volCoord_smul_volume b htop
    have hvc : volCoord b (ExteriorAlgebra.ιMulti ℝ 2 u * hodge b (ExteriorAlgebra.ιMulti ℝ 2 v)) = 0 :=
      hinner0
    rwa [hvc, zero_smul] at hsm
  refine ⟨hinner0, hnorm, fun hcn => ?_⟩
  have h0u : b 0 ∈ Submodule.span ℝ (Set.range u) := Submodule.subset_span ⟨0, rfl⟩
  have h0v : b 0 ∈ Submodule.span ℝ (Set.range v) := Submodule.subset_span ⟨0, rfl⟩
  have h0 := hcn (b 0) h0u (b 0) h0v
  rw [hb00] at h0
  exact one_ne_zero h0

end Notes49_52_53NormalSubspaces

/-! ## 6. Editorial Note 62: Orthonormal Uniqueness of Supplement (`pp. 354–355`) -/

section Note62OrthonormalSupplement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem dualTransferEquiv_eq_iff {n : ℕ} (e a : Module.Basis (Fin n) K V) :
    dualTransferEquiv a = dualTransferEquiv e ↔
      ∀ k : Fin n, dualTransferEquiv a (ExteriorAlgebra.ι K (a k)) =
        dualTransferEquiv e (ExteriorAlgebra.ι K (a k)) := by
  constructor
  · intro h k
    rw [h]
  · intro hk
    have hι : ∀ v : V, dualTransferEquiv a (ExteriorAlgebra.ι K v) =
        dualTransferEquiv e (ExteriorAlgebra.ι K v) := fun v => by
      have hv : v = ∑ k : Fin n, a.repr v k • a k := (a.sum_repr v).symm
      rw [hv]
      simp only [map_sum, map_smul, hk]
    have hAlg : ExteriorAlgebra.map a.toDualEquiv.toLinearMap =
        ExteriorAlgebra.map e.toDualEquiv.toLinearMap := by
      apply ExteriorAlgebra.hom_ext
      apply LinearMap.ext
      intro v
      exact hι v
    ext x
    change ExteriorAlgebra.map a.toDualEquiv.toLinearMap x =
      ExteriorAlgebra.map e.toDualEquiv.toLinearMap x
    rw [hAlg]

/-- **Editorial Note 62 (`pp. 354–355`) — Uniqueness of Complete Normal (Orthonormal) Systems
Preserving the Supplement**:
given a reference basis `e` and any unimodular basis `a` (`e.det a = 1`), `hodge a = hodge e`
(equivalently `∀ k, hodge a (ι (a k)) = hodge e (ι (a k))`) holds if and only if `a` is
`extInner e`-orthonormal. -/
theorem note62_hodge_eq_iff_orthonormal {n : ℕ} (e a : Module.Basis (Fin n) K V)
    (hdet : e.det a = 1) :
    (hodge a = hodge e ↔
        ∀ k : Fin n,
          hodge a (ExteriorAlgebra.ι K (a k)) = hodge e (ExteriorAlgebra.ι K (a k))) ∧
      ((∀ k : Fin n,
          hodge a (ExteriorAlgebra.ι K (a k)) = hodge e (ExteriorAlgebra.ι K (a k))) ↔
        ∀ j k : Fin n,
          extInner e (ExteriorAlgebra.ι K (a j)) (ExteriorAlgebra.ι K (a k)) =
            if j = k then 1 else 0) := by
  have hpe_eq : poincareEval a = poincareEval e := by
    apply LinearMap.ext
    intro x
    rw [poincareEval_change_basis e a x, hdet, one_smul]
  have hh_apply : ∀ x : ExteriorAlgebra K V,
      hodge a x = poincareEquiv e (dualTransferEquiv a x) := fun x => by
    have h1 := LinearMap.congr_fun (poincareEval_comp_dualTransferEquiv a) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hpe_eq] at h1
    rw [← h1, poincareEquiv_apply]
  have hh_e : ∀ x : ExteriorAlgebra K V,
      hodge e x = poincareEquiv e (dualTransferEquiv e x) := fun x => by
    have h1 := LinearMap.congr_fun (poincareEval_comp_dualTransferEquiv e) x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1
    rw [← h1, poincareEquiv_apply]
  have h1 : hodge a = hodge e ↔
      ∀ k : Fin n, hodge a (ExteriorAlgebra.ι K (a k)) = hodge e (ExteriorAlgebra.ι K (a k)) := by
    have hfull : hodge a = hodge e ↔ dualTransferEquiv a = dualTransferEquiv e := by
      constructor
      · intro h
        ext x
        apply (poincareEquiv e).injective
        rw [← hh_apply x, ← hh_e x, h]
      · intro h
        ext x
        rw [hh_apply x, hh_e x, h]
    have hvec : (∀ k : Fin n, hodge a (ExteriorAlgebra.ι K (a k)) =
        hodge e (ExteriorAlgebra.ι K (a k))) ↔
        ∀ k : Fin n, dualTransferEquiv a (ExteriorAlgebra.ι K (a k)) =
          dualTransferEquiv e (ExteriorAlgebra.ι K (a k)) := by
      refine forall_congr' fun k => ?_
      constructor
      · intro h
        apply (poincareEquiv e).injective
        rw [← hh_apply, ← hh_e, h]
      · intro h
        rw [hh_apply, hh_e, h]
    exact hfull.trans ((dualTransferEquiv_eq_iff e a).trans hvec.symm)
  refine ⟨h1, ?_⟩
  constructor
  · intro hk j k
    have hd : dualTransferEquiv a (ExteriorAlgebra.ι K (a k)) =
        dualTransferEquiv e (ExteriorAlgebra.ι K (a k)) := by
      apply (poincareEquiv e).injective
      rw [← hh_apply, ← hh_e, hk k]
    have hι : ExteriorAlgebra.ι K (a.toDualEquiv (a k)) =
        ExteriorAlgebra.ι K (e.toDualEquiv (a k)) := by
      change ExteriorAlgebra.map a.toDualEquiv.toLinearMap (ExteriorAlgebra.ι K (a k)) =
        ExteriorAlgebra.map e.toDualEquiv.toLinearMap (ExteriorAlgebra.ι K (a k)) at hd
      simpa only [ExteriorAlgebra.map_apply_ι, LinearEquiv.coe_coe] using hd
    rw [ExteriorAlgebra.ι_inj] at hι
    have hev := LinearMap.congr_fun hι (a j)
    have hl : (a.toDualEquiv (a k)) (a j) = if j = k then 1 else 0 := by
      have ha : a.toDualEquiv (a k) = a.dualBasis k := a.map_apply a.toDualEquiv k
      rw [ha, a.dualBasis_apply_self]
    have hr : (e.toDualEquiv (a k)) (a j) =
        extInner e (ExteriorAlgebra.ι K (a j)) (ExteriorAlgebra.ι K (a k)) := by
      rw [toDualEquiv_eq_extInner_pub e (a k) (a j), extInner_symm]
    rw [hl, hr] at hev
    exact hev.symm
  · intro hortho k
    rw [hh_apply, hh_e]
    congr 1
    change ExteriorAlgebra.map a.toDualEquiv.toLinearMap (ExteriorAlgebra.ι K (a k)) =
      ExteriorAlgebra.map e.toDualEquiv.toLinearMap (ExteriorAlgebra.ι K (a k))
    rw [ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
    congr 1
    apply a.ext
    intro j
    simp only [LinearEquiv.coe_coe]
    have ha : a.toDualEquiv (a k) = a.dualBasis k := a.map_apply a.toDualEquiv k
    rw [ha, a.dualBasis_apply_self, toDualEquiv_eq_extInner_pub e (a k) (a j), extInner_symm,
      hortho j k]

end Note62OrthonormalSupplement

/-! ## 7. Editorial Note 69: Orthonormal Subspace Bases & Exterior Hadamard Inequality (`pp. 358–359`) -/

section Note69HadamardInequality

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Euclidean inner product on vectors extracted from `extInner b`. -/
def vecInner {n : ℕ} (b : Module.Basis (Fin n) ℝ V) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun x y => extInner b (ExteriorAlgebra.ι ℝ x) (ExteriorAlgebra.ι ℝ y))
    (fun x₁ x₂ y => by simp only [map_add, LinearMap.add_apply])
    (fun r x y => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul])
    (fun x y₁ y₂ => by simp only [map_add])
    (fun r x y => by simp only [map_smul])

@[simp] theorem vecInner_apply {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (x y : V) :
    vecInner b x y = extInner b (ExteriorAlgebra.ι ℝ x) (ExteriorAlgebra.ι ℝ y) :=
  rfl

theorem vecInner_pos_def {n : ℕ} (b : Module.Basis (Fin n) ℝ V) (x : V) :
    0 ≤ vecInner b x x ∧ (vecInner b x x = 0 ↔ x = 0) := by
  have hcs := note68_extInner_cauchy_schwarz b (ExteriorAlgebra.ι ℝ x) (ExteriorAlgebra.ι ℝ x)
  refine ⟨hcs.1, ?_⟩
  rw [vecInner_apply, hcs.2.1, ExteriorAlgebra.ι_eq_zero_iff]

theorem vecInner_isSymm {n : ℕ} (b : Module.Basis (Fin n) ℝ V) : (vecInner b).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun _x _y => extInner_symm b _ _

private theorem exists_orthonormal_basis_of_submodule {n : ℕ} (b : Module.Basis (Fin n) ℝ V)
    (W : Submodule ℝ V) :
    ∃ (k : ℕ) (w : Fin k → V),
      LinearIndependent ℝ w ∧
      Submodule.span ℝ (Set.range w) = W ∧
      (∀ i j : Fin k, extInner b (ExteriorAlgebra.ι ℝ (w i)) (ExteriorAlgebra.ι ℝ (w j)) =
        if i = j then 1 else 0) := by
  have : Module.Finite ℝ V := Module.Finite.of_basis b
  let BW : LinearMap.BilinForm ℝ W := (vecInner b).restrict W
  have hBW_symm : LinearMap.IsSymm BW :=
    LinearMap.BilinForm.isSymm_iff.mp (LinearMap.BilinForm.isSymm_def.mpr fun x y => by
      change vecInner b (x : V) (y : V) = vecInner b (y : V) (x : V)
      exact extInner_symm b _ _)
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨b₀, hb₀_ortho⟩ := LinearMap.BilinForm.exists_orthogonal_basis hBW_symm
  have hdiag_pos : ∀ i : Fin (Module.finrank ℝ W), 0 < BW (b₀ i) (b₀ i) := fun i => by
    have hne : (b₀ i : V) ≠ 0 := fun h0 => b₀.ne_zero i (Subtype.ext h0)
    have hpd := vecInner_pos_def b (b₀ i : V)
    exact lt_of_le_of_ne hpd.1 (Ne.symm (mt hpd.2.mp hne))
  let sc : Fin (Module.finrank ℝ W) → ℝˣ := fun i =>
    Units.mk0 (Real.sqrt (BW (b₀ i) (b₀ i)))⁻¹
      (inv_ne_zero (Real.sqrt_ne_zero'.mpr (hdiag_pos i)))
  let b₁ : Module.Basis (Fin (Module.finrank ℝ W)) ℝ W := b₀.unitsSMul sc
  let w : Fin (Module.finrank ℝ W) → V := fun i => (b₁ i : V)
  have hw_li : LinearIndependent ℝ w :=
    b₁.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hw_span : Submodule.span ℝ (Set.range w) = W := by
    rw [show Set.range w = W.subtype '' Set.range b₁ from Set.range_comp _ _,
      ← Submodule.map_span, b₁.span_eq, Submodule.map_subtype_top]
  refine ⟨Module.finrank ℝ W, w, hw_li, hw_span, fun i j => ?_⟩
  change BW (b₁ i) (b₁ j) = if i = j then 1 else 0
  simp only [b₁, Module.Basis.unitsSMul_apply, Units.smul_def, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl]
    have hd_pos := hdiag_pos i
    have hsq : Real.sqrt (BW (b₀ i) (b₀ i)) * Real.sqrt (BW (b₀ i) (b₀ i)) = BW (b₀ i) (b₀ i) :=
      Real.mul_self_sqrt hd_pos.le
    calc
      (sc i : ℝ) * ((sc i : ℝ) * BW (b₀ i) (b₀ i))
          = ((Real.sqrt (BW (b₀ i) (b₀ i)))⁻¹ * (Real.sqrt (BW (b₀ i) (b₀ i)))⁻¹) *
              BW (b₀ i) (b₀ i) := by simp [sc, mul_assoc]
      _ = (Real.sqrt (BW (b₀ i) (b₀ i)) * Real.sqrt (BW (b₀ i) (b₀ i)))⁻¹ *
              BW (b₀ i) (b₀ i) := by rw [← mul_inv_rev]
      _ = (BW (b₀ i) (b₀ i))⁻¹ * BW (b₀ i) (b₀ i) := by rw [hsq]
      _ = 1 := inv_mul_cancel₀ hd_pos.ne'
  · rw [ite_eq_right hij]
    have ho : BW (b₀ i) (b₀ j) = 0 := hb₀_ortho hij
    rw [ho, mul_zero, mul_zero]

private theorem contractLeft_ιMulti_eq_zero_of_ortho {n m : ℕ} (b : Module.Basis (Fin n) ℝ V)
    (u : V) (v : Fin m → V)
    (ho : ∀ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ u) (ExteriorAlgebra.ι ℝ (v i)) = 0) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V)) (b.toDualEquiv u)
        (ExteriorAlgebra.ιMulti ℝ m v) = 0 := by
  induction m with
  | zero => simp [CliffordAlgebra.contractLeft_one]
  | succ m ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    have hι0 : CliffordAlgebra.ι (0 : QuadraticForm ℝ V) (v 0) = ExteriorAlgebra.ι ℝ (v 0) := rfl
    have hcl := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm ℝ V))
      (b.toDualEquiv u) (v 0) (ExteriorAlgebra.ιMulti ℝ m (Matrix.vecTail v))
    rw [hι0] at hcl
    have hdu0 : (b.toDualEquiv u) (v 0) = 0 := by
      rw [toDualEquiv_eq_extInner_pub]
      exact ho 0
    have htail : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V)) (b.toDualEquiv u)
        (ExteriorAlgebra.ιMulti ℝ m (Matrix.vecTail v)) = 0 :=
      ih (Matrix.vecTail v) (fun i => ho i.succ)
    rw [hcl, hdu0, zero_smul, zero_sub, htail, mul_zero, neg_zero]

/-- **Editorial Note 69 (`pp. 358–359`) — Exterior Hadamard Inequality & Orthogonality Characterization**:
for ANY `m : ℕ` and vectors `v : Fin m → V`:
1. `‖v₀ ∧ ⋯ ∧ v_{m-1}‖² ≤ ∏ i, ‖v_i‖²`.
2. Pairwise orthogonality implies exact equality `‖v₀ ∧ ⋯ ∧ v_{m-1}‖² = ∏ i, ‖v_i‖²`.
3. When all `v i ≠ 0`, equality holds iff the `v i` are pairwise `extInner b`-orthogonal. -/
theorem note69_exterior_hadamard_inequality {n : ℕ} (b : Module.Basis (Fin n) ℝ V) :
    ∀ (m : ℕ) (v : Fin m → V),
      extInner b (ExteriorAlgebra.ιMulti ℝ m v) (ExteriorAlgebra.ιMulti ℝ m v) ≤
          ∏ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v i)) ∧
        ((∀ i j : Fin m, i ≠ j →
            extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v j)) = 0) →
          extInner b (ExteriorAlgebra.ιMulti ℝ m v) (ExteriorAlgebra.ιMulti ℝ m v) =
            ∏ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v i))) ∧
        ((∀ i : Fin m, v i ≠ 0) →
          (extInner b (ExteriorAlgebra.ιMulti ℝ m v) (ExteriorAlgebra.ιMulti ℝ m v) =
              ∏ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v i)) ↔
            ∀ i j : Fin m, i ≠ j →
              extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v j)) = 0)) := by
  intro m
  induction m with
  | zero =>
    intro v
    have h1 : extInner b 1 (1 : ExteriorAlgebra ℝ V) = 1 := by
      calc
        extInner b 1 (1 : ExteriorAlgebra ℝ V) =
            extInner b (b.ExteriorAlgebra ∅) (b.ExteriorAlgebra ∅) := by
              simp only [basis_empty]
        _ = 1 := by rw [extInner_basis, ite_eq_left rfl]
    refine ⟨?_, ?_, ?_⟩
    · simp [ExteriorAlgebra.ιMulti_zero_apply, h1]
    · intro _; simp [ExteriorAlgebra.ιMulti_zero_apply, h1]
    · intro _; constructor
      · intro _ i; exact Fin.elim0 i
      · intro _; simp [ExteriorAlgebra.ιMulti_zero_apply, h1]
  | succ m ih =>
    intro v
    let x₀ : V := v 0
    let v' : Fin m → V := Matrix.vecTail v
    let W := Submodule.span ℝ (Set.range v')
    have ih' := ih v'
    have hprod_nonneg : ∀ i : Fin (m + 1),
        0 ≤ extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v i)) := fun i =>
      (vecInner_pos_def b (v i)).1
    have hprod_succ :
        (∏ i : Fin (m + 1), extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v i))) =
          extInner b (ExteriorAlgebra.ι ℝ x₀) (ExteriorAlgebra.ι ℝ x₀) *
            ∏ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ (v' i)) (ExteriorAlgebra.ι ℝ (v' i)) :=
      Fin.prod_univ_succ _
    by_cases hv' : LinearIndependent ℝ v'
    · obtain ⟨k, w_orth, hw_li, hw_span, hw_ortho⟩ := exists_orthonormal_basis_of_submodule b W
      let projW : V := ∑ j : Fin k,
        vecInner b x₀ (w_orth j) • w_orth j
      let perpW : V := x₀ - projW
      have hprojW_mem : projW ∈ W :=
        Submodule.sum_mem _ fun j _ =>
          Submodule.smul_mem _ _ (hw_span ▸ Submodule.subset_span ⟨j, rfl⟩)
      have hperp_w : ∀ j : Fin k,
          vecInner b perpW (w_orth j) = 0 := fun j => by
        change vecInner b (x₀ - ∑ r : Fin k, vecInner b x₀ (w_orth r) • w_orth r) (w_orth j) = 0
        rw [LinearMap.map_sub₂, LinearMap.map_sum₂, Finset.sum_eq_single j]
        · simp only [LinearMap.map_smul₂, vecInner_apply, hw_ortho j j, ite_true,
            smul_eq_mul, mul_one, sub_self]
        · intro r _ hri
          simp only [LinearMap.map_smul₂, vecInner_apply, hw_ortho r j, ite_eq_right hri, smul_zero]
        · intro hj
          exact (hj (Finset.mem_univ j)).elim
      have hperp_W : ∀ y ∈ W,
          vecInner b perpW y = 0 := fun y hy => by
        rw [← hw_span] at hy
        refine Submodule.span_induction (p := fun y _ =>
          vecInner b perpW y = 0) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨j, rfl⟩; exact hperp_w j
        · exact LinearMap.map_zero _
        · intro a c _ _ ha hc; rw [map_add, ha, hc, add_zero]
        · intro r a _ ha; rw [map_smul, ha, smul_zero]
      have hx_split : vecInner b x₀ x₀ =
          vecInner b perpW perpW + vecInner b projW projW := by
        have hx : x₀ = perpW + projW := (sub_add_cancel x₀ projW).symm
        conv_lhs => rw [hx, LinearMap.map_add₂, map_add, map_add]
        have hpp : vecInner b perpW projW = 0 := hperp_W projW hprojW_mem
        have hpp' : vecInner b projW perpW = 0 := by
          rw [vecInner_apply, extInner_symm]
          exact hpp
        rw [hpp, hpp', add_zero, zero_add]
      have hperp_le : extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) ≤
          extInner b (ExteriorAlgebra.ι ℝ x₀) (ExteriorAlgebra.ι ℝ x₀) := by
        have hp_nn := (vecInner_pos_def b projW).1
        have hsp : extInner b (ExteriorAlgebra.ι ℝ x₀) (ExteriorAlgebra.ι ℝ x₀) =
            extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) +
              extInner b (ExteriorAlgebra.ι ℝ projW) (ExteriorAlgebra.ι ℝ projW) := hx_split
        rw [vecInner_apply] at hp_nn
        linarith
      have hwedge_eq : ExteriorAlgebra.ιMulti ℝ (m + 1) v =
          ExteriorAlgebra.ι ℝ perpW * ExteriorAlgebra.ιMulti ℝ m v' := by
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        have hx : x₀ = perpW + projW := (sub_add_cancel x₀ projW).symm
        change ExteriorAlgebra.ι ℝ x₀ * ExteriorAlgebra.ιMulti ℝ m v' = _
        rw [hx, map_add, add_mul, (ι_mul_ιMulti_eq_zero_iff v' hv' projW).mpr hprojW_mem, add_zero]
      have hnorm_factor : extInner b (ExteriorAlgebra.ιMulti ℝ (m + 1) v)
          (ExteriorAlgebra.ιMulti ℝ (m + 1) v) =
          extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) *
            extInner b (ExteriorAlgebra.ιMulti ℝ m v') (ExteriorAlgebra.ιMulti ℝ m v') := by
        rw [hwedge_eq, extInner_ι_mul_left b perpW]
        have hι0 : CliffordAlgebra.ι (0 : QuadraticForm ℝ V) perpW = ExteriorAlgebra.ι ℝ perpW := rfl
        have hcl := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm ℝ V))
          (b.toDualEquiv perpW) perpW (ExteriorAlgebra.ιMulti ℝ m v')
        rw [hι0] at hcl
        have hcon0 := contractLeft_ιMulti_eq_zero_of_ortho b perpW v' fun i =>
          hperp_W (v' i) (Submodule.subset_span ⟨i, rfl⟩)
        rw [hcl, hcon0, mul_zero, sub_zero, extInner_smul_right, toDualEquiv_eq_extInner_pub]
      have h_ineq : extInner b (ExteriorAlgebra.ιMulti ℝ (m + 1) v)
          (ExteriorAlgebra.ιMulti ℝ (m + 1) v) ≤
          ∏ i : Fin (m + 1), extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v i)) := by
        rw [hnorm_factor, hprod_succ]
        exact mul_le_mul hperp_le ih'.1
          (note68_extInner_cauchy_schwarz b (ExteriorAlgebra.ιMulti ℝ m v') (ExteriorAlgebra.ιMulti ℝ m v')).1
          (vecInner_pos_def b x₀).1
      have hproj_iff : projW = 0 ↔ ∀ i : Fin m,
          vecInner b x₀ (v' i) = 0 := by
        constructor
        · intro hp0 i
          have hp_eq : perpW = x₀ := by dsimp [perpW]; rw [hp0, sub_zero]
          rw [← hp_eq]
          exact hperp_W (v' i) (Submodule.subset_span ⟨i, rfl⟩)
        · intro hx_orth
          have hW0 : ∀ j : Fin k, vecInner b x₀ (w_orth j) = 0 := fun j => by
            have hj_mem : w_orth j ∈ W := hw_span ▸ Submodule.subset_span ⟨j, rfl⟩
            refine Submodule.span_induction (p := fun y _ => vecInner b x₀ y = 0)
              ?_ ?_ ?_ ?_ hj_mem
            · rintro _ ⟨i, rfl⟩; exact hx_orth i
            · exact LinearMap.map_zero _
            · intro a c _ _ ha hc; rw [map_add, ha, hc, add_zero]
            · intro r a _ ha; rw [map_smul, ha, smul_zero]
          change (∑ j : Fin k, vecInner b x₀ (w_orth j) • w_orth j) = 0
          exact Finset.sum_eq_zero fun j _ => by rw [hW0 j, zero_smul]
      refine ⟨h_ineq, ?_, ?_⟩
      · intro hortho
        have hp0 : projW = 0 := hproj_iff.mpr fun i => hortho 0 i.succ (Fin.succ_ne_zero i).symm
        have hperp_eq : perpW = x₀ := by dsimp [perpW]; rw [hp0, sub_zero]
        have htail_eq := ih'.2.1 fun i j hij => hortho i.succ j.succ (Fin.succ_inj.ne.mpr hij)
        rw [hnorm_factor, hperp_eq, htail_eq, hprod_succ]
      · intro hnz
        constructor
        · intro heq
          have htail_pos : 0 < ∏ i : Fin m,
              extInner b (ExteriorAlgebra.ι ℝ (v' i)) (ExteriorAlgebra.ι ℝ (v' i)) :=
            Finset.prod_pos fun i _ =>
              lt_of_le_of_ne (vecInner_pos_def b (v' i)).1
                (Ne.symm (mt (vecInner_pos_def b (v' i)).2.mp (hnz i.succ)))
          have hx₀_pos : 0 < extInner b (ExteriorAlgebra.ι ℝ x₀) (ExteriorAlgebra.ι ℝ x₀) :=
            lt_of_le_of_ne (vecInner_pos_def b x₀).1
              (Ne.symm (mt (vecInner_pos_def b x₀).2.mp (hnz 0)))
          have hperp_eq : extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) =
              extInner b (ExteriorAlgebra.ι ℝ x₀) (ExteriorAlgebra.ι ℝ x₀) := by
            by_contra hne
            have hlt : extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) <
                extInner b (ExteriorAlgebra.ι ℝ x₀) (ExteriorAlgebra.ι ℝ x₀) :=
              lt_of_le_of_ne hperp_le hne
            have hm1 : extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) *
                extInner b (ExteriorAlgebra.ιMulti ℝ m v') (ExteriorAlgebra.ιMulti ℝ m v') ≤
                extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) *
                  ∏ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ (v' i)) (ExteriorAlgebra.ι ℝ (v' i)) :=
              mul_le_mul_of_nonneg_left ih'.1 (vecInner_pos_def b perpW).1
            have hm2 : extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) *
                ∏ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ (v' i)) (ExteriorAlgebra.ι ℝ (v' i)) <
                extInner b (ExteriorAlgebra.ι ℝ x₀) (ExteriorAlgebra.ι ℝ x₀) *
                  ∏ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ (v' i)) (ExteriorAlgebra.ι ℝ (v' i)) :=
              mul_lt_mul_of_pos_right hlt htail_pos
            linarith [hnorm_factor, hprod_succ]
          have htail_eq : extInner b (ExteriorAlgebra.ιMulti ℝ m v') (ExteriorAlgebra.ιMulti ℝ m v') =
              ∏ i : Fin m, extInner b (ExteriorAlgebra.ι ℝ (v' i)) (ExteriorAlgebra.ι ℝ (v' i)) := by
            rw [hnorm_factor, hprod_succ, hperp_eq] at heq
            exact mul_left_cancel₀ hx₀_pos.ne' heq
          have hp0 : projW = 0 := by
            have hzz : extInner b (ExteriorAlgebra.ι ℝ projW) (ExteriorAlgebra.ι ℝ projW) = 0 := by
              have hsp : extInner b (ExteriorAlgebra.ι ℝ x₀) (ExteriorAlgebra.ι ℝ x₀) =
                  extInner b (ExteriorAlgebra.ι ℝ perpW) (ExteriorAlgebra.ι ℝ perpW) +
                    extInner b (ExteriorAlgebra.ι ℝ projW) (ExteriorAlgebra.ι ℝ projW) := hx_split
              linarith
            exact (vecInner_pos_def b projW).2.mp hzz
          have h0_orth := hproj_iff.mp hp0
          have htail_orth := (ih'.2.2 (fun i => hnz i.succ)).mp htail_eq
          intro i j hij
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
            rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
          · exact absurd rfl hij
          · exact h0_orth j'
          · rw [extInner_symm]; exact h0_orth i'
          · exact htail_orth i' j' (fun h => hij (congrArg Fin.succ h))
        · intro hortho
          have hp0 : projW = 0 := hproj_iff.mpr fun i => hortho 0 i.succ (Fin.succ_ne_zero i).symm
          have hperp_eq : perpW = x₀ := by dsimp [perpW]; rw [hp0, sub_zero]
          have htail_eq := ih'.2.1 fun i j hij => hortho i.succ j.succ (Fin.succ_inj.ne.mpr hij)
          rw [hnorm_factor, hperp_eq, htail_eq, hprod_succ]
    · have hv_dep : ¬ LinearIndependent ℝ v := fun h => hv' (h.comp Fin.succ (Fin.succ_injective m))
      have hv_zero : ExteriorAlgebra.ιMulti ℝ (m + 1) v = 0 := (ιMulti_eq_zero_iff v).mpr hv_dep
      refine ⟨?_, ?_, ?_⟩
      · rw [hv_zero, map_zero]
        exact Finset.prod_nonneg fun i _ => hprod_nonneg i
      · intro hortho
        by_cases hnz : ∀ i : Fin (m + 1), v i ≠ 0
        · exfalso
          have hv'_ortho : (vecInner b).IsOrthoᵢ v' := fun i j hij =>
            hortho i.succ j.succ (Fin.succ_inj.ne.mpr hij)
          exact hv' (LinearMap.BilinForm.linearIndependent_of_iIsOrtho hv'_ortho fun i =>
            mt (vecInner_pos_def b (v' i)).2.mp (hnz i.succ))
        · push Not at hnz
          obtain ⟨i₀, hi₀⟩ := hnz
          have hprod0 : (∏ i : Fin (m + 1),
              extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v i))) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])
          rw [hv_zero, map_zero, hprod0]
      · intro hnz
        constructor
        · intro heq
          exfalso
          have hprod_pos : 0 < ∏ i : Fin (m + 1),
              extInner b (ExteriorAlgebra.ι ℝ (v i)) (ExteriorAlgebra.ι ℝ (v i)) :=
            Finset.prod_pos fun i _ =>
              lt_of_le_of_ne (vecInner_pos_def b (v i)).1
                (Ne.symm (mt (vecInner_pos_def b (v i)).2.mp (hnz i)))
          rw [hv_zero, map_zero] at heq
          linarith
        · intro hortho
          exfalso
          have hv'_ortho : (vecInner b).IsOrthoᵢ v' := fun i j hij =>
            hortho i.succ j.succ (Fin.succ_inj.ne.mpr hij)
          exact hv' (LinearMap.BilinForm.linearIndependent_of_iIsOrtho hv'_ortho fun i =>
            mt (vecInner_pos_def b (v' i)).2.mp (hnz i.succ))

end Note69HadamardInequality

/-! ## 8. Editorial Notes 68 & 70: Unequal-Grade Normal Shadow Cosine Equality (`pp. 357–359`) -/

section Notes68_70UnequalShadowAngles

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem exists_orthonormal_basis_adapted {n k : ℕ} (b : Module.Basis (Fin n) ℝ V)
    (W : Submodule ℝ V) (hk_eq : Module.finrank ℝ W = k) :
    ∃ (c : Module.Basis (Fin n) ℝ V) (hk : k ≤ n),
      b.det c = 1 ∧
      hodge c = hodge b ∧
      regressive c = regressive b ∧
      (∀ x y : ExteriorAlgebra ℝ V, extInner c x y = extInner b x y) ∧
      Submodule.span ℝ (Set.range (fun i : Fin k => c ⟨i.val, by omega⟩)) = W := by
  have : Module.Finite ℝ V := Module.Finite.of_basis b
  let W_perp : Submodule ℝ V := (vecInner b).orthogonal W
  obtain ⟨k', w_orth₀, hw_li₀, hw_span₀, hw_ortho₀⟩ :=
    exists_orthonormal_basis_of_submodule b W
  have hk'_eq : k' = k := by
    have hr : Module.finrank ℝ W = k' := by
      rw [← hw_span₀, finrank_span_eq_card hw_li₀, Fintype.card_fin]
    exact hr.symm.trans hk_eq
  let w_orth : Fin k → V := w_orth₀ ∘ (finCongr hk'_eq).symm
  have hw_li : LinearIndependent ℝ w_orth :=
    hw_li₀.comp _ (finCongr hk'_eq).symm.injective
  have hw_span : Submodule.span ℝ (Set.range w_orth) = W := by
    rw [show Set.range w_orth = Set.range w_orth₀ by
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ], hw_span₀]
  have hw_ortho : ∀ i j : Fin k,
      extInner b (ExteriorAlgebra.ι ℝ (w_orth i)) (ExteriorAlgebra.ι ℝ (w_orth j)) =
        if i = j then 1 else 0 := fun i j => by
    change extInner b (ExteriorAlgebra.ι ℝ (w_orth₀ ((finCongr hk'_eq).symm i)))
      (ExteriorAlgebra.ι ℝ (w_orth₀ ((finCongr hk'_eq).symm j))) = _
    rw [hw_ortho₀]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have hdisj : Disjoint W W_perp := by
    rw [disjoint_iff_inf_le]
    intro x ⟨hxW, hxP⟩
    have h0 : vecInner b x x = 0 := hxP x hxW
    exact (vecInner_pos_def b x).2.mp h0
  have hsup : W ⊔ W_perp = ⊤ := by
    rw [eq_top_iff]
    intro x _
    let p : V := ∑ i : Fin k, vecInner b x (w_orth i) • w_orth i
    let q : V := x - p
    have hp_mem : p ∈ W :=
      Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (hw_span ▸ Submodule.subset_span ⟨i, rfl⟩)
    have hq_mem : q ∈ W_perp := by
      intro y hy
      rw [← hw_span] at hy
      refine Submodule.span_induction (p := fun y _ => vecInner b y q = 0) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, rfl⟩
        rw [vecInner_apply, extInner_symm, ← vecInner_apply]
        change vecInner b (x - ∑ r : Fin k, vecInner b x (w_orth r) • w_orth r) (w_orth i) = 0
        rw [LinearMap.map_sub₂, LinearMap.map_sum₂, Finset.sum_eq_single i]
        · simp only [LinearMap.map_smul₂, vecInner_apply, hw_ortho i i, ite_true,
            smul_eq_mul, mul_one, sub_self]
        · intro r _ hri
          simp only [LinearMap.map_smul₂, vecInner_apply, hw_ortho r i, ite_eq_right hri, smul_zero]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      · exact LinearMap.map_zero₂ (vecInner b) q
      · intro a c _ _ ha hc; rw [map_add, LinearMap.add_apply, ha, hc, add_zero]
      · intro r a _ ha; simp [ha]
    have hx_eq : x = p + q := by dsimp [q]; abel
    rw [hx_eq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hp_mem) (Submodule.mem_sup_right hq_mem)
  have hcompl : IsCompl W W_perp := ⟨hdisj, codisjoint_iff.mpr hsup⟩
  obtain ⟨m, p_orth, hp_li, hp_span, hp_ortho⟩ :=
    exists_orthonormal_basis_of_submodule b W_perp
  have hfinV : Module.finrank ℝ V = n := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hm_eq : Module.finrank ℝ W_perp = m := by
    rw [← hp_span, finrank_span_eq_card hp_li, Fintype.card_fin]
  have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
  have hkm : k + m = n := by omega
  have hkn : k ≤ n := by omega
  let fam : Fin n → V := (Fin.append w_orth p_orth) ∘ (finCongr hkm).symm
  have hfam_ortho : ∀ i j : Fin n,
      extInner b (ExteriorAlgebra.ι ℝ (fam i)) (ExteriorAlgebra.ι ℝ (fam j)) =
        if i = j then 1 else 0 := fun i j => by
    obtain ⟨i', rfl⟩ := (finCongr hkm).surjective i
    obtain ⟨j', rfl⟩ := (finCongr hkm).surjective j
    simp only [fam, Function.comp_apply, Equiv.symm_apply_apply]
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i' <;>
      refine Fin.addCases (fun c' => ?_) (fun c' => ?_) j'
    · rw [Fin.append_left, Fin.append_left, hw_ortho a c']
      by_cases hac : a = c'
      · subst hac; simp
      · have hne : finCongr hkm (Fin.castAdd m a) ≠ finCongr hkm (Fin.castAdd m c') := fun h =>
          hac (Fin.castAdd_injective k m ((finCongr hkm).injective h))
        rw [ite_eq_right hac, ite_eq_right hne]
    · rw [Fin.append_left, Fin.append_right]
      have hmemP : p_orth c' ∈ W_perp := hp_span ▸ Submodule.subset_span ⟨c', rfl⟩
      have hmemW : w_orth a ∈ W := hw_span ▸ Submodule.subset_span ⟨a, rfl⟩
      have h0 : extInner b (ExteriorAlgebra.ι ℝ (w_orth a)) (ExteriorAlgebra.ι ℝ (p_orth c')) = 0 :=
        hmemP (w_orth a) hmemW
      have hne : finCongr hkm (Fin.castAdd m a) ≠ finCongr hkm (Fin.natAdd k c') := fun h => by
        have hv := congrArg Fin.val ((finCongr hkm).injective h)
        simp at hv
        omega
      rw [h0, ite_eq_right hne]
    · rw [Fin.append_right, Fin.append_left]
      have hmemP : p_orth a ∈ W_perp := hp_span ▸ Submodule.subset_span ⟨a, rfl⟩
      have hmemW : w_orth c' ∈ W := hw_span ▸ Submodule.subset_span ⟨c', rfl⟩
      have h0 : extInner b (ExteriorAlgebra.ι ℝ (p_orth a)) (ExteriorAlgebra.ι ℝ (w_orth c')) = 0 := by
        rw [extInner_symm]
        exact hmemP (w_orth c') hmemW
      have hne : finCongr hkm (Fin.natAdd k a) ≠ finCongr hkm (Fin.castAdd m c') := fun h => by
        have hv := congrArg Fin.val ((finCongr hkm).injective h)
        simp at hv
        omega
      rw [h0, ite_eq_right hne]
    · rw [Fin.append_right, Fin.append_right, hp_ortho a c']
      by_cases hac : a = c'
      · subst hac; simp
      · have hne : finCongr hkm (Fin.natAdd k a) ≠ finCongr hkm (Fin.natAdd k c') := fun h => by
          apply hac
          ext
          have hv := congrArg Fin.val ((finCongr hkm).injective h)
          simp at hv
          omega
        rw [ite_eq_right hac, ite_eq_right hne]
  have hfam_ortho' : (vecInner b).IsOrthoᵢ fam := fun i j hij => by
    dsimp only [Function.onFun]
    rw [vecInner_apply, hfam_ortho i j, ite_eq_right hij]
  have hfam_li : LinearIndependent ℝ fam :=
    LinearMap.BilinForm.linearIndependent_of_iIsOrtho hfam_ortho' fun i => by
      rw [vecInner_apply, hfam_ortho i i, ite_eq_left rfl]
      exact one_ne_zero
  have hfam_span : ⊤ ≤ Submodule.span ℝ (Set.range fam) := by
    rw [show Set.range fam = Set.range (Fin.append w_orth p_orth) by
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ],
      range_fin_append, Submodule.span_union, hw_span, hp_span, hsup]
  let c₀ : Module.Basis (Fin n) ℝ V := Module.Basis.mk hfam_li hfam_span
  have hc₀_val : ∀ i : Fin n, c₀ i = fam i := fun i => Module.Basis.mk_apply hfam_li hfam_span i
  have hmat_ortho : (b.toMatrix c₀)ᵀ * b.toMatrix c₀ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    have hsum : ∑ r : Fin n, b.repr (c₀ i) r * b.repr (c₀ j) r =
        extInner b (ExteriorAlgebra.ι ℝ (c₀ i)) (ExteriorAlgebra.ι ℝ (c₀ j)) := by
      have hxi : ExteriorAlgebra.ι ℝ (c₀ i) =
          ∑ r : Fin n, b.repr (c₀ i) r • b.ExteriorAlgebra {r} := by
        have hc := (b.sum_repr (c₀ i)).symm
        conv_lhs => rw [hc, map_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul]
        congr 1
        rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton r)]
        let g := Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofCard (Finset.card_singleton r))
        have hg0 : g 0 = r := Finset.mem_singleton.mp
          ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g 0)).1 ⟨0, rfl⟩)
        change _ = ExteriorAlgebra.ιMulti ℝ 1 (fun t => b (g t))
        rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, hg0]
      have hxj : ExteriorAlgebra.ι ℝ (c₀ j) =
          ∑ s : Fin n, b.repr (c₀ j) s • b.ExteriorAlgebra {s} := by
        have hc := (b.sum_repr (c₀ j)).symm
        conv_lhs => rw [hc, map_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_smul]
        congr 1
        rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton s)]
        let g := Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofCard (Finset.card_singleton s))
        have hg0 : g 0 = s := Finset.mem_singleton.mp
          ((Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ (g 0)).1 ⟨0, rfl⟩)
        change _ = ExteriorAlgebra.ιMulti ℝ 1 (fun t => b (g t))
        rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one, hg0]
      rw [hxi, hxj]
      simp only [map_sum, LinearMap.sum_apply, extInner_smul_left, extInner_smul_right,
        extInner_basis]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_eq_single r]
      · simp [mul_comm]
      · intro s _ hsr
        have hsing : ({s} : Finset (Fin n)) ≠ {r} := fun h => hsr (Finset.singleton_injective h)
        rw [ite_eq_right hsing, mul_zero, mul_zero]
      · intro hr; exact (hr (Finset.mem_univ r)).elim
    rw [hsum, hc₀_val, hc₀_val, hfam_ortho]
  have hdet_sq : (b.det c₀) * (b.det c₀) = 1 := by
    have hd := congrArg Matrix.det hmat_ortho
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← Module.Basis.det_apply] at hd
    exact hd
  have hdet_pm : b.det c₀ = 1 ∨ b.det c₀ = -1 := sq_eq_one_iff.mp (by rw [sq]; exact hdet_sq)
  cases n with
  | zero =>
    have hdet1 : b.det c₀ = 1 := by
      rw [Module.Basis.det_apply]
      exact Matrix.det_fin_zero
    have hh_eq : hodge c₀ = hodge b :=
      (note62_hodge_eq_iff_orthonormal b c₀ hdet1).1.mpr fun i => Fin.elim0 i
    have hreg_eq : regressive c₀ = regressive b := by
      ext x y
      exact regressive_eq_of_det_eq_one b c₀ hdet1 x y
    have hext_eq : ∀ x y : ExteriorAlgebra ℝ V, extInner c₀ x y = extInner b x y := fun x y => by
      dsimp [extInner]
      rw [hh_eq, volCoord_eq_of_det_eq_one b c₀ hdet1]
    have hk0 : k = 0 := by omega
    subst hk0
    have hWbot : W = ⊥ := Submodule.finrank_eq_zero.mp hk_eq
    refine ⟨c₀, le_rfl, hdet1, hh_eq, hreg_eq, hext_eq, ?_⟩
    rw [hWbot]
    simp
  | succ m' =>
    let signUnit : ℝˣ := if b.det c₀ = 1 then 1 else -1
    let uVec : Fin (m' + 1) → ℝˣ := fun i => if i = 0 then signUnit else 1
    let c : Module.Basis (Fin (m' + 1)) ℝ V := c₀.unitsSMul uVec
    have hdet1 : b.det c = 1 := by
      rw [← Module.Basis.det_mul_det b c₀ c, show c = c₀.unitsSMul uVec from rfl,
        Module.Basis.det_unitsSMul_self]
      have hprod : ∏ i : Fin (m' + 1), (uVec i : ℝ) = (signUnit : ℝ) := by
        rw [Finset.prod_eq_single (0 : Fin (m' + 1))]
        · simp [uVec]
        · intro i _ hi0; simp [uVec, hi0]
        · intro h0; exact (h0 (Finset.mem_univ 0)).elim
      rw [hprod]
      rcases hdet_pm with h1 | hm1
      · simp [signUnit, h1]
      · dsimp [signUnit]
        rw [hm1, ite_eq_right (by norm_num : (-1 : ℝ) ≠ 1)]
        norm_num
    have hc_ortho : ∀ i j : Fin (m' + 1),
        extInner b (ExteriorAlgebra.ι ℝ (c i)) (ExteriorAlgebra.ι ℝ (c j)) =
          if i = j then 1 else 0 := fun i j => by
      simp only [c, Module.Basis.unitsSMul_apply, hc₀_val, Units.smul_def, map_smul,
        LinearMap.smul_apply, smul_eq_mul, hfam_ortho]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, mul_one]
        by_cases hi0 : i = 0
        · subst hi0
          by_cases h1 : b.det c₀ = 1 <;> simp [uVec, signUnit, h1]
        · simp [uVec, hi0]
      · rw [ite_eq_right hij, mul_zero, mul_zero]
    have hh_eq : hodge c = hodge b :=
      (note62_hodge_eq_iff_orthonormal b c hdet1).1.mpr
        ((note62_hodge_eq_iff_orthonormal b c hdet1).2.mpr hc_ortho)
    have hreg_eq : regressive c = regressive b := by
      ext x y
      exact regressive_eq_of_det_eq_one b c hdet1 x y
    have hext_eq : ∀ x y : ExteriorAlgebra ℝ V, extInner c x y = extInner b x y := fun x y => by
      dsimp [extInner]
      rw [hh_eq, volCoord_eq_of_det_eq_one b c hdet1]
    have hspan_c : Submodule.span ℝ (Set.range (fun i : Fin k => c ⟨i.val, by omega⟩)) = W := by
      have hrng : ∀ i : Fin k, ∃ α : ℝˣ, c ⟨i.val, by omega⟩ = (α : ℝ) • w_orth i := fun i => by
        refine ⟨uVec ⟨i.val, by omega⟩, ?_⟩
        simp only [c, Module.Basis.unitsSMul_apply, hc₀_val, fam, Function.comp_apply]
        have heinv : (finCongr hkm).symm ⟨i.val, by omega⟩ = Fin.castAdd m i := by
          ext; rfl
        rw [heinv, Fin.append_left, Units.smul_def]
      have hset : Set.range (fun i : Fin k => c ⟨i.val, by omega⟩) ⊆ (W : Set V) := by
        rintro _ ⟨i, rfl⟩
        obtain ⟨α, hα⟩ := hrng i
        change c ⟨i.val, _⟩ ∈ W
        rw [hα]
        exact W.smul_mem (α : ℝ) (hw_span ▸ Submodule.subset_span ⟨i, rfl⟩)
      apply le_antisymm (Submodule.span_le.mpr hset)
      intro x hx
      rw [← hw_span, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨coeff, rfl⟩ := hx
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      obtain ⟨α, hα⟩ := hrng i
      have hw_eq : w_orth i = (α⁻¹ : ℝˣ) • c ⟨i.val, by omega⟩ := by
        rw [hα, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      rw [hw_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact ⟨c, hkn, hdet1, hh_eq, hreg_eq, hext_eq, hspan_c⟩

private theorem regressive_compl_basis_self {n : ℕ} (c : Module.Basis (Fin n) ℝ V)
    (s sB : Finset (Fin n)) (hsB : s ⊆ sB) :
    regressive c (c.ExteriorAlgebra sB)
        (c.ExteriorAlgebra s * hodge c (c.ExteriorAlgebra sB)) =
      c.ExteriorAlgebra s := by
  have hd : Disjoint s sBᶜ := disjoint_compl_right_sub hsB
  let ps := Set.powersetCard.ofCard (s := s) rfl
  let pBc := Set.powersetCard.ofCard (s := sBᶜ) rfl
  have hd' : Disjoint (ps : Finset (Fin n)) (pBc : Finset (Fin n)) := hd
  let ε : ℤˣ := (Set.powersetCard.permOfDisjoint hd').sign
  have hdisj_union : s.disjUnion sBᶜ hd = (sB \ s)ᶜ := by
    ext x
    simp only [Finset.mem_disjUnion, Finset.mem_compl, Finset.mem_sdiff]
    by_cases hxB : x ∈ sB <;> by_cases hxs : x ∈ s
    · simp [hxB, hxs]
    · simp [hxB, hxs]
    · exact absurd (hsB hxs) hxB
    · simp [hxB, hxs]
  have hm1 : c.ExteriorAlgebra s * c.ExteriorAlgebra sBᶜ =
      ((ε : ℤ) : ℝ) • c.ExteriorAlgebra (sB \ s)ᶜ := by
    have hm := ExteriorAlgebra.basis_mul_of_disjoint c ps pBc hd'
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ] at hm
    change c.ExteriorAlgebra s * c.ExteriorAlgebra sBᶜ =
      ((ε : ℤ) : ℝ) • c.ExteriorAlgebra (s.disjUnion sBᶜ hd) at hm
    rwa [hdisj_union] at hm
  have h1 : c.ExteriorAlgebra s * hodge c (c.ExteriorAlgebra sB) =
      ((orientationUnit (K := ℝ) sB : ℝ) * ((ε : ℤ) : ℝ)) • c.ExteriorAlgebra (sB \ s)ᶜ := by
    rw [hodge_basis c sB, mul_smul_comm, hm1, smul_smul]
  have hd2 : Disjoint sBᶜ (sB \ s) := disjoint_compl_left_sub Finset.sdiff_subset
  let pBs := Set.powersetCard.ofCard (s := sB \ s) rfl
  have hd2' : Disjoint (pBc : Finset (Fin n)) (pBs : Finset (Fin n)) := hd2
  let ε2 : ℤˣ := (Set.powersetCard.permOfDisjoint hd2').sign
  have hunion2 : sBᶜ.disjUnion (sB \ s) hd2 = sᶜ := by
    ext x
    simp only [Finset.mem_disjUnion, Finset.mem_compl, Finset.mem_sdiff]
    by_cases hxB : x ∈ sB <;> by_cases hxs : x ∈ s
    · simp [hxB, hxs]
    · simp [hxB, hxs]
    · exact absurd (hsB hxs) hxB
    · simp [hxB, hxs]
  have hm2 : c.ExteriorAlgebra sBᶜ * c.ExteriorAlgebra (sB \ s) =
      ((ε2 : ℤ) : ℝ) • c.ExteriorAlgebra sᶜ := by
    have hm := ExteriorAlgebra.basis_mul_of_disjoint c pBc pBs hd2'
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ] at hm
    change c.ExteriorAlgebra sBᶜ * c.ExteriorAlgebra (sB \ s) =
      ((ε2 : ℤ) : ℝ) • c.ExteriorAlgebra (sBᶜ.disjUnion (sB \ s) hd2) at hm
    rwa [hunion2] at hm
  let coeff : ℝ := (orientationUnit (K := ℝ) sB : ℝ) *
    ((orientationUnit (K := ℝ) sB : ℝ) * ((ε : ℤ) : ℝ)) *
    (orientationUnit (K := ℝ) (sB \ s)ᶜ : ℝ) * ((ε2 : ℤ) : ℝ) *
    (orientationUnit (K := ℝ) s : ℝ)
  have hreg : regressive c (c.ExteriorAlgebra sB)
      (c.ExteriorAlgebra s * hodge c (c.ExteriorAlgebra sB)) = coeff • c.ExteriorAlgebra s := by
    apply (hodge c).injective
    rw [hodge_regressive, h1, map_smul, hodge_basis c sB, hodge_basis c (sB \ s)ᶜ, compl_compl,
      smul_mul_assoc, mul_smul_comm, mul_smul_comm, hm2, smul_smul, smul_smul, smul_smul,
      map_smul, hodge_basis c s]
    have hsym : (orientationUnit (K := ℝ) s : ℝ) ^ 2 = 1 := by
      rw [sq]
      exact orientationUnit_mul_self s
    rw [smul_smul]
    congr 1
    dsimp [coeff]
    ring_nf
    rw [hsym, mul_one]
  have hpair : coeff = 1 := by
    have hin1 := note68_normal_shadow_reciprocity c (c.ExteriorAlgebra s) (c.ExteriorAlgebra sB)
    change extInner c (c.ExteriorAlgebra s)
      (regressive c (c.ExteriorAlgebra sB) (c.ExteriorAlgebra s * hodge c (c.ExteriorAlgebra sB))) =
      extInner c (c.ExteriorAlgebra s * hodge c (c.ExteriorAlgebra sB))
        (c.ExteriorAlgebra s * hodge c (c.ExteriorAlgebra sB)) at hin1
    rw [hreg, extInner_smul_right, extInner_basis, ite_eq_left rfl, mul_one] at hin1
    rw [h1, extInner_smul_left, extInner_smul_right, extInner_basis, ite_eq_left rfl, mul_one] at hin1
    have hsq1 : (orientationUnit (K := ℝ) sB : ℝ) * (orientationUnit (K := ℝ) sB : ℝ) = 1 :=
      orientationUnit_mul_self sB
    have hsq2 : ((ε : ℤ) : ℝ) * ((ε : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self ε, Units.val_one, Int.cast_one]
    have hs1 : ((orientationUnit (K := ℝ) sB : ℝ) * ((ε : ℤ) : ℝ)) *
        ((orientationUnit (K := ℝ) sB : ℝ) * ((ε : ℤ) : ℝ)) = 1 := by
      calc
        ((orientationUnit (K := ℝ) sB : ℝ) * ((ε : ℤ) : ℝ)) *
            ((orientationUnit (K := ℝ) sB : ℝ) * ((ε : ℤ) : ℝ))
            = ((orientationUnit (K := ℝ) sB : ℝ) * (orientationUnit (K := ℝ) sB : ℝ)) *
                (((ε : ℤ) : ℝ) * ((ε : ℤ) : ℝ)) := by ring
        _ = 1 * 1 := by rw [hsq1, hsq2]
        _ = 1 := by norm_num
    rw [hs1] at hin1
    exact hin1
  rw [hreg, hpair, one_smul]

private theorem mul_regressive_compl_basis_self {n : ℕ} (c : Module.Basis (Fin n) ℝ V)
    (t sA : Finset (Fin n)) (hsA : sA ⊆ t) :
    c.ExteriorAlgebra sA *
        regressive c (c.ExteriorAlgebra t) (hodge c (c.ExteriorAlgebra sA)) =
      c.ExteriorAlgebra t := by
  have hd : Disjoint tᶜ sA := disjoint_compl_left_sub hsA
  let ptc := Set.powersetCard.ofCard (s := tᶜ) rfl
  let psA := Set.powersetCard.ofCard (s := sA) rfl
  have hd' : Disjoint (ptc : Finset (Fin n)) (psA : Finset (Fin n)) := hd
  let ε : ℤˣ := (Set.powersetCard.permOfDisjoint hd').sign
  have hunion : tᶜ.disjUnion sA hd = (t \ sA)ᶜ := by
    ext x
    simp only [Finset.mem_disjUnion, Finset.mem_compl, Finset.mem_sdiff]
    by_cases hxt : x ∈ t <;> by_cases hxs : x ∈ sA
    · simp [hxt, hxs]
    · simp [hxt, hxs]
    · exact absurd (hsA hxs) hxt
    · simp [hxt, hxs]
  have hm1 : c.ExteriorAlgebra tᶜ * c.ExteriorAlgebra sA =
      ((ε : ℤ) : ℝ) • c.ExteriorAlgebra (t \ sA)ᶜ := by
    have hm := ExteriorAlgebra.basis_mul_of_disjoint c ptc psA hd'
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ] at hm
    change c.ExteriorAlgebra tᶜ * c.ExteriorAlgebra sA =
      ((ε : ℤ) : ℝ) • c.ExteriorAlgebra (tᶜ.disjUnion sA hd) at hm
    rwa [hunion] at hm
  have h1 : hodge c (regressive c (c.ExteriorAlgebra t) (hodge c (c.ExteriorAlgebra sA))) =
      ((orientationUnit (K := ℝ) t : ℝ) * (-1 : ℝ) ^ (sA.card * (n - sA.card)) *
        ((ε : ℤ) : ℝ)) • c.ExteriorAlgebra (t \ sA)ᶜ := by
    rw [hodge_regressive, hodge_hodge_basis, hodge_basis c t, smul_mul_assoc, mul_smul_comm, hm1,
      smul_smul, smul_smul]
  have hreg_eq : regressive c (c.ExteriorAlgebra t) (hodge c (c.ExteriorAlgebra sA)) =
      ((orientationUnit (K := ℝ) t : ℝ) * (-1 : ℝ) ^ (sA.card * (n - sA.card)) *
        ((ε : ℤ) : ℝ) * (-1 : ℝ) ^ ((t \ sA)ᶜ.card * (n - (t \ sA)ᶜ.card)) *
        (orientationUnit (K := ℝ) (t \ sA)ᶜ : ℝ)) • c.ExteriorAlgebra (t \ sA) := by
    have hdeg : c.ExteriorAlgebra (t \ sA)ᶜ ∈ ⋀[ℝ]^(t \ sA)ᶜ.card V :=
      basis_mem_exteriorPower c (t \ sA)ᶜ
    have hinv : regressive c (c.ExteriorAlgebra t) (hodge c (c.ExteriorAlgebra sA)) =
        (hodge c).symm (hodge c (regressive c (c.ExteriorAlgebra t) (hodge c (c.ExteriorAlgebra sA)))) :=
      ((hodge c).symm_apply_apply _).symm
    rw [hinv, h1, map_smul, hodge_symm_exteriorPower c hdeg, hodge_basis c (t \ sA)ᶜ, compl_compl,
      smul_smul, smul_smul]
  have hd2 : Disjoint sA (t \ sA) := disjoint_sdiff_self_right
  let pTs := Set.powersetCard.ofCard (s := t \ sA) rfl
  have hd2' : Disjoint (psA : Finset (Fin n)) (pTs : Finset (Fin n)) := hd2
  let ε2 : ℤˣ := (Set.powersetCard.permOfDisjoint hd2').sign
  have hunion2 : sA.disjUnion (t \ sA) hd2 = t := by
    ext x
    simp only [Finset.mem_disjUnion, Finset.mem_sdiff]
    by_cases hxt : x ∈ t <;> by_cases hxs : x ∈ sA
    · simp [hxt, hxs]
    · simp [hxt, hxs]
    · exact absurd (hsA hxs) hxt
    · simp [hxt, hxs]
  have hm2 : c.ExteriorAlgebra sA * c.ExteriorAlgebra (t \ sA) =
      ((ε2 : ℤ) : ℝ) • c.ExteriorAlgebra t := by
    have hm := ExteriorAlgebra.basis_mul_of_disjoint c psA pTs hd2'
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ] at hm
    change c.ExteriorAlgebra sA * c.ExteriorAlgebra (t \ sA) =
      ((ε2 : ℤ) : ℝ) • c.ExteriorAlgebra (sA.disjUnion (t \ sA) hd2) at hm
    rwa [hunion2] at hm
  let coeff : ℝ := (orientationUnit (K := ℝ) t : ℝ) * (-1 : ℝ) ^ (sA.card * (n - sA.card)) *
    ((ε : ℤ) : ℝ) * (-1 : ℝ) ^ ((t \ sA)ᶜ.card * (n - (t \ sA)ᶜ.card)) *
    (orientationUnit (K := ℝ) (t \ sA)ᶜ : ℝ) * ((ε2 : ℤ) : ℝ)
  have hmul : c.ExteriorAlgebra sA *
      regressive c (c.ExteriorAlgebra t) (hodge c (c.ExteriorAlgebra sA)) =
      coeff • c.ExteriorAlgebra t := by
    rw [hreg_eq, mul_smul_comm, hm2, smul_smul]
  have hpair : coeff = 1 := by
    have hrec := (note68_homogeneous_reciprocity c (basis_mem_exteriorPower c sA)
      (basis_mem_exteriorPower c t)).2
    rw [note68_normal_shadow_reciprocity] at hrec
    change extInner c (c.ExteriorAlgebra sA * hodge c (c.ExteriorAlgebra t))
        (c.ExteriorAlgebra sA * hodge c (c.ExteriorAlgebra t)) =
      extInner c
        (c.ExteriorAlgebra sA * regressive c (c.ExteriorAlgebra t) (hodge c (c.ExteriorAlgebra sA)))
        (c.ExteriorAlgebra t) at hrec
    rw [hmul, extInner_smul_left, extInner_basis, ite_eq_left rfl, mul_one] at hrec
    have hds : Disjoint sA tᶜ := disjoint_compl_right_sub hsA
    let ptc' := Set.powersetCard.ofCard (s := tᶜ) rfl
    have hds' : Disjoint (psA : Finset (Fin n)) (ptc' : Finset (Fin n)) := hds
    let ε' : ℤˣ := (Set.powersetCard.permOfDisjoint hds').sign
    have hms : c.ExteriorAlgebra sA * c.ExteriorAlgebra tᶜ =
        ((ε' : ℤ) : ℝ) • c.ExteriorAlgebra (sA.disjUnion tᶜ hds) := by
      have hm := ExteriorAlgebra.basis_mul_of_disjoint c psA ptc' hds'
      rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ] at hm
      exact hm
    have hsq1 : (orientationUnit (K := ℝ) t : ℝ) * (orientationUnit (K := ℝ) t : ℝ) = 1 :=
      orientationUnit_mul_self t
    have hsq2 : ((ε' : ℤ) : ℝ) * ((ε' : ℤ) : ℝ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self ε', Units.val_one, Int.cast_one]
    rw [hodge_basis c t, mul_smul_comm, hms, smul_smul, extInner_smul_left, extInner_smul_right,
      extInner_basis, ite_eq_left rfl, mul_one] at hrec
    have h1s : ((orientationUnit (K := ℝ) t : ℝ) * ((ε' : ℤ) : ℝ)) *
        ((orientationUnit (K := ℝ) t : ℝ) * ((ε' : ℤ) : ℝ)) = 1 := by
      calc
        ((orientationUnit (K := ℝ) t : ℝ) * ((ε' : ℤ) : ℝ)) *
            ((orientationUnit (K := ℝ) t : ℝ) * ((ε' : ℤ) : ℝ))
            = ((orientationUnit (K := ℝ) t : ℝ) * (orientationUnit (K := ℝ) t : ℝ)) *
                (((ε' : ℤ) : ℝ) * ((ε' : ℤ) : ℝ)) := by ring
        _ = 1 * 1 := by rw [hsq1, hsq2]
        _ = 1 := by norm_num
    rw [h1s] at hrec
    exact hrec.symm
  rw [hmul, hpair, one_smul]

/-- **Editorial Notes 68 & 70 (`pp. 357–359`) — Unequal-Order Normal Shadow Cosine Equality**:
for ANY independent `α`-blade `A = ιMulti ℝ α u` and `β`-blade `B = ιMulti ℝ β v` (`α ≤ β ≤ n`)
in Euclidean `(V, extInner b)`, let `M := (hodge b).symm (A * hodge b B)`, normalized shadow
`A' := (extInner b B B)⁻¹ • regressive b B (hodge b M)` in `span v`, and dual normalized shadow
`B' := ((-1)^(α(β - α)) * (extInner b A A)⁻¹) • (A * M)`:
1. `⟨A, A'⟩ = ⟨M, M⟩ / ⟨B, B⟩` and `⟨A', A'⟩ = ⟨M, M⟩ / ⟨B, B⟩`,
2. `⟨B', B⟩ = ⟨M, M⟩ / ⟨A, A⟩` and `⟨B', B'⟩ = ⟨M, M⟩ / ⟨A, A⟩`,
3. `⟨A, A'⟩² * (⟨B, B⟩ * ⟨B', B'⟩) = ⟨B', B⟩² * (⟨A, A⟩ * ⟨A', A'⟩)` (`cos² ∠AA' = cos² ∠B'B`),
4. `⟨M, M⟩ ≤ ⟨A, A⟩ * ⟨B, B⟩` (`‖A * ★B‖² ≤ ‖A‖² ‖B‖²`), and
5. `⟨★X, ★Y⟩ = ⟨X, Y⟩` (`Note 70` Hodge inner-product isometry). -/
theorem notes68_70_unequal_grade_normal_shadow_angles {n α β : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (u : Fin α → V) (v : Fin β → V)
    (hu : LinearIndependent ℝ u) (hv : LinearIndependent ℝ v)
    (hαβ : α ≤ β) (hβn : β ≤ n) :
    let A := ExteriorAlgebra.ιMulti ℝ α u
    let B := ExteriorAlgebra.ιMulti ℝ β v
    let M := (hodge b).symm (A * hodge b B)
    let A' := (extInner b B B)⁻¹ • regressive b B (hodge b M)
    let B' := (((-1 : ℝ) ^ (α * (β - α))) * (extInner b A A)⁻¹) • (A * M)
    extInner b A A' = extInner b M M / extInner b B B ∧
      extInner b A' A' = extInner b M M / extInner b B B ∧
      extInner b B' B = extInner b M M / extInner b A A ∧
      extInner b B' B' = extInner b M M / extInner b A A ∧
      (extInner b A A') ^ 2 * (extInner b B B * extInner b B' B') =
        (extInner b B' B) ^ 2 * (extInner b A A * extInner b A' A') ∧
      extInner b M M ≤ extInner b A A * extInner b B B ∧
      (∀ X Y : ExteriorAlgebra ℝ V, extInner b (hodge b X) (hodge b Y) = extInner b X Y) := by
  intro A B M A' B'
  have hA_ne : A ≠ 0 := ιMulti_ne_zero_of_linearIndependent u hu
  have hB_ne : B ≠ 0 := ιMulti_ne_zero_of_linearIndependent v hv
  have hAA_ne : extInner b A A ≠ 0 :=
    mt (note68_extInner_cauchy_schwarz b A A).2.1.mp hA_ne
  have hBB_ne : extInner b B B ≠ 0 :=
    mt (note68_extInner_cauchy_schwarz b B B).2.1.mp hB_ne
  have hA_mem : A ∈ ⋀[ℝ]^α V := ExteriorAlgebra.ιMulti_range ℝ α ⟨u, rfl⟩
  have hB_mem : B ∈ ⋀[ℝ]^β V := ExteriorAlgebra.ιMulti_range ℝ β ⟨v, rfl⟩
  have hhM : hodge b M = A * hodge b B := (hodge b).apply_symm_apply _
  have hMM : extInner b M M = extInner b (A * hodge b B) (A * hodge b B) := by
    rw [← extInner_hodge_isometry b M, hhM]
  have hAA' : extInner b A A' = extInner b M M / extInner b B B := by
    change extInner b A ((extInner b B B)⁻¹ • regressive b B (hodge b M)) = _
    rw [extInner_smul_right, hhM, show regressive b B (A * hodge b B) = normalShadowLeft b A B from rfl,
      note68_normal_shadow_reciprocity, ← hMM, div_eq_inv_mul]
  have hM_rec : regressive b B (hodge b A) = ((-1 : ℝ) ^ (α * (β - α))) • M := by
    apply (hodge b).injective
    rw [hodge_regressive, hodge_hodge_exteriorPower b hA_mem, mul_smul_comm,
      exteriorPower_mul_comm (hodge_mem_exteriorPower b hB_mem) hA_mem, smul_smul, ← pow_add,
      map_smul, hhM]
    congr 1
    have hnat : α * (n - α) + (n - β) * α = 2 * (α * (n - β)) + α * (β - α) := by
      zify [hαβ, hβn, hαβ.trans hβn]
      ring
    rw [hnat, pow_add, pow_mul, show (-1 : ℝ) ^ 2 = 1 by norm_num, one_pow, one_mul]
  have hB'_eq : B' = (extInner b A A)⁻¹ • normalShadowRight b A B := by
    change (((-1 : ℝ) ^ (α * (β - α))) * (extInner b A A)⁻¹) • (A * M) =
      (extInner b A A)⁻¹ • (A * regressive b B (hodge b A))
    rw [hM_rec, mul_smul_comm, smul_smul, mul_comm _ (extInner b A A)⁻¹]
  have hB'B : extInner b B' B = extInner b M M / extInner b A A := by
    rw [hB'_eq, extInner_smul_left, ← (note68_homogeneous_reciprocity b hA_mem hB_mem).2,
      note68_normal_shadow_reciprocity, ← hMM, div_eq_inv_mul]
  -- Adapted orthonormal basis for W_B = span v
  have hfinB_eq : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = β := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  obtain ⟨cB, hkB, _, hhB_eq, hregB_eq, hextB_eq, hspanB⟩ :=
    exists_orthonormal_basis_adapted b (Submodule.span ℝ (Set.range v)) hfinB_eq
  let embB : Fin β ↪ Fin n :=
    ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  let sB : Finset (Fin n) := Finset.univ.map embB
  have hsB_card : sB.card = β := by simp [sB]
  let gB := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := sB) hsB_card)
  let cB_v : Fin β → V := fun i => cB (gB i)
  have hcBv_li : LinearIndependent ℝ cB_v := cB.linearIndependent.comp gB gB.injective
  have hspan_gB : Submodule.span ℝ (Set.range cB_v) = Submodule.span ℝ (Set.range v) := by
    rw [← hspanB]
    have hrng : Set.range cB_v = Set.range (fun i : Fin β => cB ⟨i.val, by omega⟩) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
          (Set.powersetCard.ofCard (s := sB) hsB_card) (gB i)).1 ⟨i, rfl⟩
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
        exact ⟨j, by dsimp [cB_v]; rw [← hj]; rfl⟩
      · rintro ⟨j, rfl⟩
        have hm : embB j ∈ sB := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
        obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
          (Set.powersetCard.ofCard (s := sB) hsB_card) (embB j)).2 hm
        exact ⟨i, by dsimp [cB_v]; rw [hi]; rfl⟩
    rw [hrng]
  obtain ⟨μ, hμ⟩ := (plucker_span_eq_iff_proportional v cB_v hv hcBv_li).mp hspan_gB.symm
  have hB_bas : B = (μ : ℝ) • cB.ExteriorAlgebra sB := by
    dsimp [B]
    rw [hμ, ExteriorAlgebra.basis_apply_ofCard cB hsB_card]
    rfl
  have hBB_mu : extInner b B B = (μ : ℝ) ^ 2 := by
    rw [← hextB_eq, hB_bas, extInner_smul_left, extInner_smul_right, extInner_basis, ite_eq_left rfl,
      mul_one, sq]
  let A_sub : ⋀[ℝ]^α V := ⟨A, hA_mem⟩
  let aCoeff : Set.powersetCard (Fin n) α → ℝ := (cB.exteriorPower α).repr A_sub
  have hA_expand : A = ∑ s : Set.powersetCard (Fin n) α, aCoeff s • cB.ExteriorAlgebra s.val := by
    have hval := congrArg Subtype.val ((cB.exteriorPower α).sum_repr A_sub).symm
    change A = ((Submodule.subtype (⋀[ℝ]^α V)) _) at hval
    rw [map_sum] at hval
    refine hval.trans (Finset.sum_congr rfl fun s _ => ?_)
    rw [map_smul, Submodule.coe_subtype, ← ExteriorAlgebra.basis_eq_coe_basis cB s]
  have hAA_sum : extInner b A A = ∑ s : Set.powersetCard (Fin n) α, (aCoeff s) ^ 2 := by
    rw [← hextB_eq, hA_expand]
    simp only [map_sum, LinearMap.sum_apply, extInner_smul_left, extInner_smul_right,
      extInner_basis]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s]
    · rw [ite_eq_left rfl, mul_one, ← sq]
    · intro t _ hts
      have hne : t.val ≠ s.val := fun h => hts (Subtype.ext h)
      rw [ite_eq_right hne, mul_zero, mul_zero]
    · intro hs; exact (hs (Finset.mem_univ s)).elim
  have hA'_expand : A' = ∑ s : Set.powersetCard (Fin n) α,
      (if s.val ⊆ sB then aCoeff s else 0) • cB.ExteriorAlgebra s.val := by
    change (extInner b B B)⁻¹ • regressive b B (hodge b M) = _
    rw [hhM, ← hhB_eq, ← hregB_eq, hBB_mu, hB_bas, smul_regressive, map_smul,
      mul_smul_comm, regressive_smul, smul_smul, smul_smul, hA_expand, Finset.sum_mul,
      regressive_sum_right cB Finset.univ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_mul_assoc, regressive_smul, smul_smul]
    by_cases hsub : s.val ⊆ sB
    · rw [ite_eq_left hsub, regressive_compl_basis_self cB s.val sB hsub]
      congr 1
      have hmu0 : (μ : ℝ) ≠ 0 := μ.ne_zero
      field_simp [hmu0]
    · rw [ite_eq_right hsub]
      have hnd : ¬ Disjoint s.val sBᶜ := fun hd =>
        hsub (disjoint_compl_right_iff.mp hd)
      have hmul0 : cB.ExteriorAlgebra s.val * cB.ExteriorAlgebra sBᶜ = 0 := by
        simpa only [Set.powersetCard.val_ofCard] using
          (ExteriorAlgebra.basis_mul_of_not_disjoint cB
            (Set.powersetCard.ofCard (s := s.val) rfl)
            (Set.powersetCard.ofCard (s := sBᶜ) rfl) hnd)
      rw [hodge_basis cB sB, mul_smul_comm, hmul0, smul_zero, regressive_zero, smul_zero, zero_smul]
  have hA'A'_sum : extInner b A' A' =
      ∑ s : Set.powersetCard (Fin n) α, (if s.val ⊆ sB then aCoeff s else 0) ^ 2 := by
    rw [← hextB_eq, hA'_expand]
    simp only [map_sum, LinearMap.sum_apply, extInner_smul_left, extInner_smul_right,
      extInner_basis]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s]
    · rw [ite_eq_left rfl, mul_one, ← sq]
    · intro t _ hts
      have hne : t.val ≠ s.val := fun h => hts (Subtype.ext h)
      rw [ite_eq_right hne, mul_zero, mul_zero]
    · intro hs; exact (hs (Finset.mem_univ s)).elim
  have hMM_left : extInner b M M = extInner b B B * extInner b A' A' := by
    rw [hMM, ← hextB_eq, hBB_mu, hA'A'_sum, Finset.mul_sum]
    have hAB_sum : A * hodge b B = ∑ s : Set.powersetCard (Fin n) α,
        (aCoeff s * (μ : ℝ)) • (cB.ExteriorAlgebra s.val * hodge cB (cB.ExteriorAlgebra sB)) := by
      rw [← hhB_eq, hB_bas, map_smul, mul_smul_comm, hA_expand, Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [smul_mul_assoc, smul_smul, mul_comm (μ : ℝ) _]
    have hbasis_inner : ∀ s t : Set.powersetCard (Fin n) α,
        extInner cB (cB.ExteriorAlgebra s.val * hodge cB (cB.ExteriorAlgebra sB))
          (cB.ExteriorAlgebra t.val * hodge cB (cB.ExteriorAlgebra sB)) =
          if s = t ∧ s.val ⊆ sB then 1 else 0 := fun s t => by
      by_cases hs : s.val ⊆ sB
      · by_cases hst : s = t
        · subst hst
          rw [ite_eq_left ⟨rfl, hs⟩, ← note68_normal_shadow_reciprocity cB,
            show normalShadowLeft cB (cB.ExteriorAlgebra s.val) (cB.ExteriorAlgebra sB) =
              cB.ExteriorAlgebra s.val from regressive_compl_basis_self cB s.val sB hs,
            extInner_basis, ite_eq_left rfl]
        · rw [ite_eq_right (fun h => hst h.1), hodge_basis cB sB, mul_smul_comm, mul_smul_comm]
          by_cases ht : t.val ⊆ sB
          · have hd_s : Disjoint s.val sBᶜ := disjoint_compl_right_sub hs
            have hd_t : Disjoint t.val sBᶜ := disjoint_compl_right_sub ht
            let ps := Set.powersetCard.ofCard (s := s.val) rfl
            let pt := Set.powersetCard.ofCard (s := t.val) rfl
            let pBc := Set.powersetCard.ofCard (s := sBᶜ) rfl
            have hd_s' : Disjoint (ps : Finset (Fin n)) (pBc : Finset (Fin n)) := hd_s
            have hd_t' : Disjoint (pt : Finset (Fin n)) (pBc : Finset (Fin n)) := hd_t
            have hm_s := ExteriorAlgebra.basis_mul_of_disjoint cB ps pBc hd_s'
            have hm_t := ExteriorAlgebra.basis_mul_of_disjoint cB pt pBc hd_t'
            have hne_u : s.val.disjUnion sBᶜ hd_s ≠ t.val.disjUnion sBᶜ hd_t := fun heq => by
              apply hst
              apply Subtype.ext
              ext x
              by_cases hx : x ∈ sB
              · have hmem := Finset.ext_iff.mp heq x
                have hxc : x ∉ sBᶜ := Finset.notMem_compl.mpr hx
                simpa [Finset.mem_disjUnion, hxc] using hmem
              · constructor
                · intro hx1; exact absurd (hs hx1) hx
                · intro hx2; exact absurd (ht hx2) hx
            change extInner cB
              ((orientationUnit (K := ℝ) sB : ℝ) • (cB.ExteriorAlgebra ↑ps * cB.ExteriorAlgebra ↑pBc))
              ((orientationUnit (K := ℝ) sB : ℝ) • (cB.ExteriorAlgebra ↑pt * cB.ExteriorAlgebra ↑pBc)) = 0
            rw [hm_s, hm_t, Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ,
              ← Int.cast_smul_eq_zsmul ℝ, extInner_smul_left, extInner_smul_right,
              extInner_smul_left, extInner_smul_right, extInner_basis,
              show (↑(Set.powersetCard.disjUnion hd_s') : Finset (Fin n)) =
                s.val.disjUnion sBᶜ hd_s from rfl,
              show (↑(Set.powersetCard.disjUnion hd_t') : Finset (Fin n)) =
                t.val.disjUnion sBᶜ hd_t from rfl,
              ite_eq_right hne_u, mul_zero, mul_zero, mul_zero, mul_zero]
          · have hnd : ¬ Disjoint t.val sBᶜ := fun hd => ht (disjoint_compl_right_iff.mp hd)
            have hm0 : cB.ExteriorAlgebra t.val * cB.ExteriorAlgebra sBᶜ = 0 := by
              simpa only [Set.powersetCard.val_ofCard] using
                (ExteriorAlgebra.basis_mul_of_not_disjoint cB
                  (Set.powersetCard.ofCard (s := t.val) rfl)
                  (Set.powersetCard.ofCard (s := sBᶜ) rfl) hnd)
            rw [extInner_smul_left, extInner_smul_right, hm0, map_zero, mul_zero, mul_zero]
      · have hnd : ¬ Disjoint s.val sBᶜ := fun hd => hs (disjoint_compl_right_iff.mp hd)
        have hm0 : cB.ExteriorAlgebra s.val * cB.ExteriorAlgebra sBᶜ = 0 := by
          simpa only [Set.powersetCard.val_ofCard] using
            (ExteriorAlgebra.basis_mul_of_not_disjoint cB
              (Set.powersetCard.ofCard (s := s.val) rfl)
              (Set.powersetCard.ofCard (s := sBᶜ) rfl) hnd)
        rw [ite_eq_right (fun h => hs h.2), hodge_basis cB sB, mul_smul_comm, hm0, smul_zero,
          map_zero, LinearMap.zero_apply]
    rw [hAB_sum]
    simp only [map_sum, LinearMap.sum_apply, extInner_smul_left, extInner_smul_right]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s]
    · by_cases hs : s.val ⊆ sB
      · rw [hbasis_inner s s, ite_eq_left ⟨rfl, hs⟩, ite_eq_left hs]
        ring
      · rw [hbasis_inner s s, ite_eq_right (fun h => hs h.2), ite_eq_right hs]
        ring
    · intro t _ hts
      have hh := hbasis_inner s t
      rw [ite_eq_right (fun h => hts h.1.symm)] at hh
      rw [extInner_symm cB, hh, mul_zero, mul_zero]
    · intro hs; exact (hs (Finset.mem_univ s)).elim
  have hA'A' : extInner b A' A' = extInner b M M / extInner b B B := by
    rw [hMM_left, mul_comm (extInner b B B), mul_div_cancel_right₀ _ hBB_ne]
  have hMM_le : extInner b M M ≤ extInner b A A * extInner b B B := by
    have hsum_le : extInner b A' A' ≤ extInner b A A := by
      rw [hA'A'_sum, hAA_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      split_ifs
      · exact le_rfl
      · simpa using sq_nonneg (aCoeff s)
    rw [hMM_left, mul_comm (extInner b A A)]
    exact mul_le_mul_of_nonneg_left hsum_le (note68_extInner_cauchy_schwarz b B B).1
  -- Adapted orthonormal basis for W_A = span u
  have hfinA_eq : Module.finrank ℝ (Submodule.span ℝ (Set.range u)) = α := by
    rw [finrank_span_eq_card hu, Fintype.card_fin]
  obtain ⟨cA, hkA, _, hhA_eq, hregA_eq, hextA_eq, hspanA⟩ :=
    exists_orthonormal_basis_adapted b (Submodule.span ℝ (Set.range u)) hfinA_eq
  let embA : Fin α ↪ Fin n :=
    ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  let sA : Finset (Fin n) := Finset.univ.map embA
  have hsA_card : sA.card = α := by simp [sA]
  let gA := Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := sA) hsA_card)
  let cA_u : Fin α → V := fun i => cA (gA i)
  have hcAu_li : LinearIndependent ℝ cA_u := cA.linearIndependent.comp gA gA.injective
  have hspan_gA : Submodule.span ℝ (Set.range cA_u) = Submodule.span ℝ (Set.range u) := by
    rw [← hspanA]
    have hrng : Set.range cA_u = Set.range (fun i : Fin α => cA ⟨i.val, by omega⟩) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
          (Set.powersetCard.ofCard (s := sA) hsA_card) (gA i)).1 ⟨i, rfl⟩
        obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
        exact ⟨j, by dsimp [cA_u]; rw [← hj]; rfl⟩
      · rintro ⟨j, rfl⟩
        have hm : embA j ∈ sA := Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
        obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
          (Set.powersetCard.ofCard (s := sA) hsA_card) (embA j)).2 hm
        exact ⟨i, by dsimp [cA_u]; rw [hi]; rfl⟩
    rw [hrng]
  obtain ⟨ν, hν⟩ := (plucker_span_eq_iff_proportional u cA_u hu hcAu_li).mp hspan_gA.symm
  have hA_bas : A = (ν : ℝ) • cA.ExteriorAlgebra sA := by
    dsimp [A]
    rw [hν, ExteriorAlgebra.basis_apply_ofCard cA hsA_card]
    rfl
  have hAA_nu : extInner b A A = (ν : ℝ) ^ 2 := by
    rw [← hextA_eq, hA_bas, extInner_smul_left, extInner_smul_right, extInner_basis, ite_eq_left rfl,
      mul_one, sq]
  let B_sub : ⋀[ℝ]^β V := ⟨B, hB_mem⟩
  let bCoeff : Set.powersetCard (Fin n) β → ℝ := (cA.exteriorPower β).repr B_sub
  have hB_expand : B = ∑ t : Set.powersetCard (Fin n) β, bCoeff t • cA.ExteriorAlgebra t.val := by
    have hval := congrArg Subtype.val ((cA.exteriorPower β).sum_repr B_sub).symm
    change B = ((Submodule.subtype (⋀[ℝ]^β V)) _) at hval
    rw [map_sum] at hval
    refine hval.trans (Finset.sum_congr rfl fun t _ => ?_)
    rw [map_smul, Submodule.coe_subtype, ← ExteriorAlgebra.basis_eq_coe_basis cA t]
  have hB'_expand : B' = ∑ t : Set.powersetCard (Fin n) β,
      (if sA ⊆ t.val then bCoeff t else 0) • cA.ExteriorAlgebra t.val := by
    rw [hB'_eq]
    change (extInner b A A)⁻¹ • (A * regressive b B (hodge b A)) = _
    rw [← hhA_eq, ← hregA_eq, hAA_nu, hA_bas, smul_mul_assoc, map_smul, regressive_smul,
      mul_smul_comm, smul_smul, smul_smul, hB_expand, regressive_sum_left cA Finset.univ,
      Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_regressive, mul_smul_comm, smul_smul]
    by_cases hsub : sA ⊆ t.val
    · rw [ite_eq_left hsub, mul_regressive_compl_basis_self cA t.val sA hsub]
      congr 1
      have hnu0 : (ν : ℝ) ≠ 0 := ν.ne_zero
      field_simp [hnu0]
    · rw [ite_eq_right hsub]
      have hnd : ¬ Disjoint t.valᶜ sA := fun hd => hsub (disjoint_compl_left_iff.mp hd)
      have hm0 : cA.ExteriorAlgebra t.valᶜ * cA.ExteriorAlgebra sA = 0 := by
        simpa only [Set.powersetCard.val_ofCard] using
          (ExteriorAlgebra.basis_mul_of_not_disjoint cA
            (Set.powersetCard.ofCard (s := t.valᶜ) rfl)
            (Set.powersetCard.ofCard (s := sA) rfl) hnd)
      have hreg0 : regressive cA (cA.ExteriorAlgebra t.val)
          (hodge cA (cA.ExteriorAlgebra sA)) = 0 := by
        apply (hodge cA).injective
        rw [hodge_regressive, hodge_basis cA t.val, hodge_hodge_basis cA sA, smul_mul_assoc,
          mul_smul_comm, hm0, smul_zero, smul_zero, map_zero]
      rw [hreg0, mul_zero, smul_zero, zero_smul]
  have hB'B'_sum : extInner b B' B' =
      ∑ t : Set.powersetCard (Fin n) β, (if sA ⊆ t.val then bCoeff t else 0) ^ 2 := by
    rw [← hextA_eq, hB'_expand]
    simp only [map_sum, LinearMap.sum_apply, extInner_smul_left, extInner_smul_right,
      extInner_basis]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single t]
    · rw [ite_eq_left rfl, mul_one, ← sq]
    · intro s _ hst
      have hne : s.val ≠ t.val := fun h => hst (Subtype.ext h)
      rw [ite_eq_right hne, mul_zero, mul_zero]
    · intro ht; exact (ht (Finset.mem_univ t)).elim
  have hMM_right : extInner b M M = extInner b A A * extInner b B' B' := by
    have hrec_eq : extInner b M M = extInner b (regressive b B (hodge b A))
        (regressive b B (hodge b A)) := by
      rw [hMM, (note68_homogeneous_reciprocity b hA_mem hB_mem).1]
    rw [hrec_eq, ← hextA_eq, ← hhA_eq, ← hregA_eq, hAA_nu, hB'B'_sum, Finset.mul_sum]
    have hBA_sum : regressive cA B (hodge cA A) = ∑ t : Set.powersetCard (Fin n) β,
        (bCoeff t * (ν : ℝ)) • regressive cA (cA.ExteriorAlgebra t.val)
          (hodge cA (cA.ExteriorAlgebra sA)) := by
      rw [hA_bas, map_smul, hB_expand]
      dsimp only [regressive]
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc, mul_smul_comm, Finset.smul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [smul_smul, mul_comm (ν : ℝ) _]
    have hbasis_inner : ∀ s t : Set.powersetCard (Fin n) β,
        extInner cA (regressive cA (cA.ExteriorAlgebra s.val) (hodge cA (cA.ExteriorAlgebra sA)))
          (regressive cA (cA.ExteriorAlgebra t.val) (hodge cA (cA.ExteriorAlgebra sA))) =
          if s = t ∧ sA ⊆ s.val then 1 else 0 := fun s t => by
      by_cases hs : sA ⊆ s.val
      · by_cases hst : s = t
        · subst hst
          rw [ite_eq_left ⟨rfl, hs⟩]
          have hrc := note68_homogeneous_reciprocity cA (basis_mem_exteriorPower cA sA)
            (basis_mem_exteriorPower cA s.val)
          have hnr := note68_normal_shadow_reciprocity cA
            (cA.ExteriorAlgebra sA) (cA.ExteriorAlgebra s.val)
          have hmul_eq : normalShadowRight cA (cA.ExteriorAlgebra sA) (cA.ExteriorAlgebra s.val) =
              cA.ExteriorAlgebra s.val := by
            dsimp [normalShadowRight]
            exact mul_regressive_compl_basis_self cA s.val sA hs
          rw [← hrc.1, ← hnr, hrc.2, hmul_eq, extInner_basis, ite_eq_left rfl]
        · rw [ite_eq_right (fun h => hst h.1), ← extInner_hodge_isometry cA,
            hodge_regressive, hodge_regressive, hodge_hodge_basis cA sA,
            hodge_basis cA s.val, hodge_basis cA t.val,
            smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
            extInner_smul_left, extInner_smul_left, extInner_smul_right, extInner_smul_right]
          by_cases ht : sA ⊆ t.val
          · have hds : Disjoint s.valᶜ sA := disjoint_compl_left_sub hs
            have hdt : Disjoint t.valᶜ sA := disjoint_compl_left_sub ht
            let psc := Set.powersetCard.ofCard (s := s.valᶜ) rfl
            let ptc := Set.powersetCard.ofCard (s := t.valᶜ) rfl
            let psA := Set.powersetCard.ofCard (s := sA) rfl
            have hds' : Disjoint (psc : Finset (Fin n)) (psA : Finset (Fin n)) := hds
            have hdt' : Disjoint (ptc : Finset (Fin n)) (psA : Finset (Fin n)) := hdt
            have hms := ExteriorAlgebra.basis_mul_of_disjoint cA psc psA hds'
            have hmt := ExteriorAlgebra.basis_mul_of_disjoint cA ptc psA hdt'
            have hne_u : s.valᶜ.disjUnion sA hds ≠ t.valᶜ.disjUnion sA hdt := fun heq => by
              apply hst
              apply Subtype.ext
              ext x
              by_cases hx : x ∈ sA
              · simp [hs hx, ht hx]
              · have hmem := Finset.ext_iff.mp heq x
                have hm' : x ∉ s.val ↔ x ∉ t.val := by
                  simpa [Finset.mem_disjUnion, hx] using hmem
                exact not_iff_not.mp hm'
            change _ * (_ * (_ * (_ * extInner cA
              (cA.ExteriorAlgebra ↑psc * cA.ExteriorAlgebra ↑psA)
              (cA.ExteriorAlgebra ↑ptc * cA.ExteriorAlgebra ↑psA)))) = 0
            rw [hms, hmt, Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ,
              ← Int.cast_smul_eq_zsmul ℝ, extInner_smul_left, extInner_smul_right,
              extInner_basis,
              show (↑(Set.powersetCard.disjUnion hds') : Finset (Fin n)) =
                s.valᶜ.disjUnion sA hds from rfl,
              show (↑(Set.powersetCard.disjUnion hdt') : Finset (Fin n)) =
                t.valᶜ.disjUnion sA hdt from rfl,
              ite_eq_right hne_u, mul_zero, mul_zero, mul_zero, mul_zero, mul_zero, mul_zero]
          · have hnd : ¬ Disjoint t.valᶜ sA := fun hd => ht (disjoint_compl_left_iff.mp hd)
            have hm0 : cA.ExteriorAlgebra t.valᶜ * cA.ExteriorAlgebra sA = 0 := by
              simpa only [Set.powersetCard.val_ofCard] using
                (ExteriorAlgebra.basis_mul_of_not_disjoint cA
                  (Set.powersetCard.ofCard (s := t.valᶜ) rfl)
                  (Set.powersetCard.ofCard (s := sA) rfl) hnd)
            rw [hm0, map_zero, mul_zero, mul_zero, mul_zero, mul_zero]
      · rw [ite_eq_right (fun h => hs h.2), ← extInner_hodge_isometry cA,
          hodge_regressive, hodge_hodge_basis cA sA, hodge_basis cA s.val,
          smul_mul_assoc, mul_smul_comm]
        have hnd : ¬ Disjoint s.valᶜ sA := fun hd => hs (disjoint_compl_left_iff.mp hd)
        have hm0 : cA.ExteriorAlgebra s.valᶜ * cA.ExteriorAlgebra sA = 0 := by
          simpa only [Set.powersetCard.val_ofCard] using
            (ExteriorAlgebra.basis_mul_of_not_disjoint cA
              (Set.powersetCard.ofCard (s := s.valᶜ) rfl)
              (Set.powersetCard.ofCard (s := sA) rfl) hnd)
        rw [hm0, smul_zero, smul_zero, map_zero, LinearMap.zero_apply]
    rw [hBA_sum]
    simp only [map_sum, LinearMap.sum_apply, extInner_smul_left, extInner_smul_right]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s]
    · by_cases hs : sA ⊆ s.val
      · rw [hbasis_inner s s, ite_eq_left ⟨rfl, hs⟩, ite_eq_left hs]
        ring
      · rw [hbasis_inner s s, ite_eq_right (fun h => hs h.2), ite_eq_right hs]
        ring
    · intro t _ hts
      have hh := hbasis_inner s t
      rw [ite_eq_right (fun h => hts h.1.symm)] at hh
      rw [extInner_symm cA, hh, mul_zero, mul_zero]
    · intro hs; exact (hs (Finset.mem_univ s)).elim
  have hB'B' : extInner b B' B' = extInner b M M / extInner b A A := by
    rw [hMM_right, mul_comm (extInner b A A), mul_div_cancel_right₀ _ hAA_ne]
  have hcos : (extInner b A A') ^ 2 * (extInner b B B * extInner b B' B') =
      (extInner b B' B) ^ 2 * (extInner b A A * extInner b A' A') := by
    rw [hAA', hA'A', hB'B, hB'B']
    field_simp [hAA_ne, hBB_ne]
  refine ⟨hAA', hA'A', hB'B, hB'B', hcos, hMM_le, extInner_hodge_isometry b⟩

end Notes68_70UnequalShadowAngles

end InfoGeometry.Projective.GrassmannSubspaceShadowsResultantAndHadamard
