/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Grassmann–Plücker Subspace Equivalence, Regressive Meet Dichotomy, Exterior Cramer, & Circle Space

Wave II formalization of Hermann Grassmann's *Ausdehnungslehre* (1862) and its editorial/supplementary
notes (`hmath019-endmatter.pdf`):

1. **`GA₉` (`Nos. 63, 70`, Seligman `p. 393`)**:
   Universal alternating determinant identity `alternatingMap_apply_eq_det_smul`, Grassmann No. 63
   (`ιMulti_eq_det_smul_volume`), and Grassmann No. 70 / Plücker subspace equivalence
   (`plucker_span_eq_iff_proportional` and `plucker_projective_eq_iff_span_eq`).
2. **`GA₁₀` (`No. 87`, Editorial Note 33 `p. 342`, Seligman `p. 394` — closing the first boundary
   note of `ExteriorRegressive.lean`)**:
   Complete characterization of the regressive product of two independent blades:
   - Non-spanning dichotomy (`U ⊔ W ≠ ⊤ → regressive b (ιMulti v) (ιMulti w) = 0`), with an
     explicit `K^4` countermodel where `U ⊓ W ≠ ⊥` yet `regressive b A B = 0`.
   - Spanning intersection theorem (`U ⊔ W = ⊤ → regressive b (ιMulti v) (ιMulti w) ≠ 0 ∧
     bladeSupport (regressive b (ιMulti v) (ιMulti w)) = U ⊓ W`).
3. **`GA₁₁` (`No. 134`, Editorial Note 45 `pp. 347–349`, Seligman `p. 395`)**:
   Grassmann's exterior Cramer's rule over arbitrary commutative rings (`exterior_cramer_ιMulti`)
   and scalar volume readout over fields (`exterior_cramer_volCoord`).
4. **`GA₁₂` (`Nos. 396, 405–409`, Notes 95–97 `pp. 369–370`, Seligman `p. 397`)**:
   Lorentzian circle space `(Fin 4 → ℝ)` with `circleBilin` signature `(1, 3)`, exact double-distance
   and orthogonal-circle inner products (`grassmann_no396_double_distance`), E. Müller's Note 95
   supplementary orthogonal circle (`mueller_note95_orthogonal_supplement`), and Note 97 proving that
   every `GL(4, ℝ)` preserves syncyclicity and every `O(circleBilin)` preserves tangency, while
   a syncyclic shift sends tangent circles to non-tangent circles (`note97_syncyclic_vs_moebius_tangency`).
-/

noncomputable section

namespace InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace

open InfoGeometry.Projective.ExteriorRegressive
open InfoGeometry.Projective.ExteriorBladeIncidence
open InfoGeometry.Projective.GrassmannAusdehnungslehreRegressiveShadow
open scoped Matrix

/-! ## 1. Universal Alternating Determinant Formula & Plücker Subspace Equivalence (`Nos. 63, 70`) -/

section PluckerEquivalenceNo70

/-- **Grassmann No. 63 / Universal Alternating Determinant Theorem**:
for any basis `e : Basis ι R M`, every `N`-valued alternating map `f` transforms under arbitrary
vectors `v : ι → M` by the determinant scalar `e.det v`. -/
theorem alternatingMap_apply_eq_det_smul {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι R M) (f : M [⋀^ι]→ₗ[R] N) (v : ι → M) :
    f v = (e.det v) • f e := by
  have heq : f = e.det.smulRight (f e) := by
    refine Module.Basis.ext_alternating e fun i hi => ?_
    let σ : Equiv.Perm ι := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change f (e ∘ σ) = (e.det (e ∘ σ)) • f e
    rw [AlternatingMap.map_perm f e σ, AlternatingMap.map_perm e.det e σ, e.det_self,
      Units.smul_def, smul_assoc, one_smul, ← Units.smul_def]
  exact DFunLike.congr_fun heq v

/-- Every `Ord`-embedding `Fin n ↪o Fin n` equals the identity map. -/
private theorem orderEmbedding_fin_eq_id {n : ℕ} (g : Fin n ↪o Fin n) (i : Fin n) :
    g i = i := by
  have hsub1 : (Finset.Ici i).image g ⊆ Finset.Ici (g i) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_Ici.mpr (g.monotone (Finset.mem_Ici.mp hx))
  have hsub2 : Finset.Ici (g i) ⊆ Finset.Ici i := fun y hy =>
    Finset.mem_Ici.mpr (le_trans (g.strictMono.id_le i) (Finset.mem_Ici.mp hy))
  have heq_set : Finset.Ici (g i) = Finset.Ici i :=
    Finset.eq_of_subset_of_card_le hsub2
      (by simpa [Finset.card_image_of_injective _ g.injective] using Finset.card_le_card hsub1)
  have hi_mem : i ∈ Finset.Ici (g i) := heq_set ▸ Finset.mem_Ici.mpr le_rfl
  exact le_antisymm (Finset.mem_Ici.mp hi_mem) (g.strictMono.id_le i)

/-- **Grassmann No. 63 (`p. 393`)**: over any commutative ring `R`, the `n`-fold exterior product of
any `n` vectors equals `b.det v` times the top basis blade `b.ExteriorAlgebra Finset.univ`. -/
theorem ιMulti_eq_det_smul_volume {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (b : Module.Basis (Fin n) R M) (v : Fin n → M) :
    ExteriorAlgebra.ιMulti R n v = (b.det v) • b.ExteriorAlgebra Finset.univ := by
  have hvol : b.ExteriorAlgebra Finset.univ = ExteriorAlgebra.ιMulti R n b := by
    rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin n)]
    change ExteriorAlgebra.ιMulti R n (fun i => b (Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_fin n)) i)) = ExteriorAlgebra.ιMulti R n b
    congr 1
    funext i
    rw [orderEmbedding_fin_eq_id]
  rw [hvol]
  exact alternatingMap_apply_eq_det_smul b (ExteriorAlgebra.ιMulti R n) v

/-- **Grassmann No. 70 / Plücker Subspace Equivalence (`p. 393`)**:
two linearly independent `m`-frames have the exact same spanned subspace iff their exterior blades
differ by a nonzero scalar unit `c : Kˣ`. -/
theorem plucker_span_eq_iff_proportional {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : ℕ} (v w : Fin m → V) (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    Submodule.span K (Set.range v) = Submodule.span K (Set.range w) ↔
      ∃ c : Kˣ, ExteriorAlgebra.ιMulti K m v = (c : K) • ExteriorAlgebra.ιMulti K m w := by
  constructor
  · intro hspan
    let W := Submodule.span K (Set.range w)
    let bW : Module.Basis (Fin m) K W := Module.Basis.span hw
    let v' : Fin m → W := fun i =>
      ⟨v i, by dsimp [W]; rw [← hspan]; exact Submodule.subset_span (Set.mem_range_self i)⟩
    have hv'_li : LinearIndependent K v' :=
      (show LinearIndependent K (W.subtype ∘ v') from hv).of_comp
    have htop_v' : ⊤ ≤ Submodule.span K (Set.range v') := by
      rintro ⟨x, hx⟩ _
      have hx' : x ∈ Submodule.span K (Set.range v) := hspan.symm ▸ hx
      rw [Submodule.mem_span_range_iff_exists_fun] at hx' ⊢
      obtain ⟨c, rfl⟩ := hx'
      refine ⟨c, ?_⟩
      ext
      simp [v']
    let bV : Module.Basis (Fin m) K W := Module.Basis.mk hv'_li htop_v'
    let f : W [⋀^Fin m]→ₗ[K] ExteriorAlgebra K V :=
      (ExteriorAlgebra.ιMulti K m).compLinearMap W.subtype
    have hf := alternatingMap_apply_eq_det_smul bW f bV
    have hfv : f bV = ExteriorAlgebra.ιMulti K m v := by
      change ExteriorAlgebra.ιMulti K m (fun i => W.subtype (bV i)) = _
      congr 1
      funext i
      simp [bV, Module.Basis.mk_apply, v']
    have hfw : f bW = ExteriorAlgebra.ιMulti K m w := by
      change ExteriorAlgebra.ιMulti K m (fun i => W.subtype (bW i)) = _
      congr 1
      funext i
      exact Module.Basis.coe_span_apply hw i
    rw [hfv, hfw] at hf
    exact ⟨(bW.isUnit_det bV).unit, hf⟩
  · rintro ⟨c, hc⟩
    exact span_eq_of_proportional v w hv hw c.ne_zero hc

/-- Projective point equality on `ℙ K (ExteriorAlgebra K V)` characterizes subspace equality. -/
theorem plucker_projective_eq_iff_span_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {m : ℕ} (v w : Fin m → V) (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    Projectivization.mk K (ExteriorAlgebra.ιMulti K m v) (ιMulti_ne_zero_of_linearIndependent v hv) =
      Projectivization.mk K (ExteriorAlgebra.ιMulti K m w) (ιMulti_ne_zero_of_linearIndependent w hw) ↔
      Submodule.span K (Set.range v) = Submodule.span K (Set.range w) := by
  rw [Projectivization.mk_eq_mk_iff, plucker_span_eq_iff_proportional v w hv hw]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

end PluckerEquivalenceNo70

/-! ## 2. Regressive Subspace Meet Dichotomy (`No. 87`, Note 33 `p. 342`, Seligman `p. 394`) -/

section RegressiveSubspaceMeet

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Any nonzero covector `d : Dual K V` equals the `i₀`-th dual basis element of a constructed
ordered basis `b'` of `V` adapted to `ker d`. -/
private theorem exists_basis_dualBasis_eq {n : ℕ} (b : Module.Basis (Fin n) K V)
    {d : Module.Dual K V} (hd : d ≠ 0) :
    ∃ (b' : Module.Basis (Fin n) K V) (i₀ : Fin n), d = b'.dualBasis i₀ := by
  have hex : ∃ v₀ : V, d v₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (LinearMap.ext h)
  obtain ⟨v₀, hv₀⟩ := hex
  have hn : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := by omega
    subst hn0
    have hvz : v₀ = 0 := by simpa using (b.sum_repr v₀).symm
    exact hv₀ (by simp [hvz])
  let x₀ : V := (d v₀)⁻¹ • v₀
  have hx₀ : d x₀ = 1 := by simp [x₀, inv_mul_cancel₀ hv₀]
  let m := n - 1
  have hm : m + 1 = n := Nat.sub_add_cancel hn
  have : Module.Finite K V := Module.Finite.of_basis b
  have hfinV : Module.finrank K V = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hrange_top : LinearMap.range d = ⊤ :=
    Submodule.eq_top_iff'.2 fun r => ⟨r • x₀, by simp [hx₀]⟩
  have hker_rank : Module.finrank K (LinearMap.ker d) = m := by
    have hrt := LinearMap.finrank_range_add_finrank_ker d
    rw [hrange_top, finrank_top, Module.finrank_self, hfinV] at hrt
    omega
  let u : Module.Basis (Fin m) K (LinearMap.ker d) :=
    Module.finBasisOfFinrankEq K (LinearMap.ker d) hker_rank
  let fam : Fin (m + 1) → V := Fin.cons x₀ (fun j => (u j : V))
  have hli_tail : LinearIndependent K (fun j : Fin m => (u j : V)) :=
    u.linearIndependent.map' (LinearMap.ker d).subtype (Submodule.ker_subtype (LinearMap.ker d))
  have hx₀_notMem : x₀ ∉ Submodule.span K (Set.range fun j : Fin m => (u j : V)) := by
    intro hmem
    have hle : Submodule.span K (Set.range fun j : Fin m => (u j : V)) ≤ LinearMap.ker d := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (u j).2
    have hx_ker := hle hmem
    rw [LinearMap.mem_ker, hx₀] at hx_ker
    exact one_ne_zero hx_ker
  have hli_fam : LinearIndependent K fam :=
    linearIndependent_finCons.2 ⟨hli_tail, hx₀_notMem⟩
  have hspan_fam : ⊤ ≤ Submodule.span K (Set.range fam) := by
    intro z _
    let kvec : LinearMap.ker d := ⟨z - d z • x₀, by simp [hx₀]⟩
    have hk_span : kvec ∈ Submodule.span K (Set.range u) := by
      rw [u.span_eq]
      trivial
    have hk_map : (kvec : V) ∈ Submodule.span K (Set.range fun j : Fin m => (u j : V)) := by
      have hm' := Submodule.mem_map_of_mem (f := (LinearMap.ker d).subtype) hk_span
      rwa [Submodule.map_span, ← Set.range_comp] at hm'
    have hsub_fam : Submodule.span K (Set.range fun j : Fin m => (u j : V)) ≤
        Submodule.span K (Set.range fam) := by
      apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨j.succ, rfl⟩
    have hx_mem : d z • x₀ ∈ Submodule.span K (Set.range fam) :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    simpa [kvec] using Submodule.add_mem _ hx_mem (hsub_fam hk_map)
  let b₀ : Module.Basis (Fin (m + 1)) K V := Module.Basis.mk hli_fam hspan_fam
  let b' : Module.Basis (Fin n) K V := b₀.reindex (finCongr hm)
  let i₀ : Fin n := finCongr hm 0
  refine ⟨b', i₀, ?_⟩
  apply b'.ext
  intro j
  obtain ⟨k, rfl⟩ := (finCongr hm).surjective j
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨q, rfl⟩
  · have hbi : b' i₀ = x₀ := by simp [b', b₀, i₀, fam]
    change d (b' i₀) = b'.dualBasis i₀ (b' i₀)
    rw [b'.dualBasis_apply_self, ite_eq_left rfl, hbi, hx₀]
  · have hne : finCongr hm q.succ ≠ i₀ := fun h =>
      Fin.succ_ne_zero q ((finCongr hm).injective h)
    have hbq : b' (finCongr hm q.succ) = (u q : V) := by simp [b', b₀, fam]
    rw [b'.dualBasis_apply_self, ite_eq_right hne, hbq]
    exact (u q).2

private theorem contractLeft_ιMulti_eq_zero_of_dual {d : Module.Dual K V} :
    ∀ {r : ℕ} (v : Fin r → V), (∀ i, d (v i) = 0) →
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) d
        (ExteriorAlgebra.ιMulti K r v) = 0
  | 0, _, _ => by simp [CliffordAlgebra.contractLeft_one]
  | r + 1, v, hv => by
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    have hι0 : CliffordAlgebra.ι (0 : QuadraticForm K V) (v 0) = ExteriorAlgebra.ι K (v 0) := rfl
    have hmul := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm K V)) d (v 0)
      (ExteriorAlgebra.ιMulti K r (Matrix.vecTail v))
    rw [hι0] at hmul
    rw [hmul, hv 0, zero_smul, zero_sub,
      contractLeft_ιMulti_eq_zero_of_dual (Matrix.vecTail v) (fun i => hv i.succ),
      mul_zero, neg_zero]

/-- If a nonzero covector `d` contracts both homogeneous `A` and `B` to zero, then their
regressive product vanishes (`regressive b A B = 0`). -/
theorem regressive_eq_zero_of_common_covector {n r s : ℕ} (b : Module.Basis (Fin n) K V)
    {d : Module.Dual K V} (hd : d ≠ 0) {A B : ExteriorAlgebra K V}
    (hA : A ∈ ⋀[K]^r V) (hB : B ∈ ⋀[K]^s V)
    (hcA : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) d A = 0)
    (hcB : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) d B = 0) :
    regressive b A B = 0 := by
  by_cases hr : n < r
  · rw [exteriorPower_eq_zero_of_gt b hr hA, zero_regressive]
  by_cases hs : n < s
  · rw [exteriorPower_eq_zero_of_gt b hs hB, regressive_zero]
  obtain ⟨b', i₀, rfl⟩ := exists_basis_dualBasis_eq b hd
  have hcA' : hodge b' A * ExteriorAlgebra.ι K (b' i₀) = 0 := by
    apply (hodge b').injective
    rw [hodge_mul_ι_basis, hodge_hodge_exteriorPower b' hA, LinearMap.map_smul, hcA,
      smul_zero, map_zero]
  have hcB' : hodge b' B * ExteriorAlgebra.ι K (b' i₀) = 0 := by
    apply (hodge b').injective
    rw [hodge_mul_ι_basis, hodge_hodge_exteriorPower b' hB, LinearMap.map_smul, hcB,
      smul_zero, map_zero]
  have hcB_left : ExteriorAlgebra.ι K (b' i₀) * hodge b' B = 0 := by
    rw [ι_mul_exteriorPower_comm (b' i₀) (hodge_mem_exteriorPower b' hB), hcB', smul_zero]
  have hB_decomp : hodge b' B =
      ExteriorAlgebra.ι K (b' i₀) *
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V)) (b'.dualBasis i₀)
          (hodge b' B) := by
    have hcm := CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm K V))
      (b'.dualBasis i₀) (b' i₀) (hodge b' B)
    have hι0 : CliffordAlgebra.ι (0 : QuadraticForm K V) (b' i₀) =
        ExteriorAlgebra.ι K (b' i₀) := rfl
    rw [hι0] at hcm
    rw [hcB_left, map_zero, b'.dualBasis_apply_self, ite_eq_left rfl, one_smul] at hcm
    exact eq_of_sub_eq_zero hcm.symm
  have hprod : hodge b' A * hodge b' B = 0 := by
    calc
      hodge b' A * hodge b' B
          = hodge b' A * (ExteriorAlgebra.ι K (b' i₀) *
              CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V))
                (b'.dualBasis i₀) (hodge b' B)) := by
            conv_lhs => rw [hB_decomp]
      _ = (hodge b' A * ExteriorAlgebra.ι K (b' i₀)) *
            CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K V))
              (b'.dualBasis i₀) (hodge b' B) := by
            simp only [mul_assoc]
      _ = 0 := by rw [hcA', zero_mul]
  have hb'_zero : regressive b' A B = 0 := by
    apply (hodge b').injective
    rw [hodge_regressive, hprod, map_zero]
  rw [← det_smul_regressive_change_basis b b' A B, hb'_zero, smul_zero]

/-- **Regressive Non-Spanning Vanishing**: if `span v ⊔ span w ≠ ⊤`, then
`regressive b (ιMulti v) (ιMulti w) = 0`. -/
theorem regressive_ιMulti_eq_zero_of_sup_ne_top {n r s : ℕ} (b : Module.Basis (Fin n) K V)
    (v : Fin r → V) (w : Fin s → V)
    (hsup : Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w) ≠ ⊤) :
    regressive b (ExteriorAlgebra.ιMulti K r v) (ExteriorAlgebra.ιMulti K s w) = 0 := by
  let S := Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w)
  have hex : ∃ v₀ : V, v₀ ∉ S := by
    by_contra h
    push Not at h
    exact hsup (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨v₀, hv₀⟩ := hex
  have hq_ne : S.mkQ v₀ ≠ 0 := by
    intro hz
    exact hv₀ ((Submodule.Quotient.mk_eq_zero S).mp hz)
  obtain ⟨dq, hdq⟩ := Module.Projective.exists_dual_eq_one K hq_ne
  let d : Module.Dual K V := dq.comp S.mkQ
  have hd_ne : d ≠ 0 := by
    intro h0
    have h1 : d v₀ = 0 := by simp [h0]
    have h2 : d v₀ = 1 := hdq
    exact one_ne_zero (h2.symm.trans h1)
  have hdv : ∀ i, d (v i) = 0 := fun i => by
    have hm : v i ∈ S := Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
    have hq : S.mkQ (v i) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hm
    change dq (S.mkQ (v i)) = 0
    rw [hq, map_zero]
  have hdw : ∀ j, d (w j) = 0 := fun j => by
    have hm : w j ∈ S := Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
    have hq : S.mkQ (w j) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hm
    change dq (S.mkQ (w j)) = 0
    rw [hq, map_zero]
  exact regressive_eq_zero_of_common_covector b hd_ne
    (ExteriorAlgebra.ιMulti_range K r ⟨v, rfl⟩)
    (ExteriorAlgebra.ιMulti_range K s ⟨w, rfl⟩)
    (contractLeft_ιMulti_eq_zero_of_dual v hdv)
    (contractLeft_ιMulti_eq_zero_of_dual w hdw)

/-- **`[countermodel_found]` (resolves the boundary remark of `ExteriorRegressive.lean`)**:
in `K^4`, two decomposable bivectors sharing a line (`bladeSupport A ⊓ bladeSupport B ≠ ⊥`) yet
failing to span `K^4` satisfy `regressive b A B = 0`. -/
theorem regressive_non_spanning_counterexample_dim4 (K : Type*) [Field K] :
    let b := Pi.basisFun K (Fin 4)
    let A := ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)
    let B := ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)
    bladeSupport A ⊓ bladeSupport B ≠ ⊥ ∧ regressive b A B = 0 := by
  intro b A B
  let v : Fin 2 → (Fin 4 → K) := ![b 0, b 1]
  let w : Fin 2 → (Fin 4 → K) := ![b 0, b 2]
  have hA_eq : A = ExteriorAlgebra.ιMulti K 2 v := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl
  have hB_eq : B = ExteriorAlgebra.ιMulti K 2 w := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    rfl
  have h0A : b 0 ∈ bladeSupport A := by
    rw [mem_bladeSupport]
    dsimp [A]
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  have h0B : b 0 ∈ bladeSupport B := by
    rw [mem_bladeSupport]
    dsimp [B]
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  refine ⟨?_, ?_⟩
  · intro hbot
    have hm : b 0 ∈ (⊥ : Submodule K (Fin 4 → K)) := hbot ▸ ⟨h0A, h0B⟩
    exact b.ne_zero 0 ((Submodule.mem_bot K).mp hm)
  · have hsup : Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w) ≠ ⊤ := by
      intro htop
      have h3mem : b 3 ∈ Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w) :=
        htop ▸ Submodule.mem_top
      have hle : Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w) ≤
          LinearMap.ker (b.dualBasis 3) := by
        refine sup_le ?_ ?_
        all_goals
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          fin_cases i <;> simp [v, w]
      have hk := hle h3mem
      rw [LinearMap.mem_ker, b.dualBasis_apply_self, ite_eq_left rfl] at hk
      exact one_ne_zero hk
    rw [hA_eq, hB_eq]
    exact regressive_ιMulti_eq_zero_of_sup_ne_top b v w hsup

theorem range_fin_append {α : Type*} {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
    Set.range (Fin.append a b) = Set.range a ∪ Set.range b := by
  ext x
  simp only [Set.mem_range, Set.mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl ⟨j, by simp⟩
    · exact Or.inr ⟨j, by simp⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd n j, by simp⟩
    · exact ⟨Fin.natAdd m j, by simp⟩

private theorem ιMulti_fin_append_congr {r s m : ℕ} (hrs : r + s = m)
    (v : Fin r → V) (w : Fin s → V) :
    ExteriorAlgebra.ιMulti K m ((Fin.append v w) ∘ (finCongr hrs).symm) =
      ExteriorAlgebra.ιMulti K r v * ExteriorAlgebra.ιMulti K s w := by
  subst hrs
  have hcomp : ((Fin.append v w) ∘ (finCongr rfl).symm) = Fin.append v w := rfl
  rw [hcomp, ExteriorAlgebra.ιMulti_mul_ιMulti]

/-- **Grassmann No. 87 & Editorial Note 33 (`p. 342`, Seligman `p. 394`)**:
when two independent blades `ιMulti K r v` and `ιMulti K s w` span `V` (`U ⊔ W = ⊤`), their
regressive product is nonzero and its annihilator support `bladeSupport` equals the intersection
`U ⊓ W` (`r + s - n`-dimensional). -/
theorem regressive_blade_intersection_of_sup_eq_top {n r s : ℕ} (b : Module.Basis (Fin n) K V)
    (v : Fin r → V) (w : Fin s → V)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w)
    (hsup : Submodule.span K (Set.range v) ⊔ Submodule.span K (Set.range w) = ⊤) :
    regressive b (ExteriorAlgebra.ιMulti K r v) (ExteriorAlgebra.ιMulti K s w) ≠ 0 ∧
      bladeSupport (regressive b (ExteriorAlgebra.ιMulti K r v) (ExteriorAlgebra.ιMulti K s w)) =
        Submodule.span K (Set.range v) ⊓ Submodule.span K (Set.range w) := by
  let U := Submodule.span K (Set.range v)
  let W := Submodule.span K (Set.range w)
  let I := U ⊓ W
  have : Module.Finite K V := Module.Finite.of_basis b
  obtain ⟨U₁', hU₁'⟩ := (I.comap U.subtype).exists_isCompl
  obtain ⟨W₁', hW₁'⟩ := (I.comap W.subtype).exists_isCompl
  let U₁ := U₁'.map U.subtype
  let W₁ := W₁'.map W.subtype
  have hI_le_U : I ≤ U := inf_le_left
  have hI_le_W : I ≤ W := inf_le_right
  have hIU_disj : Disjoint I U₁ := by
    rw [disjoint_iff_inf_le]
    intro x ⟨hxI, hxU₁⟩
    rcases hxU₁ with ⟨y, hyU₁, rfl⟩
    have hyI : y ∈ I.comap U.subtype := hxI
    have hbot := hU₁'.disjoint.le_bot ⟨hyI, hyU₁⟩
    rw [Submodule.mem_bot] at hbot
    simp [hbot]
  have hIW_disj : Disjoint I W₁ := by
    rw [disjoint_iff_inf_le]
    intro x ⟨hxI, hxW₁⟩
    rcases hxW₁ with ⟨y, hyW₁, rfl⟩
    have hyI : y ∈ I.comap W.subtype := hxI
    have hbot := hW₁'.disjoint.le_bot ⟨hyI, hyW₁⟩
    rw [Submodule.mem_bot] at hbot
    simp [hbot]
  have hIU_sup : I ⊔ U₁ = U := by
    apply le_antisymm (sup_le hI_le_U (Submodule.map_subtype_le _ _))
    intro x hxU
    let xu : U := ⟨x, hxU⟩
    have hcod := hU₁'.codisjoint.eq_top
    have hmem : xu ∈ (I.comap U.subtype) ⊔ U₁' := hcod.symm ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at hmem
    obtain ⟨a, ha, b₁, hb₁, hab⟩ := hmem
    have hx_eq : x = (a : V) + (b₁ : V) := congrArg Subtype.val hab.symm
    rw [hx_eq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
      (Submodule.mem_sup_right ⟨b₁, hb₁, rfl⟩)
  have hIW_sup : I ⊔ W₁ = W := by
    apply le_antisymm (sup_le hI_le_W (Submodule.map_subtype_le _ _))
    intro x hxW
    let xw : W := ⟨x, hxW⟩
    have hcod := hW₁'.codisjoint.eq_top
    have hmem : xw ∈ (I.comap W.subtype) ⊔ W₁' := hcod.symm ▸ Submodule.mem_top
    rw [Submodule.mem_sup] at hmem
    obtain ⟨a, ha, b₁, hb₁, hab⟩ := hmem
    have hx_eq : x = (a : V) + (b₁ : V) := congrArg Subtype.val hab.symm
    rw [hx_eq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
      (Submodule.mem_sup_right ⟨b₁, hb₁, rfl⟩)
  have hW₁_le_W : W₁ ≤ W := Submodule.map_subtype_le _ _
  have hUW₁_disj : Disjoint U W₁ := by
    rw [disjoint_iff_inf_le]
    intro x ⟨hxU, hxW₁⟩
    have hxI : x ∈ I := ⟨hxU, hW₁_le_W hxW₁⟩
    exact hIW_disj.le_bot ⟨hxI, hxW₁⟩
  have hUW₁_sup : U ⊔ W₁ = ⊤ := by
    have h1 : W ≤ I ⊔ W₁ := hIW_sup.ge
    have h2 : U ⊔ W ≤ U ⊔ (I ⊔ W₁) := sup_le_sup_left h1 U
    have h3 : U ⊔ (I ⊔ W₁) = (U ⊔ I) ⊔ W₁ := (sup_assoc _ _ _).symm
    have h4 : U ⊔ I = U := sup_of_le_left hI_le_U
    rw [hsup, h3, h4, top_le_iff] at h2
    exact h2
  let k := Module.finrank K I
  let p := Module.finrank K U₁
  let q := Module.finrank K W₁
  let bI : Module.Basis (Fin k) K I := Module.finBasis K I
  let bU₁ : Module.Basis (Fin p) K U₁ := Module.finBasis K U₁
  let bW₁ : Module.Basis (Fin q) K W₁ := Module.finBasis K W₁
  let c : Fin k → V := fun i => (bI i : V)
  let a₁ : Fin p → V := fun i => (bU₁ i : V)
  let b₁ : Fin q → V := fun i => (bW₁ i : V)
  have hc_li : LinearIndependent K c := bI.linearIndependent.map' I.subtype (Submodule.ker_subtype I)
  have ha₁_li : LinearIndependent K a₁ :=
    bU₁.linearIndependent.map' U₁.subtype (Submodule.ker_subtype U₁)
  have hb₁_li : LinearIndependent K b₁ :=
    bW₁.linearIndependent.map' W₁.subtype (Submodule.ker_subtype W₁)
  have hspan_c : Submodule.span K (Set.range c) = I := by
    have hrng : Set.range c = I.subtype '' Set.range bI := Set.range_comp I.subtype bI
    rw [hrng, ← Submodule.map_span, bI.span_eq, Submodule.map_subtype_top]
  have hspan_a₁ : Submodule.span K (Set.range a₁) = U₁ := by
    have hrng : Set.range a₁ = U₁.subtype '' Set.range bU₁ := Set.range_comp U₁.subtype bU₁
    rw [hrng, ← Submodule.map_span, bU₁.span_eq, Submodule.map_subtype_top]
  have hspan_b₁ : Submodule.span K (Set.range b₁) = W₁ := by
    have hrng : Set.range b₁ = W₁.subtype '' Set.range bW₁ := Set.range_comp W₁.subtype bW₁
    rw [hrng, ← Submodule.map_span, bW₁.span_eq, Submodule.map_subtype_top]
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
  have hkp : k + p = r := by
    have hU1 := finrank_span_eq_card hca_li
    have hU2 := finrank_span_eq_card hv
    rw [hspan_ca] at hU1
    change Module.finrank K U = _ at hU2
    rw [hU1, Fintype.card_fin] at hU2
    simpa [Fintype.card_fin] using hU2
  have hkq : k + q = s := by
    have hW1 := finrank_span_eq_card hcb_li
    have hW2 := finrank_span_eq_card hw
    rw [hspan_cb] at hW1
    change Module.finrank K W = _ at hW2
    rw [hW1, Fintype.card_fin] at hW2
    simpa [Fintype.card_fin] using hW2
  have hkpq : k + p + q = n := by
    have hV1 := finrank_span_eq_card hcab_li
    have hV2 : Module.finrank K V = n := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    rw [hspan_cab, finrank_top, Fintype.card_fin] at hV1
    omega
  let ca' : Fin r → V := (Fin.append c a₁) ∘ (finCongr hkp).symm
  let cb' : Fin s → V := (Fin.append c b₁) ∘ (finCongr hkq).symm
  have hca'_li : LinearIndependent K ca' := hca_li.comp _ (finCongr hkp).symm.injective
  have hcb'_li : LinearIndependent K cb' := hcb_li.comp _ (finCongr hkq).symm.injective
  have hspan_ca' : Submodule.span K (Set.range ca') = U := by
    have hrng : Set.range ca' = Set.range (Fin.append c a₁) := by
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    rw [hrng, hspan_ca]
  have hspan_cb' : Submodule.span K (Set.range cb') = W := by
    have hrng : Set.range cb' = Set.range (Fin.append c b₁) := by
      rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    rw [hrng, hspan_cb]
  obtain ⟨cU, hcU⟩ := (plucker_span_eq_iff_proportional v ca' hv hca'_li).mp hspan_ca'.symm
  obtain ⟨cW, hcW⟩ := (plucker_span_eq_iff_proportional w cb' hw hcb'_li).mp hspan_cb'.symm
  let C := ExteriorAlgebra.ιMulti K k c
  let A₁ := ExteriorAlgebra.ιMulti K p a₁
  let B₁ := ExteriorAlgebra.ιMulti K q b₁
  have hιv : ExteriorAlgebra.ιMulti K r v = (cU : K) • (C * A₁) := by
    rw [hcU, ← ιMulti_fin_append_congr hkp c a₁]
  have hιw : ExteriorAlgebra.ιMulti K s w = (cW : K) • (C * B₁) := by
    rw [hcW, ← ιMulti_fin_append_congr hkq c b₁]
  have hA₁_mem : A₁ ∈ ⋀[K]^p V := ExteriorAlgebra.ιMulti_range K p ⟨a₁, rfl⟩
  have hB₁_mem : B₁ ∈ ⋀[K]^q V := ExteriorAlgebra.ιMulti_range K q ⟨b₁, rfl⟩
  have hreg :
      regressive b (ExteriorAlgebra.ιMulti K r v) (ExteriorAlgebra.ιMulti K s w) =
        ((cU : K) * (cW : K) * volCoord b (C * A₁ * B₁)) • C := by
    rw [hιv, hιw, smul_regressive, regressive_smul,
      grassmann_no103_blade b hkpq c hA₁_mem hB₁_mem, smul_smul, smul_smul, mul_assoc]
  have htop_prod : C * A₁ * B₁ =
      ExteriorAlgebra.ιMulti K (k + p + q) (Fin.append (Fin.append c a₁) b₁) := by
    dsimp [C, A₁, B₁]
    rw [ExteriorAlgebra.ιMulti_mul_ιMulti, ExteriorAlgebra.ιMulti_mul_ιMulti]
  have htop_ne : C * A₁ * B₁ ≠ 0 := by
    rw [htop_prod]
    exact ιMulti_ne_zero_of_linearIndependent _ hcab_li
  have htop_mem : C * A₁ * B₁ ∈ ⋀[K]^n V := by
    have hmem : C * A₁ * B₁ ∈ ⋀[K]^(k + p + q) V := by
      rw [htop_prod]
      exact ExteriorAlgebra.ιMulti_range K _ ⟨_, rfl⟩
    simpa [hkpq] using hmem
  have hvol_ne : volCoord b (C * A₁ * B₁) ≠ 0 := by
    intro h0
    apply htop_ne
    have hsm := eq_volCoord_smul_volume b htop_mem
    rwa [h0, zero_smul] at hsm
  have hcoef_ne : (cU : K) * (cW : K) * volCoord b (C * A₁ * B₁) ≠ 0 :=
    mul_ne_zero (mul_ne_zero cU.ne_zero cW.ne_zero) hvol_ne
  refine ⟨?_, ?_⟩
  · rw [hreg]
    exact smul_ne_zero hcoef_ne (ιMulti_ne_zero_of_linearIndependent c hc_li)
  · rw [hreg, bladeSupport_smul C hcoef_ne]
    exact (bladeSupport_ιMulti c hc_li).trans hspan_c

end RegressiveSubspaceMeet

/-! ## 3. Grassmann's Exterior Cramer's Rule (`No. 134`, Editorial Note 45, Seligman `p. 395`) -/

section ExteriorCramerRuleNo134

/-- **Grassmann No. 134 (Exterior Cramer Identity)** over ANY commutative ring `R`:
replacing the `i`-th column of an `n`-blade `a` by `∑ j, x j • a j` yields
`x i • ιMulti R n a`. -/
theorem exterior_cramer_ιMulti {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} (a : Fin n → M) (x : Fin n → R) (i : Fin n) :
    ExteriorAlgebra.ιMulti R n (Function.update a i (∑ j : Fin n, x j • a j)) =
      x i • ExteriorAlgebra.ιMulti R n a := by
  rw [(ExteriorAlgebra.ιMulti R n).map_update_sum Finset.univ i (fun j => x j • a j) a]
  rw [Finset.sum_eq_single i]
  · rw [AlternatingMap.map_update_smul, Function.update_eq_self]
  · intro j _ hj
    rw [AlternatingMap.map_update_smul]
    have hzero : ExteriorAlgebra.ιMulti R n (Function.update a i (a j)) = 0 := by
      refine (ExteriorAlgebra.ιMulti R n).map_eq_zero_of_eq _ (i := i) (j := j) ?_ hj.symm
      simp [hj]
    rw [hzero, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Field scalar quotient form of **Grassmann No. 134**: if `a : Fin n → V` is linearly
independent, then `volCoord b (ιMulti K n a) ≠ 0` and
`x i = volCoord b (ιMulti K n (Function.update a i (∑ j, x j • a j))) / volCoord b (ιMulti K n a)`. -/
theorem exterior_cramer_volCoord {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (a : Fin n → V) (ha : LinearIndependent K a)
    (x : Fin n → K) (i : Fin n) :
    volCoord b (ExteriorAlgebra.ιMulti K n a) ≠ 0 ∧
      x i =
        volCoord b (ExteriorAlgebra.ιMulti K n (Function.update a i (∑ j : Fin n, x j • a j))) /
          volCoord b (ExteriorAlgebra.ιMulti K n a) := by
  have ha_ne : ExteriorAlgebra.ιMulti K n a ≠ 0 := ιMulti_ne_zero_of_linearIndependent a ha
  have ha_mem : ExteriorAlgebra.ιMulti K n a ∈ ⋀[K]^n V := ExteriorAlgebra.ιMulti_range K n ⟨a, rfl⟩
  have hvol_ne : volCoord b (ExteriorAlgebra.ιMulti K n a) ≠ 0 := by
    intro h0
    apply ha_ne
    have hsm := eq_volCoord_smul_volume b ha_mem
    rwa [h0, zero_smul] at hsm
  refine ⟨hvol_ne, ?_⟩
  rw [exterior_cramer_ιMulti a x i, LinearMap.map_smul, smul_eq_mul,
    mul_div_cancel_right₀ _ hvol_ne]

end ExteriorCramerRuleNo134

/-! ## 4. Lorentzian Circle Space, E. Müller Supplement & Note 97 Syncyclic Countermodel -/

section CircleSpaceNotes95_97

/-- Homogeneous coordinates `[1, a, b, a² + b² - r²] ∈ ℝ⁴` representing the circle with center
`(a, b)` and radius `r` (`Grassmann Nos. 396–409`). -/
def circleVec (a b r : ℝ) : Fin 4 → ℝ :=
  ![1, a, b, a ^ 2 + b ^ 2 - r ^ 2]

/-- Point `(x, y)` embedded as a zero-radius null circle `[1, x, y, x² + y²]`. -/
def pointCircleVec (x y : ℝ) : Fin 4 → ℝ :=
  circleVec x y 0

/-- Signature-`(1, 3)` Lorentzian bilinear form on `ℝ⁴` realizing Grassmann's double-distance
product on circles (`circleBilin u v = u₀ v₃ + u₃ v₀ - 2 u₁ v₁ - 2 u₂ v₂`). -/
def circleBilin : LinearMap.BilinForm ℝ (Fin 4 → ℝ) :=
  LinearMap.mk₂ ℝ (fun u v => u 0 * v 3 + u 3 * v 0 - 2 * u 1 * v 1 - 2 * u 2 * v 2)
    (fun u₁ u₂ v => by simp only [Pi.add_apply, mul_add, add_mul]; abel)
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_add, mul_sub, mul_assoc]
      rw [mul_left_comm 2 c, mul_left_comm 2 c])
    (fun u v₁ v₂ => by simp only [Pi.add_apply, mul_add]; abel)
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_add, mul_sub, mul_assoc]
      rw [mul_left_comm (u 0) c, mul_left_comm (u 3) c,
        mul_left_comm (u 1) c, mul_left_comm 2 c,
        mul_left_comm (u 2) c, mul_left_comm 2 c])

theorem circleBilin_apply (u v : Fin 4 → ℝ) :
    circleBilin u v = u 0 * v 3 + u 3 * v 0 - 2 * u 1 * v 1 - 2 * u 2 * v 2 :=
  rfl

/-- **Grassmann No. 396**: the circle bilinear form evaluates to point double distance
`(x - a)² + (y - b)² - r²`, norm `-2 r²`, and radical/tangency pairing
`(a₁ - a₂)² + (b₁ - b₂)² - r₁² - r₂²`. -/
theorem grassmann_no396_double_distance (x y a b r a₁ b₁ r₁ a₂ b₂ r₂ : ℝ) :
    circleBilin (pointCircleVec x y) (circleVec a b r) = (x - a) ^ 2 + (y - b) ^ 2 - r ^ 2 ∧
      circleBilin (circleVec a b r) (circleVec a b r) = -2 * r ^ 2 ∧
      circleBilin (circleVec a₁ b₁ r₁) (circleVec a₂ b₂ r₂) =
        (a₁ - a₂) ^ 2 + (b₁ - b₂) ^ 2 - r₁ ^ 2 - r₂ ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [circleBilin_apply, pointCircleVec, circleVec]
    ring

private def circleDiagEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun u := ![(u 0 + u 3) / 2, u 1, u 2, (u 0 - u 3) / 2]
  invFun w := ![w 0 + w 3, w 1, w 2, w 0 - w 3]
  map_add' u v := by
    ext i
    fin_cases i <;> (simp; try ring)
  map_smul' c u := by
    ext i
    fin_cases i <;> (simp; try ring)
  left_inv u := by
    ext i
    fin_cases i <;> (simp; try ring)
  right_inv w := by
    ext i
    fin_cases i <;> (simp; try ring)

private theorem vec4_two {α : Type*} (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
private theorem vec4_three {α : Type*} (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl

/-- Sylvester inertia signature `(1, 3)` of the circle space Lorentzian quadratic form. -/
theorem circleBilin_signature :
    sigPos circleBilin.toQuadraticMap = 1 ∧ sigNeg circleBilin.toQuadraticMap = 3 := by
  let w : Fin 4 → ℝ := (![2, -2, -2, -2] : Fin 4 → ℝ)
  let Qw := QuadraticMap.weightedSumSquares ℝ w
  let e : Qw.IsometryEquiv circleBilin.toQuadraticMap :=
    { toLinearEquiv := circleDiagEquiv.symm
      map_app' := fun m => by
        change circleBilin (circleDiagEquiv.symm m) (circleDiagEquiv.symm m) = Qw m
        dsimp [Qw]
        rw [QuadraticMap.weightedSumSquares_apply, circleBilin_apply]
        simp only [circleDiagEquiv, LinearEquiv.coe_symm_mk, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one, vec4_two, vec4_three, smul_eq_mul, w]
        ring }
  have heq : circleBilin.toQuadraticMap.Equivalent Qw := ⟨e.symm⟩
  have hsp : sigPos Qw = {i : Fin 4 | (0 : ℝ) < w i}.ncard :=
    QuadraticForm.sigPos_weightedSumSquares
  have hsn : sigNeg Qw = {i : Fin 4 | w i < 0}.ncard :=
    QuadraticForm.sigNeg_weightedSumSquares
  have hset_pos : ({i : Fin 4 | (0 : ℝ) < w i} : Set (Fin 4)) = {0} := by
    ext i
    fin_cases i <;> simp [w]
  have hset_neg : ({i : Fin 4 | w i < 0} : Set (Fin 4)) = {1, 2, 3} := by
    ext i
    fin_cases i <;> simp [w]
  have hcard_neg : ({1, 2, 3} : Set (Fin 4)).ncard = 3 := by
    have hfin : ({1, 2, 3} : Set (Fin 4)) = (({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4)) := by
      simp
    rw [hfin, Set.ncard_coe_finset]
    decide
  refine ⟨?_, ?_⟩
  · rw [heq.sigPos_eq, hsp, hset_pos, Set.ncard_singleton]
  · rw [heq.sigNeg_eq, hsn, hset_neg, hcard_neg]

/-- **E. Müller's Supplement (`Editorial Note 95, p. 369`)**: for three circles `C₁, C₂, C₃ ∈ ℝ⁴`,
construct the unique vector orthogonal to all three representing the orthogonal circle. -/
def circleSupplement (C₁ C₂ C₃ : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let b := Pi.basisFun ℝ (Fin 4)
  let ℓ : Fin 4 → ℝ := fun i =>
    volCoord b (ExteriorAlgebra.ι ℝ (b i) * ExteriorAlgebra.ι ℝ C₁ *
      ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₃)
  ![ℓ 3, -(ℓ 1 / 2), -(ℓ 2 / 2), ℓ 0]

/-- **Editorial Note 95 (`p. 369`)**: E. Müller's orthogonal circle functional matches
`volCoord (ι u * ι C₁ * ι C₂ * ι C₃)` identically, annihilates `C₁, C₂, C₃`, and is nonzero
iff `C₁, C₂, C₃` are linearly independent. -/
theorem mueller_note95_orthogonal_supplement (C₁ C₂ C₃ : Fin 4 → ℝ) :
    (∀ u : Fin 4 → ℝ,
      circleBilin u (circleSupplement C₁ C₂ C₃) =
        volCoord (Pi.basisFun ℝ (Fin 4))
          (ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ C₁ *
            ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₃)) ∧
      circleBilin C₁ (circleSupplement C₁ C₂ C₃) = 0 ∧
      circleBilin C₂ (circleSupplement C₁ C₂ C₃) = 0 ∧
      circleBilin C₃ (circleSupplement C₁ C₂ C₃) = 0 ∧
      (circleSupplement C₁ C₂ C₃ ≠ 0 ↔ LinearIndependent ℝ ![C₁, C₂, C₃]) := by
  let b := Pi.basisFun ℝ (Fin 4)
  have heval : ∀ u : Fin 4 → ℝ,
      circleBilin u (circleSupplement C₁ C₂ C₃) =
        volCoord b (ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ C₁ *
          ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₃) := fun u => by
    have hu : u = u 0 • b 0 + u 1 • b 1 + u 2 • b 2 + u 3 • b 3 := by
      ext i
      fin_cases i <;> simp [b]
    rw [circleBilin_apply]
    dsimp [circleSupplement, b]
    conv_rhs => rw [hu]; dsimp [b]
    simp only [map_add, map_smul, add_mul, smul_mul_assoc, smul_eq_mul]
    ring
  have hC₁ : circleBilin C₁ (circleSupplement C₁ C₂ C₃) = 0 := by
    rw [heval C₁, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul, LinearMap.map_zero]
  have hC₂ : circleBilin C₂ (circleSupplement C₁ C₂ C₃) = 0 := by
    rw [heval C₂]
    have hsw : ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₁ =
        -(ExteriorAlgebra.ι ℝ C₁ * ExteriorAlgebra.ι ℝ C₂) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    rw [hsw, neg_mul, neg_mul, mul_assoc (ExteriorAlgebra.ι ℝ C₁), ExteriorAlgebra.ι_sq_zero,
      mul_zero, zero_mul, neg_zero, LinearMap.map_zero]
  have hC₃ : circleBilin C₃ (circleSupplement C₁ C₂ C₃) = 0 := by
    rw [heval C₃]
    have h31 : ExteriorAlgebra.ι ℝ C₃ * ExteriorAlgebra.ι ℝ C₁ =
        -(ExteriorAlgebra.ι ℝ C₁ * ExteriorAlgebra.ι ℝ C₃) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have h32 : ExteriorAlgebra.ι ℝ C₃ * ExteriorAlgebra.ι ℝ C₂ =
        -(ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₃) :=
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have h3123 : ExteriorAlgebra.ι ℝ C₃ * ExteriorAlgebra.ι ℝ C₁ *
        ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₃ = 0 := by
      calc
        ExteriorAlgebra.ι ℝ C₃ * ExteriorAlgebra.ι ℝ C₁ *
            ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₃
            = -((ExteriorAlgebra.ι ℝ C₁ * (ExteriorAlgebra.ι ℝ C₃ * ExteriorAlgebra.ι ℝ C₂)) *
                ExteriorAlgebra.ι ℝ C₃) := by
              rw [h31, neg_mul, neg_mul, mul_assoc (ExteriorAlgebra.ι ℝ C₁)]
        _ = (ExteriorAlgebra.ι ℝ C₁ * ExteriorAlgebra.ι ℝ C₂) *
              (ExteriorAlgebra.ι ℝ C₃ * ExteriorAlgebra.ι ℝ C₃) := by
              rw [h32, mul_neg, neg_mul, neg_neg]
              simp only [mul_assoc]
        _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero, mul_zero]
    rw [h3123, LinearMap.map_zero]
  refine ⟨heval, hC₁, hC₂, hC₃, ?_⟩
  let ω := ExteriorAlgebra.ι ℝ C₁ * ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₃
  have hω_eq : ω = ExteriorAlgebra.ιMulti ℝ 3 ![C₁, C₂, C₃] := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    simp [ω, Matrix.vecTail, mul_assoc]
  constructor
  · intro hne
    contrapose! hne
    have hω0 : ω = 0 := by
      rw [hω_eq, ιMulti_eq_zero_iff]
      exact hne
    have hω_prod :
        ExteriorAlgebra.ι ℝ C₁ * (ExteriorAlgebra.ι ℝ C₂ * ExteriorAlgebra.ι ℝ C₃) = 0 := by
      simpa [ω, mul_assoc] using hω0
    ext i
    fin_cases i <;> simp [circleSupplement, mul_assoc, hω_prod]
  · intro hli
    have hω_ne : ω ≠ 0 := by
      rw [hω_eq]
      exact ιMulti_ne_zero_of_linearIndependent ![C₁, C₂, C₃] hli
    have hsupp_ne : bladeSupport ω ≠ ⊤ := by
      intro htop
      have hspan : bladeSupport ω = Submodule.span ℝ (Set.range ![C₁, C₂, C₃]) := by
        rw [hω_eq]
        exact bladeSupport_ιMulti ![C₁, C₂, C₃] hli
      rw [hspan] at htop
      have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range ![C₁, C₂, C₃])) = 3 := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
      rw [htop, finrank_top] at h1
      have h2 : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
      omega
    have hex : ∃ j : Fin 4, ExteriorAlgebra.ι ℝ (b j) * ω ≠ 0 := by
      by_contra h
      push Not at h
      apply hsupp_ne
      rw [eq_top_iff]
      intro u _
      have hmem : ∀ j : Fin 4, b j ∈ bladeSupport ω := fun j => (mem_bladeSupport ω (b j)).mpr (h j)
      have hspan_top : Submodule.span ℝ (Set.range b) = ⊤ := b.span_eq
      have hu_span : u ∈ Submodule.span ℝ (Set.range b) := hspan_top ▸ Submodule.mem_top
      refine (Submodule.span_le.mpr ?_) hu_span
      rintro _ ⟨j, rfl⟩
      exact hmem j
    obtain ⟨j, hj⟩ := hex
    have hmem4 : ExteriorAlgebra.ι ℝ (b j) * ω ∈ ⋀[ℝ]^4 (Fin 4 → ℝ) := by
      rw [hω_eq, ExteriorAlgebra.exteriorPower, pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _)
        (by
          rw [← ExteriorAlgebra.exteriorPower]
          exact ExteriorAlgebra.ιMulti_range ℝ 3 ⟨![C₁, C₂, C₃], rfl⟩)
    have hvol_ne : volCoord b (ExteriorAlgebra.ι ℝ (b j) * ω) ≠ 0 := by
      intro h0
      apply hj
      have hsm := eq_volCoord_smul_volume b hmem4
      rwa [h0, zero_smul] at hsm
    intro hsupp0
    have hz : circleBilin (b j) (circleSupplement C₁ C₂ C₃) = 0 := by
      rw [hsupp0]
      simp
    rw [heval (b j)] at hz
    exact hvol_ne (by simpa [ω, mul_assoc] using hz)

/-- Four circles in `ℝ⁴` are syncyclic (share a common orthogonal / lie in a 3D subspace)
precisely when their 4-fold exterior product vanishes (`No. 406, Note 97`). -/
def IsSyncyclic4 (C₁ C₂ C₃ C₄ : Fin 4 → ℝ) : Prop :=
  ExteriorAlgebra.ιMulti ℝ 4 ![C₁, C₂, C₃, C₄] = 0

/-- Two circles `u, v ∈ ℝ⁴` are tangent precisely when `(circleBilin u v)² = circleBilin u u * circleBilin v v`. -/
def IsCircleTangent (u v : Fin 4 → ℝ) : Prop :=
  (circleBilin u v) ^ 2 = circleBilin u u * circleBilin v v

private noncomputable def syncyclicShiftEquiv : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) where
  toFun u := ![u 0, u 1, u 2, u 3 - 3 * u 0]
  invFun w := ![w 0, w 1, w 2, w 3 + 3 * w 0]
  map_add' u v := by ext i; fin_cases i <;> (simp; try ring)
  map_smul' c u := by ext i; fin_cases i <;> (simp; try ring)
  left_inv u := by ext i; fin_cases i <;> (simp; try ring)
  right_inv w := by ext i; fin_cases i <;> (simp; try ring)

/-- **Editorial Note 97 (`pp. 369–370`) — `[countermodel_found]` for Syncyclic Tangency**:
1. Every `GL(4, ℝ)` linear automorphism preserves `IsSyncyclic4`.
2. Every `O(circleBilin)` orthogonal transformation preserves `IsCircleTangent`.
3. However, `syncyclicShiftEquiv ∈ GL(4, ℝ)` sends two tangent circles `(0,0; r=1)` and `(2,0; r=1)`
   to non-tangent circles `(0,0; r=2)` and `(2,0; r=2)`. -/
theorem note97_syncyclic_vs_moebius_tangency :
    (∀ (T : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (C₁ C₂ C₃ C₄ : Fin 4 → ℝ),
      IsSyncyclic4 (T C₁) (T C₂) (T C₃) (T C₄) ↔ IsSyncyclic4 C₁ C₂ C₃ C₄) ∧
      (∀ (T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)),
        (∀ u v, circleBilin (T u) (T v) = circleBilin u v) →
          ∀ u v, IsCircleTangent u v → IsCircleTangent (T u) (T v)) ∧
      (∃ (T : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (u v : Fin 4 → ℝ),
        IsCircleTangent u v ∧ ¬ IsCircleTangent (T u) (T v)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T C₁ C₂ C₃ C₄
    simp only [IsSyncyclic4, ιMulti_eq_zero_iff]
    have hcomp : ![T C₁, T C₂, T C₃, T C₄] = (T : (Fin 4 → ℝ) → (Fin 4 → ℝ)) ∘ ![C₁, C₂, C₃, C₄] := by
      ext i j
      fin_cases i <;> rfl
    rw [hcomp]
    exact not_congr ((T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)).linearIndependent_iff T.ker)
  · intro T hT u v huv
    dsimp [IsCircleTangent] at huv ⊢
    rw [hT, hT, hT, huv]
  · refine ⟨syncyclicShiftEquiv, circleVec 0 0 1, circleVec 2 0 1, ?_, ?_⟩
    · simp [IsCircleTangent, (grassmann_no396_double_distance 0 0 0 0 1 0 0 1 2 0 1).2.1,
        (grassmann_no396_double_distance 0 0 2 0 1 0 0 1 2 0 1).2.1,
        (grassmann_no396_double_distance 0 0 0 0 1 0 0 1 2 0 1).2.2]
      norm_num
    · have hu : syncyclicShiftEquiv (circleVec 0 0 1) = circleVec 0 0 2 := by
        ext i; fin_cases i <;> (simp [syncyclicShiftEquiv, circleVec]; try norm_num)
      have hv : syncyclicShiftEquiv (circleVec 2 0 1) = circleVec 2 0 2 := by
        ext i; fin_cases i <;> (simp [syncyclicShiftEquiv, circleVec]; try norm_num)
      rw [hu, hv]
      simp [IsCircleTangent, (grassmann_no396_double_distance 0 0 0 0 2 0 0 2 2 0 2).2.1,
        (grassmann_no396_double_distance 0 0 2 0 2 0 0 2 2 0 2).2.1,
        (grassmann_no396_double_distance 0 0 0 0 2 0 0 2 2 0 2).2.2]
      norm_num

end CircleSpaceNotes95_97

end InfoGeometry.Projective.GrassmannPluckerMeetAndCircleSpace
