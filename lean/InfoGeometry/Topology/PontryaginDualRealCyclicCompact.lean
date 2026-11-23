/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Portions adapted from `external_refs/riemann-masullo`
(`RiemannMasullo/ForMathlib/Topology/Algebra/PontryaginDual/{Real,Cyclic,Compact}.lean`,
Apache-2.0, revision `be5d4cb0356d48406eae83233d73c99085b9a038`).
-/
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Order.Compact

/-!
# Pontryagin Duality for `ℝ`, `ℤ × U`, and Compact Polar Sets

Ports `exists_realPontryaginDualEquiv`, `exists_cyclicProductCharacterHomeomorph`,
and `exists_isCompact_pontryaginDual_polar` from `RiemannMasullo` against the
pinned Mathlib `v4.34.1` toolchain.
-/

public section

noncomputable section

open Filter Function Set
open scoped Topology

namespace InfoGeometry.Topology.PontryaginDualRealCyclicCompact

/-- The real line is isomorphic to its Pontryagin dual by the pairing
`(x, y) ↦ exp(2πixy)`. -/
theorem exists_realPontryaginDualEquiv :
    ∃ e : Multiplicative ℝ ≃ₜ* PontryaginDual (Multiplicative ℝ),
      ∀ x y : ℝ, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        Circle.exp (2 * Real.pi * (x * y)) := by
  let G := Multiplicative ℝ
  let a : ℝ := 2 * Real.pi
  have ha : a ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  let pairing : G →* PontryaginDual G :=
    { toFun := fun x ↦
        { toFun := fun y ↦ Circle.exp (a * (x.toAdd * y.toAdd))
          map_one' := by change Circle.exp (a * (x.toAdd * 0)) = 1; simp
          map_mul' := fun y z ↦ by
            change Circle.exp (a * (x.toAdd * (y.toAdd + z.toAdd))) =
              Circle.exp (a * (x.toAdd * y.toAdd)) * Circle.exp (a * (x.toAdd * z.toAdd))
            rw [mul_add, mul_add, Circle.exp_add]
          continuous_toFun := Circle.exp.continuous.comp
            (continuous_const.mul (continuous_const.mul continuous_id)) }
      map_one' := PontryaginDual.ext fun y ↦ by
        change Circle.exp (a * (0 * y.toAdd)) = 1
        simp
      map_mul' := fun x y ↦ PontryaginDual.ext fun z ↦ by
        change Circle.exp (a * ((x.toAdd + y.toAdd) * z.toAdd)) =
          Circle.exp (a * (x.toAdd * z.toAdd)) * Circle.exp (a * (y.toAdd * z.toAdd))
        rw [add_mul, mul_add, Circle.exp_add] }
  have hcont : Continuous pairing := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
      (show G → (G →ₜ* Circle) from pairing)
    exact Circle.exp.continuous.comp (continuous_const.mul (continuous_fst.mul continuous_snd))
  have hinj : Injective pairing := by
    intro x y hxy
    have hphase : (fun t : ℝ ↦ a * (x.toAdd * t)) = fun t : ℝ ↦ a * (y.toAdd * t) :=
      Circle.isCoveringMap_exp.eq_of_comp_eq (by fun_prop) (by fun_prop)
        (funext fun t ↦ congrArg (fun χ : PontryaginDual G ↦ χ (Multiplicative.ofAdd t)) hxy)
        0 (by simp)
    change x.toAdd = y.toAdd
    exact mul_left_cancel₀ ha (by simpa only [mul_one] using congrFun hphase 1)
  have hsurj : Surjective pairing := by
    intro χ
    let c : C(ℝ, Circle) := ⟨fun t ↦ χ (Multiplicative.ofAdd t), χ.continuous⟩
    obtain ⟨L, ⟨hL0, hL⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      c 0 0 (Circle.exp_zero.trans (map_one χ).symm)
    have hl (t : ℝ) : Circle.exp (L t) = χ (Multiplicative.ofAdd t) := congrFun hL t
    have hAgree : Circle.exp ∘ (fun p : ℝ × ℝ ↦ L (p.1 + p.2)) =
        Circle.exp ∘ (fun p : ℝ × ℝ ↦ L p.1 + L p.2) := by
      funext p
      simp only [comp_apply, hl, Circle.exp_add, ← map_mul]
      rfl
    have hadd : (fun p : ℝ × ℝ ↦ L (p.1 + p.2)) = fun p : ℝ × ℝ ↦ L p.1 + L p.2 :=
      Circle.isCoveringMap_exp.eq_of_comp_eq
        (L.continuous.comp (continuous_fst.add continuous_snd))
        ((L.continuous.comp continuous_fst).add (L.continuous.comp continuous_snd))
        hAgree (0, 0) (by change L (0 + 0) = L 0 + L 0; simp [hL0])
    let Ladd : ℝ →+ ℝ :=
      { toFun := L
        map_zero' := hL0
        map_add' := fun x y ↦ congrFun hadd (x, y) }
    let Llin := Ladd.toRealLinearMap L.continuous
    have hlin (t : ℝ) : L t = t * L 1 := by
      change Llin t = t * Llin 1
      simpa only [smul_eq_mul, mul_one] using Llin.map_smul t (1 : ℝ)
    refine ⟨Multiplicative.ofAdd (L 1 / a), PontryaginDual.ext fun t ↦ ?_⟩
    change Circle.exp (a * ((L 1 / a) * t.toAdd)) = χ t
    calc
      _ = Circle.exp (L t.toAdd) := by
        apply congrArg Circle.exp
        rw [hlin t.toAdd]
        calc
          _ = t.toAdd * (L 1 / a * a) := by ring
          _ = _ := by rw [div_mul_cancel₀ _ ha]
      _ = χ t := hl t.toAdd
  let equiv := MulEquiv.ofBijective pairing ⟨hinj, hsurj⟩
  let e : G ≃ₜ* PontryaginDual G :=
    { equiv with
      continuous_toFun := hcont
      continuous_invFun := (Equiv.continuous_symm_iff equiv.toEquiv).mpr
        (pairing.isOpenMap_of_sigmaCompact hsurj hcont) }
  exact ⟨e, fun _ _ ↦ rfl⟩

/-- A complex character of an infinite cyclic group times a compact group is determined
by its value on the generator and its unitary restriction. -/
theorem exists_cyclicProductCharacterHomeomorph {U : Type*} [CommGroup U] [TopologicalSpace U]
    [IsTopologicalGroup U] [CompactSpace U] [T2Space U] :
    ∃ e : (Multiplicative ℤ × U →ₜ* ℂ) ≃ₜ ℂˣ × PontryaginDual U, ∀ c,
      ((e c).1 : ℂ) = c (Multiplicative.ofAdd 1, 1) ∧ ∀ u, ((e c).2 u : ℂ) = c (1, u) := by
  let gen : Multiplicative ℤ × U := (Multiplicative.ofAdd 1, 1)
  let i : U →ₜ* (Multiplicative ℤ × U) :=
    { toFun := fun u ↦ (1, u)
      map_one' := rfl
      map_mul' := fun x y ↦ Prod.ext (mul_one _).symm rfl
      continuous_toFun := continuous_const.prodMk continuous_id }
  have hcircle (c : Multiplicative ℤ × U →ₜ* ℂ) (u : U) :
      c (i u) ∈ Submonoid.unitSphere ℂ := by
    let a := c.comp i
    obtain ⟨B, hB⟩ := (isCompact_range a.continuous.norm).bddAbove
    have hle (v : U) : ‖a v‖ ≤ 1 := by
      by_contra! h
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
      have hb := hB (Set.mem_range_self (v ^ n))
      change ‖a (v ^ n)‖ ≤ B at hb
      rw [map_pow, norm_pow] at hb
      exact hn.not_ge hb
    apply mem_sphere_zero_iff_norm.mpr
    refine (hle u).antisymm ?_
    have h := hle u⁻¹
    rw [map_inv, norm_inv] at h
    exact (inv_le_one₀ (norm_pos_iff.mpr ((Group.isUnit _).map a).ne_zero)).mp h
  let value (c : Multiplicative ℤ × U →ₜ* ℂ) : ℂˣ :=
    Units.mk0 (c gen) ((Group.isUnit gen).map c).ne_zero
  let restrict (c : Multiplicative ℤ × U →ₜ* ℂ) : PontryaginDual U :=
    { toFun := fun u ↦ ⟨c (i u), hcircle c u⟩
      map_one' := Circle.ext (map_one (c.comp i))
      map_mul' := fun u v ↦ Circle.ext (map_mul (c.comp i) u v)
      continuous_toFun := (c.continuous.comp i.continuous).subtype_mk (hcircle c) }
  have hpowers : Continuous (fun p : ℂˣ × Multiplicative ℤ ↦ (p.1 ^ p.2.toAdd : ℂˣ)) :=
    continuous_prod_of_discrete_right.mpr fun n ↦ continuous_zpow n.toAdd
  let extend (p : ℂˣ × PontryaginDual U) : Multiplicative ℤ × U →ₜ* ℂ :=
    { toFun := fun x ↦ ((p.1 ^ x.1.toAdd : ℂˣ) : ℂ) * (p.2 x.2 : ℂ)
      map_one' := by
        change ↑(p.1 ^ (0 : ℤ)) * (p.2 1 : ℂ) = 1
        simp
      map_mul' := fun x y ↦ by
        change ↑(p.1 ^ (x.1.toAdd + y.1.toAdd)) * (p.2 (x.2 * y.2) : ℂ) = _
        simp only [zpow_add, Units.val_mul, map_mul, Circle.coe_mul]
        ring
      continuous_toFun := (Units.continuous_val.comp (hpowers.comp
        (continuous_const.prodMk continuous_fst))).mul
        (continuous_subtype_val.comp (p.2.continuous.comp continuous_snd)) }
  refine ⟨{
    toFun := fun c ↦ (value c, restrict c)
    invFun := extend
    left_inv := fun c ↦ by
      ext1 x
      have hgen : gen ^ x.1.toAdd * i x.2 = x := by
        apply Prod.ext
        · change x.1.toAdd • (1 : ℤ) + 0 = x.1.toAdd
          simp
        · change (1 : U) ^ x.1.toAdd * x.2 = x.2
          simp
      change ↑(value c ^ x.1.toAdd) * c (i x.2) = c x
      rw [Units.val_zpow_eq_zpow_val]
      change (c gen) ^ x.1.toAdd * c (i x.2) = c x
      rw [← map_zpow, ← map_mul, hgen]
    right_inv := fun p ↦ Prod.ext (Units.ext (by
      change ↑(p.1 ^ (1 : ℤ)) * (p.2 1 : ℂ) = _
      simp)) (PontryaginDual.ext fun u ↦ Circle.ext (by
        change ↑(p.1 ^ (0 : ℤ)) * (p.2 u : ℂ) = _
        simp))
    continuous_toFun := (Units.isEmbedding_val₀.continuous_iff.mpr (continuous_eval_const gen)).prodMk ?_
    continuous_invFun := ContinuousMonoidHom.continuous_of_continuous_uncurry extend ?_ },
    fun c ↦ ⟨rfl, fun u ↦ rfl⟩⟩
  · apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (continuous_eval.comp (continuous_fst.prodMk (i.continuous.comp continuous_snd))).subtype_mk
      (fun p ↦ hcircle p.1 p.2)
  · have : ContinuousEval (PontryaginDual U) U Circle :=
      inferInstanceAs (ContinuousEval (U →ₜ* Circle) U Circle)
    exact (Units.continuous_val.comp (hpowers.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)))).mul (continuous_subtype_val.comp
      (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd))))

/-- There is a radius such that characters mapping any fixed identity neighborhood into
the closed circle ball of that radius form a compact set in the compact-open topology.
Powers give equicontinuity at the identity, and Arzelà–Ascoli gives compactness. -/
theorem exists_isCompact_pontryaginDual_polar {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ r : ℝ, 0 < r ∧ ∀ U ∈ 𝓝 (1 : G),
      IsCompact {χ : PontryaginDual G | MapsTo χ U (Metric.closedBall 1 r)} := by
  classical
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  obtain ⟨r, hr, hBall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hArc
  refine ⟨r, hr, fun U hU ↦ ?_⟩
  let W := Metric.closedBall (1 : Circle) r
  let S := {f : G →* Circle | MapsTo f U W}
  have hEqui : Equicontinuous (fun f : S ↦ (f.1 : G → Circle)) := by
    refine equicontinuous_of_equicontinuousAt_one Subtype.val ?_
    apply (Metric.equicontinuousAt_iff_right (α := Circle)).mpr
    intro ε hε
    let T (n : ℕ) := (fun z : Circle ↦ z ^ n) ⁻¹' W
    have hDisj : Disjoint (Metric.ball (1 : Circle) ε)ᶜ (⋂ n, T n) := by
      refine Set.disjoint_left.mpr fun z hz hzT ↦ ?_
      have hz1 := Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two (z := z)
        (fun n _ ↦ hBall (mem_iInter.mp hzT n))
      exact hz (hz1.symm ▸ Metric.mem_ball_self hε)
    obtain ⟨N, hN⟩ := (isClosed_compl_iff.mpr Metric.isOpen_ball).isCompact
      |>.elim_finite_subfamily_closed T
        (fun n ↦ Metric.isClosed_closedBall.preimage (continuous_pow n)) hDisj
    have hNear : ∀ᶠ x : G in 𝓝 1, ∀ n ∈ N, x ^ n ∈ U :=
      (eventually_all_finset N).2 fun n _ ↦
        (continuous_pow n).tendsto' 1 1 (one_pow n) hU
    filter_upwards [hNear] with x hx f
    have hPow : f.1 x ∈ ⋂ n ∈ N, T n := by
      simp only [mem_iInter, T, mem_preimage, ← map_pow]
      exact fun n hn ↦ f.2 (hx n hn)
    have hMem : f.1 x ∈ Metric.ball (1 : Circle) ε := by
      by_contra hz
      exact (Set.disjoint_left.mp hN) hz hPow
    simpa [Function.comp_def, map_one, Metric.mem_ball, dist_comm] using hMem
  let A := {f : ContinuousMonoidHom G Circle | MapsTo f U W}
  let C := ContinuousMonoidHom.toContinuousMap '' A
  have hPointwise : ContinuousMap.toFun '' C =
      Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
    ext f
    constructor
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      exact ⟨hψ, ψ.toMonoidHom, rfl⟩
    · rintro ⟨hf, ψ, rfl⟩
      let ψc : ContinuousMonoidHom G Circle :=
        { toMonoidHom := ψ, continuous_toFun := hEqui.continuous ⟨ψ, hf⟩ }
      exact ⟨ψc.toContinuousMap, ⟨ψc, hf, rfl⟩, rfl⟩
  have hC : IsCompact C := by
    apply ArzelaAscoli.isCompact_of_equicontinuous
    · rw [hPointwise]
      exact ((isClosed_set_pi fun _ _ ↦ Metric.isClosed_closedBall).inter
        (MonoidHom.isClosed_range_coe G Circle)).isCompact
    · refine (equicontinuous_iff_range (F := fun f : C ↦ f.1.toFun)).mpr ?_
      rw [← Set.image_eq_range ContinuousMap.toFun C, hPointwise]
      have hRange : range (fun f : S ↦ (f.1 : G → Circle)) =
          Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
        ext f
        constructor
        · rintro ⟨ψ, rfl⟩
          exact ⟨ψ.2, ψ.1, rfl⟩
        · rintro ⟨hf, ψ, rfl⟩
          exact ⟨⟨ψ, hf⟩, rfl⟩
      rw [← hRange]
      exact equicontinuous_iff_range.mp hEqui
  exact (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).isCompact_iff.mpr hC

end InfoGeometry.Topology.PontryaginDualRealCyclicCompact

end noncomputable section
