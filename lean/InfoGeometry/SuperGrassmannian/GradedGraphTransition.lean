/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GradedGraphChart
import InfoGeometry.SuperGrassmannian.GraphChartTransition

/-!
# Degree preservation on graph-chart overlaps

The inverse of a bijective degree-preserving operator preserves degree by the
native direct-sum decomposition. Consequently the ordered fractional graph
transition is degree-preserving wherever its denominator is invertible.
The scalar ring acting on the modules may be noncommutative.
-/

namespace InfoGeometry.SuperGrassmannian.GradedGraphTransition

open DirectSum GradedGraphChart

variable {A k ι U W : Type*} [Ring A] [CommRing k] [DecidableEq ι]
  [AddCommGroup U] [Module A U] [Module k U]
  [AddCommGroup W] [Module A W] [Module k W]
  (GU : ι → Submodule k U) (GW : ι → Submodule k W)
  [Decomposition GU] [Decomposition GW]

/-- Degree preservation of an equivalence forces degree preservation of its
inverse; it is not a second independent assumption. -/
theorem preservesDegree_symm (e : U ≃ₗ[A] W)
    (he : PreservesDegree GU GW e.toLinearMap) :
    PreservesDegree GW GU e.symm.toLinearMap := by
  intro i y hy
  have hc := map_component GU GW e.toLinearMap he i (e.symm y)
  have hcomp : (decompose GU (e.symm y) i : U) = e.symm y := by
    apply e.injective
    simpa only [LinearEquiv.coe_coe, e.apply_symm_apply,
      decompose_of_mem_same GW hy] using hc
  exact hcomp ▸ (decompose GU (e.symm y) i).property

omit [Decomposition GW] in
/-- Even block operators induce even fractional graph coordinates, with the
inverse in its correct noncommutative composition order. -/
theorem fractional_preservesDegree
    (a : Module.End A U) (b : W →ₗ[A] U)
    (c : U →ₗ[A] W) (d : Module.End A W) (f : U →ₗ[A] W)
    (ha : PreservesDegree GU GU a) (hb : PreservesDegree GW GU b)
    (hc : PreservesDegree GU GW c) (hd : PreservesDegree GW GW d)
    (hf : PreservesDegree GU GW f)
    (u : U ≃ₗ[A] U) (hu : u.toLinearMap = a + b.comp f) :
    PreservesDegree GU GW ((c + d.comp f).comp u.symm.toLinearMap) := by
  have htop : PreservesDegree GU GU u.toLinearMap := by
    rw [hu]
    intro i x hx
    exact (GU i).add_mem (ha i x hx) (hb i (f x) (hf i x hx))
  have hinv := preservesDegree_symm GU GU u htop
  intro i x hx
  exact (GW i).add_mem (hc i (u.symm x) (hinv i x hx))
    (hd i (f (u.symm x)) (hf i (u.symm x) (hinv i x hx)))

end InfoGeometry.SuperGrassmannian.GradedGraphTransition
