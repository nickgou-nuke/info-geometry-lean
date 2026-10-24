/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.ProjectorGraphChart

/-!
# Exact graph-chart domains and ordered block transitions

An arbitrary change of coordinates need not keep a submodule in the same graph
chart. The first-coordinate map must cover the target, and the second coordinate
must depend only on it. An invertible first-coordinate map gives the familiar
fractional formula, with the order of operator composition retained.
-/

namespace InfoGeometry.SuperGrassmannian.GraphChartTransition

variable {R M N : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Exact criterion for a linear image of a graph to equal another graph.
The map on the ambient module need not be invertible. -/
theorem map_graph_eq_iff (T : Module.End R (M × N))
    (f g : M →ₗ[R] N) :
    f.graph.map T = g.graph ↔
      (∀ x, (T (x, f x)).2 = g (T (x, f x)).1) ∧
      Function.Surjective (fun x => (T (x, f x)).1) := by
  constructor
  · intro h
    constructor
    · intro x
      have hx : T (x, f x) ∈ f.graph.map T := ⟨(x, f x), rfl, rfl⟩
      rw [h] at hx
      exact hx
    · intro x
      have hx : (x, g x) ∈ f.graph.map T := by rw [h]; rfl
      obtain ⟨z, hz, he⟩ := hx
      have hz' : z = (z.1, f z.1) := Prod.ext rfl hz
      refine ⟨z.1, ?_⟩
      change (T (z.1, f z.1)).1 = x
      rw [← hz']
      exact congrArg Prod.fst he
  · rintro ⟨hcompat, hsurj⟩
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : w = (w.1, f w.1) := Prod.ext rfl hw
      rw [hw']
      exact hcompat w.1
    · intro hz
      obtain ⟨x, hx⟩ := hsurj z.1
      refine ⟨(x, f x), rfl, Prod.ext hx ?_⟩
      exact (hcompat x).trans ((congrArg g hx).trans hz.symm)

/-- The noncommutative fractional graph transition. `u` supplies a genuine
inverse of the first-coordinate operator `a + b ∘ f`; the inverse is on the
right of `c + d ∘ f`. -/
theorem block_map_graph (a : Module.End R M) (b : N →ₗ[R] M)
    (c : M →ₗ[R] N) (d : Module.End R N) (f : M →ₗ[R] N)
    (u : M ≃ₗ[R] M) (hu : u.toLinearMap = a + b.comp f) :
    f.graph.map ((a.coprod b).prod (c.coprod d)) =
      ((c + d.comp f).comp u.symm.toLinearMap).graph := by
  apply (map_graph_eq_iff _ _ _).mpr
  have htop (x : M) : a x + b (f x) = u x := by
    exact (LinearMap.congr_fun hu x).symm
  constructor
  · intro x
    change c x + d (f x) = c (u.symm (a x + b (f x))) +
      d (f (u.symm (a x + b (f x))))
    rw [htop, u.symm_apply_apply]
  · intro x
    refine ⟨u.symm x, ?_⟩
    change a (u.symm x) + b (f (u.symm x)) = x
    rw [htop, u.apply_symm_apply]

end InfoGeometry.SuperGrassmannian.GraphChartTransition
