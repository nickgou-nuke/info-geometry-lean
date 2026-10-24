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

/-- For an injective ambient operator, being a graph forces the first-coordinate
operator to be bijective. Surjectivity alone is insufficient for an inverse. -/
theorem map_graph_eq_iff_of_injective (T : Module.End R (M × N))
    (hT : Function.Injective T) (f g : M →ₗ[R] N) :
    f.graph.map T = g.graph ↔
      (∀ x, (T (x, f x)).2 = g (T (x, f x)).1) ∧
      Function.Bijective (fun x => (T (x, f x)).1) := by
  rw [map_graph_eq_iff]
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨hc, ⟨?_, hs⟩⟩
    intro x y hxy
    have he : T (x, f x) = T (y, f y) :=
      Prod.ext hxy ((hc x).trans ((congrArg g hxy).trans (hc y).symm))
    exact congrArg Prod.fst (hT he)
  · rintro ⟨hc, hi, hs⟩
    exact ⟨hc, hs⟩

/-- Exact domain of a graph coordinate under an injective ambient operator.
This replaces an assumed denominator inverse with a necessary and sufficient
condition, with no finite-dimensional or commutative-scalar restriction. -/
theorem exists_map_graph_iff (T : Module.End R (M × N))
    (hT : Function.Injective T) (f : M →ₗ[R] N) :
    (∃ g : M →ₗ[R] N, f.graph.map T = g.graph) ↔
      Function.Bijective (fun x => (T (x, f x)).1) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ((map_graph_eq_iff_of_injective T hT f g).mp hg).2
  · intro h
    let top := (LinearMap.fst R M N).comp (T.comp (LinearMap.id.prod f))
    let bottom := (LinearMap.snd R M N).comp (T.comp (LinearMap.id.prod f))
    let u : M ≃ₗ[R] M := LinearEquiv.ofBijective top h
    refine ⟨bottom.comp u.symm.toLinearMap, (map_graph_eq_iff T _ _).mpr ⟨?_, h.2⟩⟩
    intro x
    change bottom x = bottom (u.symm (u x))
    rw [u.symm_apply_apply]

/-- Swapping the two summands turns a graph into the graph of `g` exactly when
`f` and `g` are two-sided inverses. The summands need not be isomorphic in advance. -/
theorem swap_map_graph_eq_iff (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    f.graph.map (LinearEquiv.prodComm R M N).toLinearMap = g.graph ↔
      Function.LeftInverse g f ∧ Function.RightInverse g f := by
  constructor
  · intro h
    constructor
    · intro x
      have hx : (f x, x) ∈ f.graph.map (LinearEquiv.prodComm R M N).toLinearMap :=
        ⟨(x, f x), rfl, rfl⟩
      rw [h] at hx
      exact hx.symm
    · intro y
      have hy : (y, g y) ∈ f.graph.map (LinearEquiv.prodComm R M N).toLinearMap := by
        rw [h]; rfl
      obtain ⟨z, hz, he⟩ := hy
      have h1 : z.2 = y := congrArg Prod.fst he
      have h2 : z.1 = g y := congrArg Prod.snd he
      change z.2 = f z.1 at hz
      rw [h1, h2] at hz
      exact hz.symm
  · rintro ⟨hl, hr⟩
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change w.1 = g w.2
      change w.2 = f w.1 at hw
      rw [hw, hl]
    · intro hz
      refine ⟨(z.2, z.1), ?_, rfl⟩
      change z.1 = f z.2
      change z.2 = g z.1 at hz
      rw [hz, hr]

/-- A coordinate swap remains in a graph chart exactly on the invertible locus. -/
theorem exists_swap_map_graph_iff (f : M →ₗ[R] N) :
    (∃ g : N →ₗ[R] M,
      f.graph.map (LinearEquiv.prodComm R M N).toLinearMap = g.graph) ↔
      Function.Bijective f := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨hl, hr⟩ := (swap_map_graph_eq_iff f g).mp hg
    exact ⟨hl.injective, hr.surjective⟩
  · intro hf
    let e := LinearEquiv.ofBijective f hf
    exact ⟨e.symm.toLinearMap, (swap_map_graph_eq_iff _ _).mpr
      ⟨e.symm_apply_apply, e.apply_symm_apply⟩⟩

/-- A nonzero kernel is an obstruction to staying in the graph chart even
under the invertible ambient coordinate swap. -/
theorem swap_map_graph_ne_of_kernel (f : M →ₗ[R] N) {x : M}
    (hx : x ≠ 0) (hfx : f x = 0) (g : N →ₗ[R] M) :
    f.graph.map (LinearEquiv.prodComm R M N).toLinearMap ≠ g.graph := by
  intro h
  have hi := ((exists_swap_map_graph_iff f).mp ⟨g, h⟩).1
  exact hx (hi (hfx.trans f.map_zero.symm))

end InfoGeometry.SuperGrassmannian.GraphChartTransition
