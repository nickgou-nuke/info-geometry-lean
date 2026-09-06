import Mathlib

namespace InfoGeometry.Algebra.Zorn

theorem LinearMap.map_span_of_maps
    {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N]
    (f : M →ₗ[R] N) (s : Set M) (t : Submodule R N)
    (h : ∀ x ∈ s, f x ∈ t) :
    Submodule.map f (Submodule.span R s) ≤ t := by
  rintro y ⟨x, hx, rfl⟩
  refine Submodule.span_induction (p := fun x _ => f x ∈ t) ?_ ?_ ?_ ?_ hx
  · intro x hx
    exact h x hx
  · simpa using t.zero_mem
  · intro x y _ _ hx hy
    simpa using t.add_mem hx hy
  · intro a x _ hx
    simpa using t.smul_mem a hx

end InfoGeometry.Algebra.Zorn
