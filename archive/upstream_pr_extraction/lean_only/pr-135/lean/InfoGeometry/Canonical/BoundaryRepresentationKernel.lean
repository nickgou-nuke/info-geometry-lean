import Mathlib

/-!
# Kernel API for simultaneous boundary intertwiners

For a finite family of source and target operators, this file packages the
generator-wise intertwining equations as one linear map.  It is deliberately
independent of a particular boundary representation or colimit carrier.
-/

namespace InfoGeometry.Canonical.BoundaryRepresentationKernel

variable {R V W ι : Type*}
  [CommRing R]
  [AddCommGroup V] [AddCommGroup W]
  [Module R V] [Module R W]

/-- The defect of a candidate linear intertwiner at one generator. -/
def intertwinerDefect
    (source : ι → Module.End R V)
    (target : ι → Module.End R W)
    (i : ι) (T : V →ₗ[R] W) : V →ₗ[R] W :=
  (T.comp (source i)) - ((target i).comp T)

/-- All generator-wise intertwining defects, bundled into one linear map. -/
def simultaneousIntertwinerMap
    (source : ι → Module.End R V)
    (target : ι → Module.End R W) :
    (V →ₗ[R] W) →ₗ[R] (ι → (V →ₗ[R] W)) where
  toFun T := fun i => intertwinerDefect source target i T
  map_add' T U := by
    funext i
    ext x
    simp [intertwinerDefect]
    module
  map_smul' c T := by
    funext i
    ext x
    simp [intertwinerDefect]
    module

@[simp] theorem simultaneousIntertwinerMap_apply
    (source : ι → Module.End R V)
    (target : ι → Module.End R W)
    (T : V →ₗ[R] W) (i : ι) :
    simultaneousIntertwinerMap source target T i =
      T.comp (source i) - (target i).comp T :=
  rfl

/-- Membership in the kernel is exactly the generator-wise intertwining law. -/
theorem mem_ker_simultaneousIntertwinerMap_iff
    (source : ι → Module.End R V)
    (target : ι → Module.End R W)
    (T : V →ₗ[R] W) :
    T ∈ LinearMap.ker (simultaneousIntertwinerMap source target) ↔
      ∀ i, T.comp (source i) = (target i).comp T := by
  constructor
  · intro h i
    have hi := congrFun h i
    exact sub_eq_zero.mp hi
  · intro h
    change simultaneousIntertwinerMap source target T = 0
    ext i x
    exact sub_eq_zero.mpr (congrArg (fun f => f x) (h i))

/-- Zero kernel is equivalent to uniqueness of the zero simultaneous
intertwiner. -/
theorem ker_simultaneousIntertwinerMap_eq_bot_iff
    (source : ι → Module.End R V)
    (target : ι → Module.End R W) :
    LinearMap.ker (simultaneousIntertwinerMap source target) = ⊥ ↔
      ∀ T : V →ₗ[R] W,
        (∀ i, T.comp (source i) = (target i).comp T) → T = 0 := by
  constructor
  · intro h T hT
    have hmem : T ∈ LinearMap.ker (simultaneousIntertwinerMap source target) :=
      (mem_ker_simultaneousIntertwinerMap_iff source target T).2 hT
    have : T ∈ (⊥ : Submodule R (V →ₗ[R] W)) := by simpa [h] using hmem
    simpa using this
  · intro h
    apply le_antisymm
    · intro T hT
      change simultaneousIntertwinerMap source target T = 0 at hT
      have hzero : T = 0 := h T
        ((mem_ker_simultaneousIntertwinerMap_iff source target T).1 hT)
      exact hzero ▸ (Submodule.zero_mem (⊥ : Submodule R (V →ₗ[R] W)))
    · exact bot_le

/-- Finite-dimensional consequence of a trivial intertwiner kernel. -/
theorem simultaneousIntertwinerMap_kernel_finrank_zero_of_eq_bot
    {K V W ι : Type*}
    [Field K]
    [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (source : ι → Module.End K V)
    (target : ι → Module.End K W)
    (hker : LinearMap.ker (simultaneousIntertwinerMap source target) = ⊥) :
    Module.finrank K (LinearMap.ker (simultaneousIntertwinerMap source target)) = 0 := by
  rw [hker]
  simp

/-- In the same finite-dimensional setting, zero kernel finrank is equivalent
to the kernel being the bottom submodule. -/
theorem simultaneousIntertwinerMap_kernel_eq_bot_of_finrank_zero
    {K V W ι : Type*}
    [Field K]
    [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (source : ι → Module.End K V)
    (target : ι → Module.End K W)
    (hfin : Module.finrank K
        (LinearMap.ker (simultaneousIntertwinerMap source target)) = 0) :
    LinearMap.ker (simultaneousIntertwinerMap source target) = ⊥ := by
  exact Submodule.finrank_eq_zero.mp hfin

/-- Rank-nullity for the bundled simultaneous intertwiner defect map. -/
theorem simultaneousIntertwinerMap_finrank_range_add_kernel
    {K V W ι : Type*}
    [Field K]
    [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (source : ι → Module.End K V)
    (target : ι → Module.End K W) :
    Module.finrank K
          (LinearMap.range (simultaneousIntertwinerMap source target)) +
        Module.finrank K
          (LinearMap.ker (simultaneousIntertwinerMap source target)) =
      Module.finrank K (V →ₗ[K] W) := by
  exact LinearMap.finrank_range_add_finrank_ker _

/-- A trivial simultaneous intertwiner kernel makes the defect map injective. -/
theorem simultaneousIntertwinerMap_range_finrank_eq_domain_finrank_of_eq_bot
    {K V W ι : Type*}
    [Field K]
    [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (source : ι → Module.End K V)
    (target : ι → Module.End K W)
    (hker : LinearMap.ker (simultaneousIntertwinerMap source target) = ⊥) :
    Module.finrank K
        (LinearMap.range (simultaneousIntertwinerMap source target)) =
      Module.finrank K (V →ₗ[K] W) := by
  have hrank := simultaneousIntertwinerMap_finrank_range_add_kernel
    source target
  rw [hker] at hrank
  simpa using hrank

end InfoGeometry.Canonical.BoundaryRepresentationKernel
