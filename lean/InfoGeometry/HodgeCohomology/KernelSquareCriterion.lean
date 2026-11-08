/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range

/-! Kernel stability is exactly the absence of a nonzero vector both in the
range and kernel. No positive inner product or adjoint is assumed. -/
namespace InfoGeometry.HodgeCohomology

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem kernel_square_eq_iff (f : V →ₗ[R] V) :
    LinearMap.ker (f.comp f) = LinearMap.ker f ↔
      Disjoint (LinearMap.range f) (LinearMap.ker f) := by
  rw [Submodule.disjoint_def]
  constructor
  · intro he y hy hk
    obtain ⟨x, rfl⟩ := hy
    have hx : x ∈ LinearMap.ker (f.comp f) := hk
    rw [he] at hx
    exact hx
  · intro hd
    ext x
    constructor
    · intro hx
      exact hd (f x) ⟨x, rfl⟩ hx
    · intro hx
      change f (f x) = 0
      change f x = 0 at hx
      rw [hx, map_zero]

/-- A square-zero operator has stable kernel precisely when it is zero. -/
theorem square_zero_kernel_stable_iff (f : V →ₗ[R] V) (hf : f.comp f = 0) :
    LinearMap.ker (f.comp f) = LinearMap.ker f ↔ f = 0 := by
  rw [hf, LinearMap.ker_zero, eq_comm, LinearMap.ker_eq_top]

end InfoGeometry.HodgeCohomology
