import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Left modules

The old Spectral file introduces a custom left-module hierarchy and custom
module homomorphisms. Lean 4/mathlib already has the corresponding native
structures, so this port exposes the useful carrier-level interface without
duplicating those typeclasses.
-/

namespace InfoGeometry.Spectral.Algebra.LeftModule

universe u v

variable {R : Type u} {M : Type v} {N : Type v}
variable [Ring R]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- A native left module carrier. -/
abbrev Carrier (R : Type u) [Ring R] := ModuleCat R

/-- The categorical carrier associated to a concrete native module. -/
abbrev of (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] :
    ModuleCat R :=
  ModuleCat.of R M

/-- Native module morphisms are linear maps. -/
abbrev Hom (R : Type u) (M : Type v) (N : Type v)
    [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] :=
  M →ₗ[R] N

@[simp] theorem map_zero (f : M →ₗ[R] N) : f 0 = 0 :=
  f.map_zero

@[simp] theorem map_add (f : M →ₗ[R] N) (x y : M) :
    f (x + y) = f x + f y :=
  f.map_add x y

@[simp] theorem map_smul (f : M →ₗ[R] N) (r : R) (x : M) :
    f (r • x) = r • f x :=
  f.map_smul r x

theorem map_add_smul (f : M →ₗ[R] N) (a b : R) (x y : M) :
    f (a • x + b • y) = a • f x + b • f y := by
  rw [f.map_add, f.map_smul, f.map_smul]

end InfoGeometry.Spectral.Algebra.LeftModule
