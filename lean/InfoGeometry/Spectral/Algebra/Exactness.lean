import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Exactness of linear maps

The old Spectral reference defines exactness for pointed and truncated
homotopy maps.  The reusable algebraic core needed by the Lean-native
spectral sequence owners is the ordinary module statement that the image of
the first map is the kernel of the second.
-/

namespace InfoGeometry.Spectral.Algebra.Exactness

universe u v w

variable {R : Type u} {M : Type v} {N : Type w} {P : Type*}
variable [Semiring R]
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]

/-- The first map is exact at the middle module. -/
def IsExact (f : M →ₗ[R] N) (g : N →ₗ[R] P) : Prop :=
  LinearMap.range f = LinearMap.ker g

theorem isExact_iff (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    IsExact f g ↔ LinearMap.range f = LinearMap.ker g :=
  Iff.rfl

theorem range_le_ker {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : IsExact f g) : LinearMap.range f ≤ LinearMap.ker g := by
  rw [h]

theorem comp_eq_zero {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : IsExact f g) : g.comp f = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.mem_ker.mp
  apply h ▸ (show f x ∈ LinearMap.range f from ⟨x, rfl⟩)

theorem mem_ker_iff_exists_preimage {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h : IsExact f g) (y : N) :
    y ∈ LinearMap.ker g ↔ ∃ x : M, f x = y := by
  rw [← h]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

end InfoGeometry.Spectral.Algebra.Exactness
