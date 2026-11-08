import Mathlib.Algebra.DirectSum.Module
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Direct sums for graded module families

This is the Lean 4 replacement for the quotient-based direct-sum layer in the
old Spectral reference. The carrier and universal map are delegated to
Mathlib's finite-support `DirectSum` construction.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedDirectSum

variable {I : Type v} [DecidableEq I]
variable (M : I → Type u) [∀ i, AddCommMonoid (M i)]

/-- The direct sum of the graded components. -/
abbrev Carrier := DirectSum I M

/-- Inclusion of one homogeneous component. -/
def inclusion (i : I) : M i →+ Carrier M := DirectSum.of M i

@[simp] theorem inclusion_apply (i : I) (x : M i) :
    inclusion M i x = DirectSum.of M i x := rfl

/-- The linear map induced by a family of component maps. -/
def descend {N : Type u} [AddCommMonoid N]
    (f : ∀ i, M i →+ N) : Carrier M →+ N :=
  DirectSum.toAddMonoid f

@[simp] theorem descend_inclusion {N : Type u} [AddCommMonoid N]
    (f : ∀ i, M i →+ N) (i : I) (x : M i) :
    descend M f (inclusion M i x) = f i x := by
  exact DirectSum.toAddMonoid_of f i x

/-- The component maps determine a linear map out of the direct sum. -/
theorem descend_unique {N : Type u} [AddCommMonoid N]
    (f : ∀ i, M i →+ N) (g : Carrier M →+ N)
    (h : ∀ i x, g (inclusion M i x) = f i x) :
    g = descend M f := by
  apply AddMonoidHom.ext
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x => exact (h i x).trans (descend_inclusion M f i x).symm
  | add x y hx hy => simp [map_add, hx, hy]

end GradedDirectSum
end InfoGeometry.Spectral.Algebra
