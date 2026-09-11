import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Free groups

The old Spectral reference implemented the free group by a word quotient.
Mathlib already owns that quotient and its universal property, so this file
exposes the small interface used by the reference without introducing a
second free-group carrier.
-/

namespace InfoGeometry.Spectral.Algebra.FreeGroup

universe u v

variable {X : Type u} {G : Type v} [Group G]

/-- The native free-group carrier. -/
abbrev Carrier (X : Type u) := FreeGroup X

/-- The canonical generator inclusion. -/
def inclusion (x : X) : Carrier X := FreeGroup.of x

@[simp]
theorem inclusion_apply (x : X) : inclusion x = FreeGroup.of x := rfl

/-- The homomorphism extending a function on the generators. -/
def descend (f : X → G) : Carrier X →* G := FreeGroup.lift f

@[simp]
theorem descend_inclusion (f : X → G) (x : X) :
    descend f (inclusion x) = f x := by
  change (FreeGroup.lift f) (FreeGroup.of x) = f x
  simp

/-!
The universal property is stated as equality of homomorphisms, which is the
Lean 4/mathlib replacement for the old pointwise homotopy formulation.
-/
theorem descend_unique (f : X → G) (g : Carrier X →* G)
    (h : ∀ x, g (inclusion x) = f x) :
    g = descend f := by
  apply MonoidHom.ext
  intro x
  induction x using FreeGroup.induction_on with
  | C1 => simp
  | of x => exact (h x).trans (descend_inclusion f x).symm
  | inv_of x hx => simp [hx]
  | mul x y hx hy => simp [map_mul, hx, hy]

end InfoGeometry.Spectral.Algebra.FreeGroup
