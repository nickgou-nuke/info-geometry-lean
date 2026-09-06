import Mathlib

/-!
# Free abelian groups

The reference implementation builds a free abelian group through a custom
quotient. Lean 4/mathlib already owns this construction, so this module
exposes the universal-property surface needed by direct sums and homology.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace FreeAbelian

variable {α : Type u} {A : Type v} [AddCommGroup A]

abbrev Carrier (α : Type u) := FreeAbelianGroup α

def inclusion (x : α) : Carrier α := FreeAbelianGroup.of x

theorem inclusion_apply (x : α) : inclusion x = FreeAbelianGroup.of x := rfl

def descend (f : α → A) : Carrier α →+ A := FreeAbelianGroup.lift f

@[simp] theorem descend_inclusion (f : α → A) (x : α) :
    descend f (inclusion x) = f x := by
  exact FreeAbelianGroup.lift_apply_of f x

theorem descend_unique (f : α → A) (g : Carrier α →+ A)
    (h : ∀ x, g (inclusion x) = f x) :
    g = descend f := by
  apply AddMonoidHom.ext
  intro x
  induction x using FreeAbelianGroup.induction_on with
  | C0 => simp
  | C1 x => exact (h x).trans (descend_inclusion f x).symm
  | Cn x hx => simp [hx, h]
  | Cp x y hx hy => simp [map_add, hx, hy]

end FreeAbelian
end InfoGeometry.Spectral.Algebra
