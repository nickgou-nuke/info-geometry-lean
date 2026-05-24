import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Albert-Cayley-Dickson sign layer

This file defines the sign-parametrized Cayley-Dickson step.

The split case is identified by the theorem that the new generator squares
to `+1`, not by a convention-dependent name for `γ`.
-/

namespace InfoGeometry.Algebra.AlbertCD

structure CDInvolutionDatum (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] where
  star : A →ₗ[R] A
  star_involutive : star.comp star = LinearMap.id

/--
Raw Cayley-Dickson doubled carrier `A ⊕ A`.

The multiplication is intentionally not made into a `Ring` instance here,
because higher Cayley-Dickson stages may be nonassociative.
-/
structure CDStep (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] where
  re : A
  im : A

/--
Convention-dependent Albert multiplication.

TODO: instantiate once the base algebra laws are fixed.
-- DEBT_KIND: SORRY
-/
def albertMul
    {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (J : CDInvolutionDatum R A)
    (mulA : A → A → A)
    (γ : R)
    (x y : CDStep R A) : CDStep R A := by
  sorry

/--
The split condition: the new generator has square `+1`.

This is the convention-independent target theorem.
-- DEBT_KIND: SORRY
-/
def IsSplitStep
    {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    (J : CDInvolutionDatum R A)
    (mulA : A → A → A)
    (γ : R) : Prop := by
  sorry

end InfoGeometry.Algebra.AlbertCD
