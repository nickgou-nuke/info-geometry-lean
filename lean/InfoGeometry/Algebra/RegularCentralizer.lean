/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.AssociativeRegularCommutant
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Star.Module
import Mathlib.Basic.Real.Star

/-!
# The opposite algebra as the full regular centralizer

The existing `AssociativeRegularCommutant` owner identifies the commutant as a
set. Here that identification is upgraded to a native algebra equivalence
from the opposite algebra to the actual `Subalgebra.centralizer` inside
`Module.End R A`. Multiplication order is retained and the inverse is the
explicit evaluation at `1`; no finite dimension or matrix carrier is used.

Over the reals, star is a linear involution interchanging the two regular
actions. This is an algebraic regular representation statement. It does not
construct a Hilbert completion, cyclic separating state, modular operator,
or spacetime horizon.
-/

namespace InfoGeometry.Algebra.RegularCentralizer

open MulOpposite
open AssociativeRegularCommutant

section Algebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- The full centralizer of the existing left regular action. -/
abbrev leftCentralizer : Subalgebra R (Module.End R A) :=
  Subalgebra.centralizer R (Set.range (leftRegular (R := R) : A → Module.End R A))

theorem mem_leftCentralizer_iff (T : Module.End R A) :
    T ∈ leftCentralizer (R := R) (A := A) ↔
      T ∈ leftRegularCommutant (R := R) := by
  constructor
  · intro h a x
    have he := (Subalgebra.mem_centralizer_iff R).mp h
      (leftRegular (R := R) a) ⟨a, rfl⟩
    exact (LinearMap.congr_fun he x).symm
  · intro h
    apply (Subalgebra.mem_centralizer_iff R).mpr
    rintro _ ⟨a, rfl⟩
    apply LinearMap.ext
    intro x
    exact (h a x).symm

/-- Right multiplication is an algebra homomorphism from the opposite algebra. -/
def rightRegularHom : Aᵐᵒᵖ →ₐ[R] Module.End R A where
  toFun b := rightRegular (R := R) (unop b)
  map_zero' := by ext x; exact mul_zero x
  map_one' := by ext x; exact mul_one x
  map_add' a b := by ext x; exact mul_add x (unop a) (unop b)
  map_mul' a b := by
    ext x
    exact (mul_assoc x (unop b) (unop a)).symm
  commutes' r := by
    ext x
    change x * algebraMap R A r = r • x
    rw [← Algebra.commutes r x, Algebra.smul_def]

@[simp] theorem rightRegularHom_apply (b : Aᵐᵒᵖ) (x : A) :
    rightRegularHom (R := R) b x = x * unop b := rfl

theorem rightRegularHom_mem_leftCentralizer (b : Aᵐᵒᵖ) :
    rightRegularHom (R := R) b ∈ leftCentralizer (R := R) :=
  (mem_leftCentralizer_iff _).mpr (rightRegular_mem_leftRegularCommutant (unop b))

/-- Equality of native subalgebras, reusing the set-level regular commutant theorem. -/
theorem leftCentralizer_eq_rightRegularHom_range :
    leftCentralizer (R := R) (A := A) = (rightRegularHom (R := R) (A := A)).range := by
  ext T
  rw [mem_leftCentralizer_iff, leftRegularCommutant_eq_rightRegular_range]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨op b, hb.symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨unop b, hb.symm⟩

/-- Right multiplication, now with its actual centralizer codomain. -/
def rightToCentralizer : Aᵐᵒᵖ →ₐ[R] leftCentralizer (R := R) (A := A) :=
  (rightRegularHom (R := R)).codRestrict _ rightRegularHom_mem_leftCentralizer

/-- The full regular commutant is the opposite algebra, with a constructive inverse. -/
def regularCentralizerEquiv :
    Aᵐᵒᵖ ≃ₐ[R] leftCentralizer (R := R) (A := A) where
  __ := rightToCentralizer (R := R)
  invFun T := op (T.1 1)
  left_inv b := by simp [rightToCentralizer, rightRegularHom, rightRegular]
  right_inv T := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    have h := (mem_leftCentralizer_iff T.1).mp T.2 x 1
    simpa [rightToCentralizer, rightRegularHom, rightRegular, leftRegular] using h.symm

@[simp] theorem regularCentralizerEquiv_apply (b : Aᵐᵒᵖ) (x : A) :
    (regularCentralizerEquiv (R := R) b : Module.End R A) x = x * unop b := rfl

@[simp] theorem regularCentralizerEquiv_symm_apply
    (T : leftCentralizer (R := R) (A := A)) :
    (regularCentralizerEquiv (R := R)).symm T = op (T.1 1) := rfl

/-- A proper supported corner cannot be a full centralizer: it lacks the ambient unit. -/
theorem centralizer_ne_proper_corner (s : Set A) (e : A) (he : e ≠ 1) :
    (Subalgebra.centralizer R s : Set A) ≠ {x : A | e * x = x ∧ x * e = x} := by
  intro h
  have h1 : (1 : A) ∈ (Subalgebra.centralizer R s : Set A) :=
    (Subalgebra.centralizer R s).one_mem
  rw [h] at h1
  exact he (by simpa using h1.1)

end Algebra

section RealStar

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

/-- The ordinary star involution is real-linear; it is not a square-minus-one phase. -/
abbrev realStar : A ≃ₗ[ℝ] A := starLinearEquiv ℝ

@[simp] theorem realStar_apply (x : A) : realStar x = star x := rfl

theorem realStar_square :
    realStar.toLinearMap * realStar.toLinearMap = (1 : Module.End ℝ A) := by
  ext x
  exact star_star x

/-- Conjugation reverses the regular side and applies star to the coefficient. -/
theorem realStar_leftRegular (a : A) :
    realStar.toLinearMap * leftRegular (R := ℝ) a * realStar.toLinearMap =
      rightRegular (R := ℝ) (star a) := by
  ext x
  change star (a * star x) = x * star a
  rw [star_mul, star_star]

theorem realStar_rightRegular (a : A) :
    realStar.toLinearMap * rightRegular (R := ℝ) a * realStar.toLinearMap =
      leftRegular (R := ℝ) (star a) := by
  ext x
  change star (star x * a) = star a * x
  rw [star_mul, star_star]

end RealStar

end InfoGeometry.Algebra.RegularCentralizer
