import InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterInnerAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Star.Basic

/-!
# Star-unitarity of the ternary Coxeter element

The Artin braid owner supplies self-adjoint involutions `β₁` and `β₂`, their
Artin relation, and the order-three Coxeter identity.  This file derives the
honest star identity for `c = β₂ β₁`.  The permutation of the colour
projections is deliberately not claimed here; it remains a separate closure
obligation.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterColorAction

open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterInnerAction
open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

theorem coxeter_star_eq_sq :
    star (coxeterElement g) = coxeterElement g * coxeterElement g := by
  calc
    star (coxeterElement g) =
        star (braidGenerator2 g * braidGenerator1 g) := rfl
    _ = star (braidGenerator1 g) * star (braidGenerator2 g) :=
      star_mul _ _
    _ = braidGenerator1 g * braidGenerator2 g := by
      rw [braidGenerator1_star g, braidGenerator2_star g]
    _ = braidGenerator1 g * braidGenerator2 g * 1 := by rw [mul_one]
    _ = braidGenerator1 g * braidGenerator2 g *
          (braidGenerator1 g * braidGenerator1 g) := by
      rw [braidGenerator1_sq g]
    _ = (braidGenerator1 g * braidGenerator2 g * braidGenerator1 g) *
          braidGenerator1 g := by
      noncomm_ring
    _ = (braidGenerator2 g * braidGenerator1 g * braidGenerator2 g) *
          braidGenerator1 g := by
      rw [artin_braid_relation g]
    _ = braidGenerator2 g * braidGenerator1 g *
          (braidGenerator2 g * braidGenerator1 g) := by
      noncomm_ring
    _ = coxeterElement g * coxeterElement g := rfl

theorem coxeter_star_eq_unit_inverse :
    star (coxeterElement g) = (↑((coxeterUnit g)⁻¹) : A) := by
  calc
    star (coxeterElement g) = coxeterElement g * coxeterElement g :=
      coxeter_star_eq_sq g
    _ = (↑((coxeterUnit g)⁻¹) : A) := by rfl

theorem coxeter_is_starUnitary :
    star (coxeterElement g) * coxeterElement g = 1 ∧
      coxeterElement g * star (coxeterElement g) = 1 := by
  rw [coxeter_star_eq_sq g]
  constructor
  · exact coxeterElement_cube g
  · simpa [mul_assoc] using coxeterElement_cube g

end InfoGeometry.Canonical.ToeplitzCuntzThreeCoxeterColorAction
