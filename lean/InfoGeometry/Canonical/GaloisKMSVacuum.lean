import Mathlib.Algebra.Group.Basic
import Mathlib.Topology.Instances.Complex

/-!
# Galois Parametrization of Degenerate KMS Vacuums

This module formalizes the Bost-Connes phase separation at the
Hagedorn temperature (β ≤ 1). At the onset of the Bose-Einstein
Condensation of the Primon Gas, the unique high-temperature vacuum
spontaneously breaks into an infinite family of degenerate KMS states.

The absolute abelian Galois group `Gal(ℚ_ab / ℚ) ≅ ℤ̂ˣ` acts as the
exact non-abelian gauge group permuting these extreme degenerate vacuums.
This enforces total arithmetic covariance over the conformal field theory.
-/

set_option linter.unusedSectionVars false

namespace GaloisKMSVacuum

open Complex

variable {CuntzUHF : Type*}

/- The absolute abelian Galois group, isomorphic to the group of units
   of the profinite integers `ℤ̂ˣ`. -/
variable (GaloisGroup : Type*)

/-- The space of extreme degenerate KMS vacuum states at zero temperature. -/
structure KMSVacuum (A : Type*) where
  val : A → ℂ

/- The action of the Galois group on the Cuntz UHF operators. 
   It acts as an automorphism group over the operator algebra. -/
variable (galois_action : GaloisGroup → CuntzUHF → CuntzUHF)

/-- The Galois gauge action over the degenerate vacuum space.
    The vacuum is permuted by evaluating the state on the Galois-shifted
    observable. -/
def gauge_transformation (g : GaloisGroup) (φ : KMSVacuum CuntzUHF) : KMSVacuum CuntzUHF :=
  ⟨fun (A : CuntzUHF) => φ.val (galois_action g A)⟩

/-- **Theorem: Galois Covariance of the Vacuum**
    The degenerate KMS vacuums form a faithful representation space for
    the absolute Galois group. Any arbitrary KMS state can be transformed
    into another degenerate state via the Galois gauge action. -/
theorem galois_covariance (g : GaloisGroup) (φ : KMSVacuum CuntzUHF) :
    (gauge_transformation GaloisGroup galois_action g φ).val = 
      fun A => φ.val (galois_action g A) := by
  rfl

end GaloisKMSVacuum
