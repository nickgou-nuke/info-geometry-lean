import Mathlib
import InfoGeometry.Canonical.SingleParticleFockStateBridge
import InfoGeometry.Physics.NuclearFiniteNilpotentSoul

/-!
# Mathlib exterior-algebra realization of the finite nuclear soul

The abstract `FiniteSoul` owner requires only a certified nilpotence order.
This module supplies a genuine Grassmann realization using Mathlib's exterior
algebra.

For every one-form generator `θ = ι(v)`:

* `θ² = 0`;
* generators anticommute;
* `θ` is therefore a `FiniteSoul` of order two;
* `1+θ` has the exact inverse `1-θ`.

This is the precise finite Grassmann statement currently supported.  It does
not identify an arbitrary odd exterior element with a one-form and does not
assert a general Berezinian formula.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearExteriorGrassmannSoul

open ExteriorAlgebra
open InfoGeometry.Canonical.SingleParticleFockStateBridge
open InfoGeometry.Physics.NuclearFiniteNilpotentSoul
open InfoGeometry.Algebra.CyclotomicOperatorProjectors

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

abbrev GrassmannAlgebra := ExteriorAlgebra R V

/-- Grassmann one-form generator. -/
def theta (v : V) : GrassmannAlgebra :=
  ExteriorAlgebra.ι R v

@[simp] theorem theta_sq (v : V) :
    theta (R := R) v * theta (R := R) v = 0 := by
  exact ExteriorAlgebra.ι_sq_zero v

/-- Grassmann generators anticommute. -/
theorem theta_anticomm (v w : V) :
    theta (R := R) v * theta (R := R) w =
      -(theta (R := R) w * theta (R := R) v) := by
  exact exterior_generator_anticomm v w

/-- A one-form Grassmann generator has nilpotence order two. -/
theorem theta_isNilpotent_two (v : V) :
    IsNilpotent (theta (R := R) v) 2 := by
  simpa [IsNilpotent, pow_two] using theta_sq (R := R) v

/-- A Mathlib exterior generator as the abstract finite-soul carrier. -/
def thetaFiniteSoul (v : V) : FiniteSoul (GrassmannAlgebra (R := R) (V := V)) where
  value := theta (R := R) v
  order := 2
  nilpotent := theta_isNilpotent_two (R := R) v

/-- Exact inverse of a one-generator Grassmann unipotent. -/
theorem one_add_theta_mul_one_sub_theta (v : V) :
    (1 + theta (R := R) v) * (1 - theta (R := R) v) = 1 := by
  have hsq := theta_sq (R := R) v
  noncomm_ring [hsq]

/-- The inverse also works from the right. -/
theorem one_sub_theta_mul_one_add_theta (v : V) :
    (1 - theta (R := R) v) * (1 + theta (R := R) v) = 1 := by
  have hsq := theta_sq (R := R) v
  noncomm_ring [hsq]

/-- The abstract finite-soul inverse polynomial agrees with the explicit
`1-θ` formula at nilpotence order two. -/
theorem theta_inversePolynomial_eq (v : V) :
    (thetaFiniteSoul (R := R) v).inversePolynomial =
      1 - theta (R := R) v := by
  simp [FiniteSoul.inversePolynomial, thetaFiniteSoul,
    unipotentInvPoly, Finset.sum_range_succ, pow_two]

/-- Consolidated genuine Grassmann one-form packet. -/
theorem grassmann_one_form_packet (v w : V) :
    theta (R := R) v * theta (R := R) v = 0 ∧
      theta (R := R) v * theta (R := R) w =
        -(theta (R := R) w * theta (R := R) v) ∧
      (1 + theta (R := R) v) * (1 - theta (R := R) v) = 1 ∧
      (1 - theta (R := R) v) * (1 + theta (R := R) v) = 1 :=
  ⟨theta_sq (R := R) v,
    theta_anticomm (R := R) v w,
    one_add_theta_mul_one_sub_theta (R := R) v,
    one_sub_theta_mul_one_add_theta (R := R) v⟩

end InfoGeometry.Physics.NuclearExteriorGrassmannSoul

end noncomputable section
