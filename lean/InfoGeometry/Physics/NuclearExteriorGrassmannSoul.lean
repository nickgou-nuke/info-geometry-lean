import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
def theta (v : V) : GrassmannAlgebra (R := R) (V := V) :=
  ExteriorAlgebra.ι R v

@[simp] theorem theta_sq (v : V) :
    theta (R := R) (V := V) v * theta (R := R) (V := V) v = 0 := by
  exact ExteriorAlgebra.ι_sq_zero v

/-- Grassmann generators anticommute. -/
theorem theta_anticomm (v w : V) :
    theta (R := R) (V := V) v * theta (R := R) (V := V) w =
      -(theta (R := R) (V := V) w * theta (R := R) (V := V) v) := by
  have h := neg_eq_iff_add_eq_zero.mpr
    (ExteriorAlgebra.ι_add_mul_swap (R := R) (M := V) v w)
  change ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
    -(ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v)
  calc
    ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
        -(-(ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w)) := by simp
    _ = -(ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v) := by rw [h]

/-- A one-form Grassmann generator has nilpotence order two. -/
theorem theta_isNilpotent_two (v : V) :
    InfoGeometry.Algebra.CyclotomicOperatorProjectors.IsNilpotent
      (theta (R := R) (V := V) v) 2 := by
  simpa [InfoGeometry.Algebra.CyclotomicOperatorProjectors.IsNilpotent, pow_two]
    using theta_sq (R := R) (V := V) v

/-- A Mathlib exterior generator as the abstract finite-soul carrier. -/
def thetaFiniteSoul (v : V) : FiniteSoul (GrassmannAlgebra (R := R) (V := V)) where
  value := theta (R := R) (V := V) v
  order := 2
  nilpotent := theta_isNilpotent_two v

/-- Exact inverse of a one-generator Grassmann unipotent. -/
theorem one_add_theta_mul_one_sub_theta (v : V) :
    (1 + theta (R := R) (V := V) v) * (1 - theta (R := R) (V := V) v) = 1 := by
  have hsq := theta_sq (R := R) (V := V) v
  calc
    (1 + theta (R := R) (V := V) v) * (1 - theta (R := R) (V := V) v) =
        1 - theta (R := R) (V := V) v * theta (R := R) (V := V) v := by noncomm_ring
    _ = 1 := by rw [hsq]; simp

/-- The inverse also works from the right. -/
theorem one_sub_theta_mul_one_add_theta (v : V) :
    (1 - theta (R := R) (V := V) v) * (1 + theta (R := R) (V := V) v) = 1 := by
  have hsq := theta_sq (R := R) (V := V) v
  calc
    (1 - theta (R := R) (V := V) v) * (1 + theta (R := R) (V := V) v) =
        1 - theta (R := R) (V := V) v * theta (R := R) (V := V) v := by noncomm_ring
    _ = 1 := by rw [hsq]; simp

/-- The abstract finite-soul inverse polynomial agrees with the explicit
`1-θ` formula at nilpotence order two. -/
theorem theta_inversePolynomial_eq (v : V) :
    (thetaFiniteSoul v).inversePolynomial =
      1 - theta (R := R) (V := V) v := by
  simp [FiniteSoul.inversePolynomial, thetaFiniteSoul,
    unipotentInvPoly, sub_eq_add_neg]
  abel

/-- Consolidated genuine Grassmann one-form packet. -/
theorem grassmann_one_form_packet (v w : V) :
    theta (R := R) (V := V) v * theta (R := R) (V := V) v = 0 ∧
      theta (R := R) (V := V) v * theta (R := R) (V := V) w =
        -(theta (R := R) (V := V) w * theta (R := R) (V := V) v) ∧
      (1 + theta (R := R) (V := V) v) *
          (1 - theta (R := R) (V := V) v) = 1 ∧
      (1 - theta (R := R) (V := V) v) *
          (1 + theta (R := R) (V := V) v) = 1 :=
  ⟨theta_sq v, theta_anticomm v w,
    one_add_theta_mul_one_sub_theta v,
    one_sub_theta_mul_one_add_theta v⟩

end InfoGeometry.Physics.NuclearExteriorGrassmannSoul

end noncomputable section
