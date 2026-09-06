import Mathlib
import Mathlib.Tactic.FieldSimp
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Thermo.ComplexThermodynamicLift

Proof-only complex lift of the elementary thermodynamic algebra.

This module formalizes the rule:

  real thermodynamic formulas that are algebraic identities
  may be lifted to complex coordinates.

It proves only algebraic identities over `ℂ`.

No zeta theorem.
No analytic continuation.
No self-concordance claim.
No Hilbert--Pólya claim.
No socket.
No certificate.
-/

noncomputable section

namespace InfoGeometry.Thermo.ComplexThermodynamicLift


/-! ## 1. Complex first law algebra -/

/--
Complexified first-law datum.

`β` is inverse temperature / modular scale.
`T` is temperature.
`dS = β dQ`.
`T = β⁻¹`.

This is an algebraic complex lift of the reversible scalar identity.
-/
@[rep_depth thermo]
structure ComplexFirstLawDatum where
  dQ : ℂ
  dS : ℂ
  β : ℂ
  T : ℂ
  firstLaw_inverse : dS = β * dQ
  temperature_eq_inv_beta : T = β⁻¹

namespace ComplexFirstLawDatum

variable (D : ComplexFirstLawDatum)

/--
If `β ≠ 0`, then `T dS = dQ`.

This is the complex algebraic lift of `δQ = T dS`.
-/
@[rep_depth thermo]
theorem temperature_mul_entropy_eq_heat
    (hβ : D.β ≠ 0) :
    D.T * D.dS = D.dQ := by
  rw [D.temperature_eq_inv_beta, D.firstLaw_inverse]
  field_simp [hβ]

/--
If `dQ ≠ 0`, then `β = dS / dQ`.

This is the complex algebraic lift of `β = dS / δQ`.
-/
@[rep_depth thermo]
theorem beta_eq_entropy_div_heat
    (hQ : D.dQ ≠ 0) :
    D.β = D.dS / D.dQ := by
  rw [D.firstLaw_inverse]
  field_simp [hQ]

/--
If `β ≠ 0`, then `T⁻¹ = β`.
-/
@[rep_depth thermo]
theorem inv_temperature_eq_beta
    (hβ : D.β ≠ 0) :
    D.T⁻¹ = D.β := by
  rw [D.temperature_eq_inv_beta]
  field_simp [hβ]

/--
If `β ≠ 0` and `dQ ≠ 0`, then `T⁻¹ = dS / dQ`.
-/
@[rep_depth thermo]
theorem inv_temperature_eq_entropy_div_heat
    (hβ : D.β ≠ 0)
    (hQ : D.dQ ≠ 0) :
    D.T⁻¹ = D.dS / D.dQ := by
  rw [D.inv_temperature_eq_beta hβ]
  exact D.beta_eq_entropy_div_heat hQ

end ComplexFirstLawDatum


/-! ## 2. Complex Bregman algebra -/

/--
Complex Bregman expression associated to an arbitrary potential `Φ`
and an arbitrary gradient field `grad`.

`DΦ(z,w) = Φ z - Φ w - grad w * (z - w)`.

This is only the algebraic expression. Convexity/positivity is not asserted
over `ℂ`.
-/
@[rep_depth thermo]
def complexBregman
    (Φ grad : ℂ → ℂ)
    (z w : ℂ) : ℂ :=
  Φ z - Φ w - grad w * (z - w)

/--
The complex Bregman expression vanishes on the diagonal.
-/
@[rep_depth thermo]
theorem complexBregman_self
    (Φ grad : ℂ → ℂ)
    (z : ℂ) :
    complexBregman Φ grad z z = 0 := by
  unfold complexBregman
  ring

/--
Three-point identity for the complex Bregman expression.

`D(x,z) = D(x,y) + D(y,z) + (grad y - grad z) * (x - y)`.
-/
@[rep_depth thermo]
theorem complexBregman_three_point
    (Φ grad : ℂ → ℂ)
    (x y z : ℂ) :
    complexBregman Φ grad x z =
      complexBregman Φ grad x y
        + complexBregman Φ grad y z
        + (grad y - grad z) * (x - y) := by
  unfold complexBregman
  ring

/--
Symmetrized complex Bregman expression.

`D(z,w) + D(w,z) = (grad z - grad w) * (z - w)`.
-/
@[rep_depth thermo]
theorem complexBregman_symm_sum
    (Φ grad : ℂ → ℂ)
    (z w : ℂ) :
    complexBregman Φ grad z w
      + complexBregman Φ grad w z =
        (grad z - grad w) * (z - w) := by
  unfold complexBregman
  ring


/-! ## 3. Cayley functional-equation algebra -/

/--
Cayley coordinate for the functional-equation involution.

`w = (s - 1) / s`.
-/
@[rep_depth projective]
def cayleyFE (s : ℂ) : ℂ :=
  (s - 1) / s

/--
Inverse Cayley coordinate.

`s = 1 / (1 - w)`.
-/
@[rep_depth projective]
def invCayleyFE (w : ℂ) : ℂ :=
  1 / (1 - w)

/--
The reflection `s ↦ 1 - s` becomes inversion in Cayley coordinate.

This is a purely algebraic theorem over `ℂ`.
-/
@[rep_depth projective]
theorem cayley_reflection_eq_inv
    (s : ℂ)
    (h1s : 1 - s ≠ 0)
    (hsm1 : s - 1 ≠ 0) :
    cayleyFE (1 - s) = (cayleyFE s)⁻¹ := by
  unfold cayleyFE
  field_simp [h1s, hsm1]
  ring

/--
`invCayleyFE` is a left inverse to `cayleyFE` away from the excluded points.
-/
@[rep_depth projective]
theorem invCayley_cayley
    (s : ℂ)
    (hs0 : s ≠ 0) :
    invCayleyFE (cayleyFE s) = s := by
  unfold invCayleyFE cayleyFE
  field_simp [hs0]
  ring

/--
`cayleyFE` is a left inverse to `invCayleyFE` away from the excluded point.
-/
@[rep_depth projective]
theorem cayley_invCayley
    (w : ℂ)
    (hw : 1 - w ≠ 0) :
    cayleyFE (invCayleyFE w) = w := by
  unfold cayleyFE invCayleyFE
  field_simp [hw]
  ring


end InfoGeometry.Thermo.ComplexThermodynamicLift
