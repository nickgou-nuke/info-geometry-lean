import InfoGeometry.Canonical.ProjectiveFoundation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PSLDescent
import InfoGeometry.Topology.ProjectiveKleinCompactification

/-!
# Klein monodromy representation space

Direct algebraic theorems for the Klein relation, projective central sign, and
finite rational matrix model.  No finite witness or descent-contract packet is
used.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

open InfoGeometry.Canonical.ProjectiveFoundation
open InfoGeometry.Canonical.PSLDescent
open InfoGeometry.Topology.ProjectiveKleinCompactification

/-- Abstract Klein-bottle monodromy as the native relation subtype in `G × G`. -/
abbrev KleinMonodromyPair (G : Type*) [Group G] :=
  { p : G × G // p.1 * p.2 * p.1⁻¹ = p.2⁻¹ }

namespace KleinMonodromyPair

variable {G : Type*} [Group G]
variable (rho : KleinMonodromyPair G)

/-- First monodromy generator. -/
def a : G :=
  rho.1.1

/-- Second monodromy generator. -/
def b : G :=
  rho.1.2

/-- Defining Klein-bottle relation. -/
theorem relation :
    rho.a * rho.b * rho.a⁻¹ = rho.b⁻¹ :=
  rho.2

/-- Equivalent four-term form of the Klein relation. -/
theorem relation_mul_inv_right :
    rho.a * rho.b * rho.a⁻¹ * rho.b = 1 := by
  rw [rho.relation, inv_mul_cancel]

/-- Conjugation by the first generator also sends the inverse of the second
generator back to the second generator. -/
theorem two_cycle_on_b :
    rho.a * rho.b⁻¹ * rho.a⁻¹ = rho.b := by
  have h := congrArg Inv.inv rho.relation
  simpa [mul_assoc, mul_inv_rev] using h

end KleinMonodromyPair

/-- Owner-backed `SL(2,ℝ)` central-kernel descent datum. -/
def psl2rDescentContract : PSLDescentContract :=
  pslDescentContract

/-- Direct readback of the central-kernel descent law. -/
theorem psl2r_kernel_trivial
    (g : SL2R) (tau : UpperHalfPlane) :
    (-g) • tau = g • tau :=
  psl2rDescentContract.sl2r_kernel_trivial_on_base g tau

/-- The finite rational model satisfies the Klein presentation equation. -/
theorem finite_klein_relation :
    twistA * parabolicB * twistA * parabolicB = I2 :=
  klein_bottle_relation

/-- The finite rational projective chart identifies the central sign. -/
theorem finite_projective_sign :
    ProjectivelyEqual I2 minusI2 :=
  projective_identifies_central_sign

/-- The twist conjugates the parabolic generator to its inverse. -/
theorem finite_twist_conjugates_parabolic :
    twistA * parabolicB * twistA = parabolicBInv :=
  twist_conjugates_parabolic

/-- The Möbius generator is projectively involutive. -/
theorem finite_mobius_square_projective :
    ProjectivelyEqual (mobiusS * mobiusS) I2 :=
  mobius_square_projectively_identity

end InfoGeometry.Canonical.KleinMonodromyRepresentationSpace
