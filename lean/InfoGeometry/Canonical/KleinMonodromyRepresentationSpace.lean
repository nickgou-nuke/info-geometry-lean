import InfoGeometry.Canonical.ProjectiveFoundation
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

end KleinMonodromyPair

/-- Owner-backed `SL(2,ℝ)` central-kernel descent datum. -/
def psl2rDescentContract : PSLDescentContract :=
  pslDescentContract

/-- Direct readback of the central-kernel descent law. -/
theorem psl2r_kernel_trivial
    (g : SL2R) (tau : UpperHalfPlane) :
    (-g) • tau = g • tau :=
  psl2rDescentContract.sl2r_kernel_trivial_on_base g tau

/-- Exact finite projective Klein laws, expressed without an evidence record. -/
abbrev FiniteProjectiveKleinWitness : Prop :=
  ProjectivelyEqual I2 minusI2 ∧
    twistA * parabolicB * twistA = parabolicBInv ∧
    twistA * parabolicB * twistA * parabolicB = I2 ∧
    (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
    ProjectivelyEqual (mobiusS * mobiusS) I2

namespace FiniteProjectiveKleinWitness

theorem projective_sign (h : FiniteProjectiveKleinWitness) :
    ProjectivelyEqual I2 minusI2 :=
  h.1

theorem twist_conjugates_parabolic (h : FiniteProjectiveKleinWitness) :
    twistA * parabolicB * twistA = parabolicBInv :=
  h.2.1

theorem klein_relation (h : FiniteProjectiveKleinWitness) :
    twistA * parabolicB * twistA * parabolicB = I2 :=
  h.2.2.1

theorem mobius_refocus (h : FiniteProjectiveKleinWitness) :
    ∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t] :=
  h.2.2.2.1

theorem mobius_square_projective (h : FiniteProjectiveKleinWitness) :
    ProjectivelyEqual (mobiusS * mobiusS) I2 :=
  h.2.2.2.2

end FiniteProjectiveKleinWitness

/-- Canonical finite witness supplied by the exact rational matrix theorems. -/
theorem finiteProjectiveKleinWitness : FiniteProjectiveKleinWitness :=
  ⟨projective_identifies_central_sign,
   twist_conjugates_parabolic,
   klein_bottle_relation,
   mobius_refocus_vector,
   mobius_square_projectively_identity⟩

/-- The finite rational model satisfies the Klein presentation equation. -/
theorem finite_klein_relation :
    twistA * parabolicB * twistA * parabolicB = I2 :=
  finiteProjectiveKleinWitness.klein_relation

/-- The finite rational projective chart identifies the central sign. -/
theorem finite_projective_sign :
    ProjectivelyEqual I2 minusI2 :=
  finiteProjectiveKleinWitness.projective_sign

/-- The twist conjugates the parabolic generator to its inverse. -/
theorem finite_twist_conjugates_parabolic :
    twistA * parabolicB * twistA = parabolicBInv :=
  finiteProjectiveKleinWitness.twist_conjugates_parabolic

/-- The Möbius generator is projectively involutive. -/
theorem finite_mobius_square_projective :
    ProjectivelyEqual (mobiusS * mobiusS) I2 :=
  finiteProjectiveKleinWitness.mobius_square_projective

/-- Direct finite formula synthesis from the native matrix owner. -/
theorem finite_formula_packet (t : ℚ) :
    ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      mobiusS.mulVec ![t, 1] = ![-1, t] ∧
      ProjectivelyEqual (mobiusS * mobiusS) I2 :=
  projective_klein_formula_packet t

end InfoGeometry.Canonical.KleinMonodromyRepresentationSpace
