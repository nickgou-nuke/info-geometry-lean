import InfoGeometry.Canonical.ProjectiveFoundation
import InfoGeometry.Canonical.PSLDescent
import InfoGeometry.Topology.ProjectiveKleinCompactification

/-!
# Klein monodromy representation space

This file records only the theorem-safe algebraic signatures needed for the
"it is not the sphere, it is the bottle" lane.

It does not construct a character variety, prove Painlevé isomonodromy, or show
that a geometric quotient is a manifold.  It packages:

* the Klein relation `a * b * a⁻¹ = b⁻¹` in an abstract target group;
* the `SL₂ -> PSL₂` kernel-triviality contract already available from Mathlib;
* the existing finite rational matrix witness from
  `Topology.ProjectiveKleinCompactification`.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

open InfoGeometry.Canonical.ProjectiveFoundation
open InfoGeometry.Canonical.PSLDescent
open InfoGeometry.Topology.ProjectiveKleinCompactification

/-- Abstract algebraic target for a Klein-bottle monodromy representation. -/
structure KleinMonodromyPair (G : Type*) [Group G] where
  a : G
  b : G
  relation : a * b * a⁻¹ = b⁻¹

namespace KleinMonodromyPair

variable {G : Type*} [Group G]
variable (ρ : KleinMonodromyPair G)

/-- Equivalent four-term readback of the Klein relation. -/
theorem relation_mul_inv_right :
    ρ.a * ρ.b * ρ.a⁻¹ * ρ.b = 1 := by
  calc
    ρ.a * ρ.b * ρ.a⁻¹ * ρ.b = (ρ.b⁻¹) * ρ.b := by rw [ρ.relation]
    _ = 1 := inv_mul_cancel ρ.b

end KleinMonodromyPair

/--
Projective descent contract for the Möbius/upper-half-plane lane.

This records exactly the kernel-triviality already proved in
`Canonical.PSLDescent`: the central sign `-g` acts the same as `g` on the base.
-/
def psl2rDescentContract : PSLDescentContract :=
  pslDescentContract

/--
Finite formula-level projective witness over exact rational `2 x 2` matrices.

This is not a `PSL₂(ℝ)` character variety point.  It is only the existing exact
matrix witness that the central sign quotient and Klein relation hold in the
projective chart.
-/
structure FiniteProjectiveKleinWitness where
  projective_sign : ProjectivelyEqual I2 minusI2
  twist_conjugates_parabolic : twistA * parabolicB * twistA = parabolicBInv
  klein_relation : twistA * parabolicB * twistA * parabolicB = I2
  mobius_refocus : ∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]
  mobius_square_projective : ProjectivelyEqual (mobiusS * mobiusS) I2

/-- The existing rational matrix formulas provide the finite projective witness. -/
def finiteProjectiveKleinWitness : FiniteProjectiveKleinWitness where
  projective_sign := projective_identifies_central_sign
  twist_conjugates_parabolic := twist_conjugates_parabolic
  klein_relation := klein_bottle_relation
  mobius_refocus := mobius_refocus_vector
  mobius_square_projective := mobius_square_projectively_identity

/-- Readback: the finite witness satisfies the Klein presentation equation. -/
theorem finite_klein_relation :
    finiteProjectiveKleinWitness.klein_relation = klein_bottle_relation := rfl

/-- Readback: the projective chart identifies the central sign. -/
theorem finite_projective_sign :
    finiteProjectiveKleinWitness.projective_sign = projective_identifies_central_sign := rfl

/-- Compact theorem packet for the current formula-level Klein monodromy lane. -/
theorem finite_formula_packet (t : ℚ) :
    ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      mobiusS.mulVec ![t, 1] = ![-1, t] ∧
      ProjectivelyEqual (mobiusS * mobiusS) I2 := by
  exact ⟨finiteProjectiveKleinWitness.projective_sign,
    finiteProjectiveKleinWitness.klein_relation,
    finiteProjectiveKleinWitness.mobius_refocus t,
    finiteProjectiveKleinWitness.mobius_square_projective⟩

end InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

end noncomputable section
