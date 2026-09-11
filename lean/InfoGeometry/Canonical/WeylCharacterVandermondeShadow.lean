import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.Spin44CharacterShadow
import InfoGeometry.Canonical.VandermondeExclusionBridge

/-!
# InfoGeometry.Canonical.WeylCharacterVandermondeShadow

Finite shadow bridge between the existing D4/`Spin(4,4)` character lane and the
finite Vandermonde exclusion lane.

This file is intentionally narrow:

* the character side is the already-owned finite weight-sum shadow from
  `Spin44CharacterShadow`;
* the denominator side is the finite Vandermonde determinant / collision
  criterion from `VandermondeExclusionBridge`;
* the bridge is a packaging layer saying that a finite character readout can be
  paired with a finite exclusion regulator.

It does **not** prove:

* Souriau orbit integral equals representation character,
* general Weyl character formula,
* cancellation/regularity of the full numerator-denominator quotient,
* Type III / AQFT / operator-trace statements.
-/

namespace InfoGeometry.Canonical.WeylCharacterVandermondeShadow

open InfoGeometry.Canonical.Spin44CharacterShadow
open InfoGeometry.Canonical.VandermondeExclusionBridge

section FiniteShadow

variable {R : Type*} [CommRing R] {n : ℕ}

variable (D : Fin n → R)

/-- The denominator shadow is exactly the finite Vandermonde determinant. -/
@[rep_depth thermo]
def DenominatorShadow.value : R :=
  VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant D

/-- The denominator shadow unfolds to the Vandermonde determinant. -/
@[rep_depth thermo]
theorem DenominatorShadow.value_eq_determinant :
    value D =
      VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant D := rfl

end FiniteShadow

section D4Packet

/--
Finite D4 character/Vandermonde packet.

The numerator is one of the existing finite `Spin(4,4)` character shadows; the
denominator is a separate finite Vandermonde shadow on a scalar node family.
-/
@[rep_depth thermo]
structure D4CharacterVandermondePacket where
  β : Cartan4
  numerator : ℝ
  denominatorNodes : Fin 4 → ℝ
  numerator_eq_vector :
      numerator = vectorCharacter β
    ∨ numerator = spinorEvenCharacter β
    ∨ numerator = spinorOddCharacter β
    ∨ numerator = diracSpinorCharacter β
  denominatorWitness : Fin 4 → ℝ
  denominatorWitness_nodes :
    denominatorWitness = denominatorNodes

namespace D4CharacterVandermondePacket

variable (P : D4CharacterVandermondePacket)

/-- The packaged denominator value is the Vandermonde determinant of the nodes. -/
@[rep_depth thermo]
theorem denominator_eq_vandermonde :
    VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant
        P.denominatorWitness =
      Matrix.det (Matrix.vandermonde P.denominatorNodes) := by
  unfold VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant
    VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.matrix
  rw [P.denominatorWitness_nodes]

/-- The denominator zero-locus is exactly collision of two distinct nodes. -/
@[rep_depth thermo]
theorem denominator_eq_zero_iff_collision :
    VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant
        P.denominatorWitness = 0 ↔
      ∃ i j : Fin 4,
        P.denominatorNodes i = P.denominatorNodes j ∧ i ≠ j := by
  rw [← P.denominatorWitness_nodes]
  exact
    VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant_eq_zero_iff_collision
      P.denominatorWitness

/-- Nonzero denominator is equivalent to injectivity of the denominator nodes. -/
@[rep_depth thermo]
theorem denominator_ne_zero_iff_injective :
    VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant
        P.denominatorWitness ≠ 0 ↔ Function.Injective P.denominatorNodes := by
  rw [← P.denominatorWitness_nodes]
  exact
    VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant_ne_zero_iff_injective
      P.denominatorWitness

/--
Finite shadow packet:
the numerator is one of the existing D4 character shadows, and the denominator
is governed by finite Vandermonde exclusion.
-/
@[rep_depth thermo]
theorem finite_character_denominator_packet :
    (P.numerator = vectorCharacter P.β
      ∨ P.numerator = spinorEvenCharacter P.β
      ∨ P.numerator = spinorOddCharacter P.β
      ∨ P.numerator = diracSpinorCharacter P.β)
    ∧
    (VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant
        P.denominatorWitness = 0 ↔
      ∃ i j : Fin 4,
        P.denominatorNodes i = P.denominatorNodes j ∧ i ≠ j)
    ∧
    (VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant
        P.denominatorWitness ≠ 0 ↔ Function.Injective P.denominatorNodes) := by
  exact
    ⟨P.numerator_eq_vector,
      P.denominator_eq_zero_iff_collision,
      P.denominator_ne_zero_iff_injective⟩

end D4CharacterVandermondePacket

end D4Packet

end InfoGeometry.Canonical.WeylCharacterVandermondeShadow
