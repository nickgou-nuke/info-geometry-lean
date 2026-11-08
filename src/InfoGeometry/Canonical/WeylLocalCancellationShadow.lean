import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.WeylAlternatingNumeratorShadow

/-!
# InfoGeometry.Canonical.WeylLocalCancellationShadow

Local finite cancellation shadow for the Weyl-character corridor.

This file does not prove the full Weyl character formula.  It formalizes only a
local quotient lane on the noncollision domain:

* a finite alternating Gibbs numerator,
* a finite Vandermonde denominator,
* an explicit hypothesis that the numerator vanishes on the denominator
  collision locus,
* a quotient readout defined only when the denominator is nonzero.
-/

namespace InfoGeometry.Canonical.WeylLocalCancellationShadow

open InfoGeometry.Canonical.WeylAlternatingNumeratorShadow
open InfoGeometry.Canonical.WeylCharacterVandermondeShadow

section LocalShadow

/--
Local finite cancellation data for a D4 shadow packet.

The field `numerator_zero_on_collision` is the precise replacement for prose
claims that the alternating numerator vanishes on the Weyl-denominator
collision locus.
-/
@[rep_depth thermo]
structure LocalCancellationShadowPacket (σ : Type*) [Fintype σ] where
  data : D4AlternatingCharacterShadowPacket σ
  numerator_zero_on_collision :
    (∃ i j : Fin 4,
        data.denominatorPacket.denominatorNodes i =
          data.denominatorPacket.denominatorNodes j ∧ i ≠ j) →
      data.numeratorData.value = 0

namespace LocalCancellationShadowPacket

variable {σ : Type*} [Fintype σ]
variable (P : LocalCancellationShadowPacket σ)

/-- The finite denominator value. -/
@[rep_depth thermo]
def denominator : ℝ :=
  VandermondeExclusionBridge.FiniteVandermondeExclusionWitness.determinant
    P.data.denominatorPacket.denominatorWitness

/-- The finite numerator value. -/
@[rep_depth thermo]
noncomputable def numerator : ℝ :=
  P.data.numeratorData.value

/-- The noncollision domain is the locus where the finite denominator is nonzero. -/
@[rep_depth thermo]
def NoncollisionDomain : Prop :=
  P.denominator ≠ 0

/--
Local quotient readout on the noncollision domain.

This is the honest finite replacement for a Weyl-character quotient: it is only
defined when the denominator is nonzero.
-/
@[rep_depth thermo]
 noncomputable def quotient (_h : P.NoncollisionDomain) : ℝ :=
  P.numerator / P.denominator

@[rep_depth thermo]
theorem denominator_eq_zero_iff_collision :
    P.denominator = 0 ↔
      ∃ i j : Fin 4,
        P.data.denominatorPacket.denominatorNodes i =
          P.data.denominatorPacket.denominatorNodes j ∧ i ≠ j := by
  exact P.data.denominatorPacket.denominator_eq_zero_iff_collision

@[rep_depth thermo]
theorem denominator_ne_zero_iff_injective :
    P.denominator ≠ 0 ↔ Function.Injective P.data.denominatorPacket.denominatorNodes := by
  exact P.data.denominatorPacket.denominator_ne_zero_iff_injective

/-- On the collision locus, the numerator vanishes by hypothesis. -/
@[rep_depth thermo]
theorem numerator_eq_zero_of_collision
    (hcoll :
      ∃ i j : Fin 4,
        P.data.denominatorPacket.denominatorNodes i =
          P.data.denominatorPacket.denominatorNodes j ∧ i ≠ j) :
    P.numerator = 0 :=
  P.numerator_zero_on_collision hcoll

/--
If the denominator vanishes, then the numerator also vanishes.

This is the local cancellation shadow statement, but not yet a quotient
regularity theorem.
-/
@[rep_depth thermo]
theorem denominator_zero_forces_numerator_zero
    (hden : P.denominator = 0) :
    P.numerator = 0 := by
  exact P.numerator_eq_zero_of_collision ((P.denominator_eq_zero_iff_collision).mp hden)

/-- The quotient unfolds to the ordinary scalar ratio on the noncollision domain. -/
@[rep_depth thermo]
theorem quotient_eq_ratio (h : P.NoncollisionDomain) :
    P.quotient h = P.numerator / P.denominator := rfl

/-- The noncollision-domain quotient is well-typed because the denominator is nonzero. -/
@[rep_depth thermo]
theorem quotient_domain_packet :
    (P.NoncollisionDomain ↔ P.denominator ≠ 0) ∧
      (∀ h : P.NoncollisionDomain, P.quotient h = P.numerator / P.denominator) := by
  exact ⟨Iff.rfl, fun h => P.quotient_eq_ratio h⟩

/--
Combined local cancellation packet.

This is the strongest honest finite statement in this lane:

* denominator zero iff collision,
* numerator vanishes on collisions,
* quotient exists on the noncollision domain.
-/
@[rep_depth thermo]
theorem local_cancellation_packet :
    (P.denominator = 0 ↔
      ∃ i j : Fin 4,
        P.data.denominatorPacket.denominatorNodes i =
          P.data.denominatorPacket.denominatorNodes j ∧ i ≠ j)
    ∧
    ((∃ i j : Fin 4,
        P.data.denominatorPacket.denominatorNodes i =
          P.data.denominatorPacket.denominatorNodes j ∧ i ≠ j) →
      P.numerator = 0)
    ∧
    (P.NoncollisionDomain ↔ P.denominator ≠ 0) := by
  exact
    ⟨P.denominator_eq_zero_iff_collision,
      P.numerator_zero_on_collision,
      Iff.rfl⟩

end LocalCancellationShadowPacket

end LocalShadow

end InfoGeometry.Canonical.WeylLocalCancellationShadow
