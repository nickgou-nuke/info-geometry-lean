import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.WeylCharacterVandermondeShadow

/-!
# InfoGeometry.Canonical.WeylAlternatingNumeratorShadow

Finite alternating Gibbs numerator shadow for the Weyl-character corridor.

This file introduces only the finite numerator lane:

* a finite index type playing the role of a Weyl-group shadow;
* a sign map taking values `±1`;
* a Gibbs exponent map;
* the resulting alternating exponential sum.

This is not a proof of the Weyl character formula.  It is the honest finite
owner surface needed before any local cancellation or quotient regularity shadow.
-/

namespace InfoGeometry.Canonical.WeylAlternatingNumeratorShadow

open scoped BigOperators

/-- A finite sign in the alternating numerator shadow. -/
@[rep_depth thermo]
def signBit (b : Bool) : ℝ :=
  if b then 1 else -1

@[rep_depth thermo]
theorem signBit_eq_one_or_neg_one (b : Bool) :
    signBit b = 1 ∨ signBit b = -1 := by
  cases b <;> simp [signBit]

/--
Finite alternating Gibbs numerator data.

`σ` is the finite shadow of the Weyl-group index set.  `sign` supplies the
alternating parity and `exponent` supplies the Gibbs exponent.
-/
@[rep_depth thermo]
structure AlternatingGibbsNumeratorData (σ : Type*) [Fintype σ] where
  sign : σ → Bool
  exponent : σ → ℝ

namespace AlternatingGibbsNumeratorData

variable {σ : Type*} [Fintype σ]
variable (N : AlternatingGibbsNumeratorData σ)

/-- The finite alternating Gibbs numerator. -/
@[rep_depth thermo]
noncomputable def value : ℝ :=
  ∑ w : σ, signBit (N.sign w) * Real.exp (N.exponent w)

/-- Pointwise numerator summand. -/
@[rep_depth thermo]
noncomputable def term (w : σ) : ℝ :=
  signBit (N.sign w) * Real.exp (N.exponent w)

@[rep_depth thermo]
theorem value_eq_sum_terms :
    N.value = ∑ w : σ, N.term w := rfl

/-- Each summand is a signed Gibbs factor. -/
@[rep_depth thermo]
theorem term_eq_signed_gibbs (w : σ) :
    N.term w = signBit (N.sign w) * Real.exp (N.exponent w) := rfl

/-- Each sign factor is exactly `+1` or `-1`. -/
@[rep_depth thermo]
theorem sign_factor_eq_one_or_neg_one (w : σ) :
    signBit (N.sign w) = 1 ∨ signBit (N.sign w) = -1 :=
  signBit_eq_one_or_neg_one (N.sign w)

/--
The numerator is a finite alternating sum of Gibbs factors.
-/
@[rep_depth thermo]
theorem alternating_gibbs_packet :
    N.value = ∑ w : σ, signBit (N.sign w) * Real.exp (N.exponent w) ∧
      ∀ w : σ, signBit (N.sign w) = 1 ∨ signBit (N.sign w) = -1 := by
  exact ⟨rfl, fun w => N.sign_factor_eq_one_or_neg_one w⟩

end AlternatingGibbsNumeratorData

section D4Shadow

open InfoGeometry.Canonical.WeylCharacterVandermondeShadow

/--
Finite D4 numerator/denominator shadow packet.

This combines the new alternating Gibbs numerator lane with the already-owned
finite Vandermonde denominator lane.  It is still only a shadow packet: no
quotient theorem is asserted.
-/
@[rep_depth thermo]
structure D4AlternatingCharacterShadowPacket (σ : Type*) [Fintype σ] where
  numeratorData : AlternatingGibbsNumeratorData σ
  denominatorPacket : D4CharacterVandermondePacket

namespace D4AlternatingCharacterShadowPacket

variable {σ : Type*} [Fintype σ]
variable (P : D4AlternatingCharacterShadowPacket σ)

/-- The numerator side is a finite alternating Gibbs sum. -/
@[rep_depth thermo]
theorem numerator_is_alternating_gibbs :
    P.numeratorData.value =
      ∑ w : σ,
        signBit (P.numeratorData.sign w) * Real.exp (P.numeratorData.exponent w) := by
  rfl

/-- The denominator side is governed by finite Vandermonde exclusion. -/
@[rep_depth thermo]
theorem denominator_zero_iff_collision :
    P.denominatorPacket.denominatorWitness.determinant = 0 ↔
      ∃ i j : Fin 4,
        P.denominatorPacket.denominatorNodes i =
          P.denominatorPacket.denominatorNodes j ∧ i ≠ j :=
  P.denominatorPacket.denominator_eq_zero_iff_collision

/-- The combined finite packet exposes both lanes without asserting quotient regularity. -/
@[rep_depth thermo]
theorem numerator_denominator_shadow_packet :
    (P.numeratorData.value =
      ∑ w : σ,
        signBit (P.numeratorData.sign w) * Real.exp (P.numeratorData.exponent w))
    ∧
    (P.denominatorPacket.denominatorWitness.determinant = 0 ↔
      ∃ i j : Fin 4,
        P.denominatorPacket.denominatorNodes i =
          P.denominatorPacket.denominatorNodes j ∧ i ≠ j) := by
  exact ⟨P.numerator_is_alternating_gibbs, P.denominator_zero_iff_collision⟩

end D4AlternatingCharacterShadowPacket

end D4Shadow

end InfoGeometry.Canonical.WeylAlternatingNumeratorShadow
