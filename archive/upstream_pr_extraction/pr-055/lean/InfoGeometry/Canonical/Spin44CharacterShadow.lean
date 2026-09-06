import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Fintype.Basic

/-!
# Spin(4,4) Character Shadow

This file owns only the finite D4 weight-sum shadow for the three eight-state
triality sectors.  It does not construct `Spin(4,4)`, its representation
category, an infinite operator trace, a Dixmier trace, or a Drazin-core Witten
index.  Those remain separate owner obligations.
-/

namespace InfoGeometry.Canonical.Spin44CharacterShadow

open scoped BigOperators

/-- Four Cartan coordinates for the D4/`Spin(4,4)` character shadow. -/
@[rep_depth thermo]
abbrev Cartan4 := Fin 4 → ℝ

/-- Boolean sign used to enumerate spinor weights. -/
@[rep_depth thermo]
def signOfBool (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Number of minus signs in a Boolean sign word. -/
@[rep_depth thermo]
def minusCount (ε : Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 => ε i = false).card

/-- Even spinor parity: an even number of minus signs. -/
@[rep_depth thermo]
def EvenMinus (ε : Fin 4 → Bool) : Prop :=
  minusCount ε % 2 = 0

/-- Odd spinor parity: an odd number of minus signs. -/
@[rep_depth thermo]
def OddMinus (ε : Fin 4 → Bool) : Prop :=
  minusCount ε % 2 = 1

instance decidableEvenMinus : DecidablePred EvenMinus := by
  intro ε
  unfold EvenMinus
  infer_instance

instance decidableOddMinus : DecidablePred OddMinus := by
  intro ε
  unfold OddMinus
  infer_instance

/-- Half-spinor weight pairing `1/2 * Σᵢ ±βᵢ`. -/
@[rep_depth thermo]
noncomputable def halfSignedPairing (β : Cartan4) (ε : Fin 4 → Bool) : ℝ :=
  ((2 : ℝ)⁻¹) * ∑ i : Fin 4, signOfBool (ε i) * β i

/-- Vector character shadow: weights `±eᵢ`. -/
@[rep_depth thermo]
noncomputable def vectorCharacter (β : Cartan4) : ℝ :=
  ∑ i : Fin 4, (Real.exp (β i) + Real.exp (-(β i)))

/-- Hyperbolic-cosine form of the vector character shadow. -/
@[rep_depth thermo]
noncomputable def vectorCharacterCosh (β : Cartan4) : ℝ :=
  2 * ∑ i : Fin 4, Real.cosh (β i)

/-- The vector character shadow is `2 * Σᵢ cosh βᵢ`. -/
@[rep_depth thermo]
theorem vectorCharacter_eq_two_sum_cosh (β : Cartan4) :
    vectorCharacter β = vectorCharacterCosh β := by
  unfold vectorCharacter vectorCharacterCosh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Real.cosh_eq]
  ring

/-- Positive-chirality spinor character shadow: even number of minus signs. -/
@[rep_depth thermo]
noncomputable def spinorEvenCharacter (β : Cartan4) : ℝ :=
  ∑ ε ∈ (Finset.univ.filter fun ε : Fin 4 → Bool => EvenMinus ε),
    Real.exp (halfSignedPairing β ε)

/-- Negative-chirality spinor character shadow: odd number of minus signs. -/
@[rep_depth thermo]
noncomputable def spinorOddCharacter (β : Cartan4) : ℝ :=
  ∑ ε ∈ (Finset.univ.filter fun ε : Fin 4 → Bool => OddMinus ε),
    Real.exp (halfSignedPairing β ε)

/-- Dirac spinor character shadow: sum of the two half-spinor shadows. -/
@[rep_depth thermo]
noncomputable def diracSpinorCharacter (β : Cartan4) : ℝ :=
  spinorEvenCharacter β + spinorOddCharacter β

/-- Graded vector-minus-spinor supertrace shadow. -/
@[rep_depth thermo]
noncomputable def vectorMinusDiracSupertraceShadow (β : Cartan4) : ℝ :=
  vectorCharacter β - diracSpinorCharacter β

/-- Half-spinor difference shadow, often used as a finite Witten-index proxy. -/
@[rep_depth thermo]
noncomputable def halfSpinorDifferenceShadow (β : Cartan4) : ℝ :=
  spinorEvenCharacter β - spinorOddCharacter β

/-- The even D4 half-spinor sector has eight sign weights. -/
@[rep_depth thermo]
theorem evenMinus_card :
    (Finset.univ.filter fun ε : Fin 4 → Bool => EvenMinus ε).card = 8 := by
  decide

/-- The odd D4 half-spinor sector has eight sign weights. -/
@[rep_depth thermo]
theorem oddMinus_card :
    (Finset.univ.filter fun ε : Fin 4 → Bool => OddMinus ε).card = 8 := by
  decide

/-- The finite vector-minus-Dirac supertrace formula unfolds to its three character parts. -/
@[rep_depth thermo]
theorem vectorMinusDiracSupertraceShadow_eq
    (β : Cartan4) :
    vectorMinusDiracSupertraceShadow β =
      vectorCharacter β - (spinorEvenCharacter β + spinorOddCharacter β) := by
  rfl

/-- The finite half-spinor difference shadow unfolds to `χ_s - χ_c`. -/
@[rep_depth thermo]
theorem halfSpinorDifferenceShadow_eq
    (β : Cartan4) :
    halfSpinorDifferenceShadow β =
      spinorEvenCharacter β - spinorOddCharacter β := by
  rfl

end InfoGeometry.Canonical.Spin44CharacterShadow
