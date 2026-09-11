import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic
import InfoGeometry.Exceptional.CircularSplitOctonionContactLift
import InfoGeometry.Algebra.Zorn.G2ChiralOperatorNativeBridge

namespace InfoGeometry.Exceptional.Freudenthal

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Algebra.Zorn.G2ChiralOperatorNativeBridge
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-! ## The canonical label identification

The circular Peirce labels and the chiral-envelope labels are two names for
the same eight finite carrier positions.  This is only a label map: the
Freudenthal bracket is not identified with the associative envelope by this
definition.
-/

def circularChargeToChiralGenerator : CircularChargeAtom → ChiralGenerator
  | .plusPole => .pPlus
  | .minusPole => .pMinus
  | .plusRoot i => .sPlus i
  | .minusRoot i => .sMinus i

theorem circularChargeToChiralGenerator_injective :
    Function.Injective circularChargeToChiralGenerator := by
  intro a b h
  cases a <;> cases b <;>
    simp [circularChargeToChiralGenerator] at h ⊢ <;>
    try exact h

theorem circularChargeToChiralGenerator_index (a : CircularChargeAtom) :
    chiralGeneratorIndex (circularChargeToChiralGenerator a) =
      match a with
      | .plusPole => 0
      | .plusRoot i => ⟨i.val + 1, by omega⟩
      | .minusPole => 4
      | .minusRoot i => ⟨i.val + 5, by omega⟩ := by
  cases a with
  | plusPole => rfl
  | minusPole => rfl
  | plusRoot i =>
      fin_cases i <;> rfl
  | minusRoot i =>
      fin_cases i <;> rfl

theorem chiralEnvelopeRepresentation_on_circularCharge (a : CircularChargeAtom) :
    chiralEnvelopeRepresentation
        (ChiralOperatorEnvelope.ofGenerator (circularChargeToChiralGenerator a)) =
      L (circularPeirceBasis (chiralGeneratorIndex
        (circularChargeToChiralGenerator a))) := by
  exact chiralEnvelopeRepresentation_on_generator
    (circularChargeToChiralGenerator a)

theorem chiralEnvelopeRightRepresentation_on_circularCharge
    (a : CircularChargeAtom) :
    chiralEnvelopeRightRepresentation
        (ChiralOperatorEnvelope.ofGenerator (circularChargeToChiralGenerator a)) =
      R (circularPeirceBasis (chiralGeneratorIndex
        (circularChargeToChiralGenerator a))) := by
  exact chiralEnvelopeRightRepresentation_on_generator
    (circularChargeToChiralGenerator a)

def contactAtomToChiralGenerator : ContactAtom → ChiralGenerator
  | .eMinus => .pMinus
  | .minusOne a => circularChargeToChiralGenerator a
  | .plusOne a => circularChargeToChiralGenerator a
  | .ePlus => .pPlus

theorem contactAtomToChiralGenerator_poles :
    contactAtomToChiralGenerator (.eMinus) = .pMinus ∧
      contactAtomToChiralGenerator (.ePlus) = .pPlus := by
  exact ⟨rfl, rfl⟩

theorem contactAtomToChiralGenerator_charge_lanes (a : CircularChargeAtom) :
    contactAtomToChiralGenerator (.minusOne a) =
        circularChargeToChiralGenerator a ∧
      contactAtomToChiralGenerator (.plusOne a) =
        circularChargeToChiralGenerator a := by
  exact ⟨rfl, rfl⟩

theorem chiralEnvelopeRepresentation_on_contactAtom (a : ContactAtom) :
    chiralEnvelopeRepresentation
        (ChiralOperatorEnvelope.ofGenerator (contactAtomToChiralGenerator a)) =
      L (circularPeirceBasis (chiralGeneratorIndex
        (contactAtomToChiralGenerator a))) := by
  exact chiralEnvelopeRepresentation_on_generator
    (contactAtomToChiralGenerator a)

theorem chiralEnvelopeRightRepresentation_on_contactAtom (a : ContactAtom) :
    chiralEnvelopeRightRepresentation
        (ChiralOperatorEnvelope.ofGenerator (contactAtomToChiralGenerator a)) =
      R (circularPeirceBasis (chiralGeneratorIndex
        (contactAtomToChiralGenerator a))) := by
  exact chiralEnvelopeRightRepresentation_on_generator
    (contactAtomToChiralGenerator a)

/-!
# Freudenthal Heisenberg Supercharge Readback

This module connects the canonical anticommutation relations (CAR) of the circular chiral
basis with the macroscopic Lie bracket in the contact lanes $\mathfrak{g}_{-1}$ and $\mathfrak{g}_{+1}$.

Architectural Boundary:
This formalizes an ordinary Lie algebra representation where the symplectic form acts as the
bridge from the microscopic operator envelope to the macroscopic Heisenberg Lie bracket,
generating the extreme poles $E_-$ and $E_+$.
-/

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable (phi : ContactAtom → L)

/-- READBACK THEOREM: The bracket of Q_i⁺ and Q_j⁻ in 𝔤₋₁ yields 2 δ_ij E₋ -/
theorem bracket_minusOne_supercharges
    (omega_chiral : CircularChargeAtom → CircularChargeAtom → R)
    (h_omega_roots : ∀ i j : Fin 3,
      omega_chiral (.plusRoot i) (.minusRoot j) = if i = j then 1 else 0)
    (h_bracket_minus_minus : ∀ a b : CircularChargeAtom,
      ⁅phi (.minusOne a), phi (.minusOne b)⁆ =
      (2 : R) • (omega_chiral a b) • phi .eMinus)
    (i j : Fin 3) :
    ⁅phi (.minusOne (.plusRoot i)),
     phi (.minusOne (.minusRoot j))⁆ =
    if i = j then (2 : R) • phi .eMinus else 0 := by
  rw [h_bracket_minus_minus, h_omega_roots i j]
  split_ifs with h
  · simp only [one_smul]
  · simp only [zero_smul, smul_zero]

/-- READBACK THEOREM: The bracket of Q_i⁺ and Q_j⁻ in 𝔤₊₁ yields 2 δ_ij E₊ -/
theorem bracket_plusOne_supercharges
    (omega_chiral : CircularChargeAtom → CircularChargeAtom → R)
    (h_omega_roots : ∀ i j : Fin 3,
      omega_chiral (.plusRoot i) (.minusRoot j) = if i = j then 1 else 0)
    (h_bracket_plus_plus : ∀ a b : CircularChargeAtom,
      ⁅phi (.plusOne a), phi (.plusOne b)⁆ =
      (2 : R) • (omega_chiral a b) • phi .ePlus)
    (i j : Fin 3) :
    ⁅phi (.plusOne (.plusRoot i)),
     phi (.plusOne (.minusRoot j))⁆ =
    if i = j then (2 : R) • phi .ePlus else 0 := by
  rw [h_bracket_plus_plus, h_omega_roots i j]
  split_ifs with h
  · simp only [one_smul]
  · simp only [zero_smul, smul_zero]

end InfoGeometry.Exceptional.Freudenthal
