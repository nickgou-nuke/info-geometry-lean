import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ColorCARStandardModel

/-!
# Native finite Furey charge readout

This module promotes the theorem-safe finite occupation/charge layer from the
`proofs` package onto the main `InfoGeometry` library surface.

The carrier is the existing native three-colour `Cl(5,5)` CAR owner.  The
operator `fureyCharge` is one third of the total three-mode number operator.
The scalar occupation readout has spectrum `{0, 1/3, 2/3, 1}`.

No theorem here identifies this scalar with physical electric charge, assigns
particle labels to occupation words, proves a minimal-left-ideal theorem, or
constructs `SU(3)_C × U(1)_em` gauge dynamics.
-/

noncomputable section

namespace InfoGeometry.Physics.FureyCharges

open InfoGeometry.Physics.ColorCARStandardModel

abbrev FureyAlg : Type := CAR3

/-- One of the three native CAR number projectors. -/
def fureyNumber : Fin 3 → FureyAlg
  | 0 => numberOp0
  | 1 => numberOp1
  | 2 => numberOp2

/-- Total occupation operator over the three colour CAR modes. -/
def totalFureyNumber : FureyAlg :=
  ∑ i : Fin 3, fureyNumber i

/-- One-third normalized finite Furey occupation operator. -/
def fureyCharge : FureyAlg :=
  (1 / 3 : ℝ) • totalFureyNumber

/-- Each component number operator is idempotent. -/
theorem fureyNumber_idempotent (i : Fin 3) :
    fureyNumber i * fureyNumber i = fureyNumber i := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact numberOp0_idem
  · exact numberOp1_idem
  · exact numberOp2_idem

/-- Three Boolean occupation bits, one for each native CAR colour mode. -/
abbrev Occupation3 := Fin 3 → Bool

/-- Number of occupied modes in a Boolean occupation word. -/
def fureyOccupationNumber (w : Occupation3) : ℕ :=
  (if w 0 then 1 else 0) + (if w 1 then 1 else 0) + (if w 2 then 1 else 0)

/-- Scalar one-third normalized occupation readout. -/
def fureyOccupationCharge (w : Occupation3) : ℚ :=
  (fureyOccupationNumber w : ℚ) / 3

/-- The finite occupation-charge spectrum is exactly contained in
`{0, 1/3, 2/3, 1}`. -/
theorem fureyOccupationCharge_spectrum (w : Occupation3) :
    fureyOccupationCharge w = 0 ∨
    fureyOccupationCharge w = (1 / 3 : ℚ) ∨
    fureyOccupationCharge w = (2 / 3 : ℚ) ∨
    fureyOccupationCharge w = 1 := by
  dsimp [fureyOccupationCharge, fureyOccupationNumber]
  rcases w 0 <;> rcases w 1 <;> rcases w 2 <;> simp

/-- Consolidated theorem-safe Furey occupation packet. -/
theorem furey_charge_algebraic_spine :
    (∀ i : Fin 3, fureyNumber i * fureyNumber i = fureyNumber i) ∧
    (∀ w : Occupation3,
      fureyOccupationCharge w = 0 ∨
      fureyOccupationCharge w = (1 / 3 : ℚ) ∨
      fureyOccupationCharge w = (2 / 3 : ℚ) ∨
      fureyOccupationCharge w = 1) :=
  ⟨fureyNumber_idempotent, fureyOccupationCharge_spectrum⟩

end InfoGeometry.Physics.FureyCharges

end noncomputable section
