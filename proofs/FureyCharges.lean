import proofs.ColorCARStandardModel

/-!
# Furey charge from the existing triple CAR layer

This file deliberately defines only the finite algebraic charge readout already
available in the repository: one-third of the total number operator over the
three CAR/Furey ladders.  It does **not** claim a full Standard Model theorem,
SU(3) stabilizer theorem, or analytic representation result.
-/

noncomputable section

namespace FureyCharges

open ColorCARStandardModel

set_option synthInstance.maxHeartbeats 1000000

/-- The finite algebra used for the three Furey/CAR ladders already present in
`ColorCARStandardModel`: three tensor factors of the chiral `M₂(ℂ)` CAR atom. -/
abbrev FureyAlg : Type := CAR3

/-- The Furey number operator on one of the three existing CAR ladders.

Convention: this follows the repository's chiral-number layer
`numberOpk = carAnnk * carCrek`, whose idempotence is already proved in
`ColorCARStandardModel`. -/
def fureyNumber : Fin 3 → FureyAlg
  | 0 => numberOp0
  | 1 => numberOp1
  | 2 => numberOp2

/-- Total Furey number over the three CAR ladders. -/
def totalFureyNumber : FureyAlg :=
  ∑ i : Fin 3, fureyNumber i

/-- Positive minimal-ideal Furey charge: one third of total occupation number.

This is intentionally named `fureyCharge`, not `electricCharge`: particle labels,
conjugate ideals, and the sign-reversed convention are separate layers. -/
def fureyCharge : FureyAlg :=
  (1 / 3 : ℂ) • totalFureyNumber

/-- Each Furey number operator is a projector. -/
theorem fureyNumber_idempotent (i : Fin 3) :
    fureyNumber i * fureyNumber i = fureyNumber i := by
  fin_cases i
  · exact ColorCARStandardModel.numberOp0_idem
  · exact ColorCARStandardModel.numberOp1_idem
  · exact ColorCARStandardModel.numberOp2_idem

/-! ## Finite occupation readout

The scalar readout is the finite occupation-number convention
`q(w) = #{i | w i = true}/3`, with no claim that a basis-state/particle-label
identification has been proved here. -/

/-- Three Boolean occupation bits, one for each Furey/CAR ladder. -/
abbrev Occupation3 := Fin 3 → Bool

/-- All 8 possible occupation words as a Finset for finite enumeration. -/
def allOccupations : Finset Occupation3 :=
  Finset.univ

/-- Number of occupied Furey ladders. -/
def fureyOccupationNumber (w : Occupation3) : ℕ :=
  (if w 0 then 1 else 0) + (if w 1 then 1 else 0) + (if w 2 then 1 else 0)

/-- Scalar charge readout for an occupation word. -/
def fureyOccupationCharge (w : Occupation3) : ℚ :=
  (fureyOccupationNumber w : ℚ) / 3

/-- The finite positive minimal-ideal occupation-charge spectrum is
`{0, 1/3, 2/3, 1}`. -/
theorem fureyOccupationCharge_spectrum (w : Occupation3) :
    fureyOccupationCharge w = 0 ∨
    fureyOccupationCharge w = (1 / 3 : ℚ) ∨
    fureyOccupationCharge w = (2 / 3 : ℚ) ∨
    fureyOccupationCharge w = 1 := by
  dsimp [fureyOccupationCharge, fureyOccupationNumber]
  rcases w 0 <;> rcases w 1 <;> rcases w 2 <;> simp

/-- Bundle of the finite algebraic facts proved in this file. -/
theorem furey_charge_algebraic_spine :
    (∀ i : Fin 3, fureyNumber i * fureyNumber i = fureyNumber i) ∧
    (∀ w : Occupation3,
      fureyOccupationCharge w = 0 ∨
      fureyOccupationCharge w = (1 / 3 : ℚ) ∨
      fureyOccupationCharge w = (2 / 3 : ℚ) ∨
      fureyOccupationCharge w = 1) := by
  exact ⟨fureyNumber_idempotent, fureyOccupationCharge_spectrum⟩

end FureyCharges
