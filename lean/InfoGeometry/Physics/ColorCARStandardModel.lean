import InfoGeometry.Clifford.Cl55ThreeColorChiralSums

/-!
# Native colour CAR readout

The colour lanes live in the repository-owned noncommutative `Cl(5,5)`
carrier.  This module is deliberately only a finite CAR/grade readout; it
does not claim a Standard Model representation or an identification with a
matrix/tensor-product toy.
-/

noncomputable section

namespace InfoGeometry.Physics.ColorCARStandardModel

open InfoGeometry.Clifford.Clifford55

abbrev CAR3 : Type := Cl55

def carAnn0 : CAR3 := chiralPlus55 0
def carAnn1 : CAR3 := chiralPlus55 1
def carAnn2 : CAR3 := chiralPlus55 2

def carCre0 : CAR3 := chiralMinus55 0
def carCre1 : CAR3 := chiralMinus55 1
def carCre2 : CAR3 := chiralMinus55 2

def vacuum : CAR3 := 1

def numberOp0 : CAR3 := carAnn0 * carCre0
def numberOp1 : CAR3 := carAnn1 * carCre1
def numberOp2 : CAR3 := carAnn2 * carCre2

private theorem numberOp_idem (i : Fin 3) :
    (chiralPlus55 i * chiralMinus55 i) *
        (chiralPlus55 i * chiralMinus55 i) =
      chiralPlus55 i * chiralMinus55 i := by
  have hplus := chiralPlus55_sq i
  have hminus := chiralMinus55_sq i
  have hcar :
      chiralMinus55 i * chiralPlus55 i +
          chiralPlus55 i * chiralMinus55 i = 1 := by
    simpa [add_comm] using
      (chiralPlus55_minus55_anticommutator i i)
  have hswap : chiralMinus55 i * chiralPlus55 i =
      1 - chiralPlus55 i * chiralMinus55 i := by
    exact eq_sub_of_add_eq hcar
  calc
    (chiralPlus55 i * chiralMinus55 i) *
        (chiralPlus55 i * chiralMinus55 i) =
      chiralPlus55 i *
        (chiralMinus55 i * chiralPlus55 i) * chiralMinus55 i := by
          simp only [mul_assoc]
    _ = chiralPlus55 i *
        (1 - chiralPlus55 i * chiralMinus55 i) * chiralMinus55 i := by
          rw [hswap]
    _ = chiralPlus55 i * chiralMinus55 i -
        (chiralPlus55 i * chiralPlus55 i) *
          (chiralMinus55 i * chiralMinus55 i) := by
          noncomm_ring
    _ = chiralPlus55 i * chiralMinus55 i := by
          rw [hplus, hminus]
          simp

theorem numberOp0_idem : numberOp0 * numberOp0 = numberOp0 :=
  numberOp_idem 0

theorem numberOp1_idem : numberOp1 * numberOp1 = numberOp1 :=
  numberOp_idem 1

theorem numberOp2_idem : numberOp2 * numberOp2 = numberOp2 :=
  numberOp_idem 2

theorem color_car_native_closure :
    chiralPlusSum * chiralPlusSum = 0 ∧
    chiralMinusSum * chiralMinusSum = 0 ∧
    chiralMinusSum * chiralPlusSum +
        chiralPlusSum * chiralMinusSum = (3 : Cl55) ∧
    numberOp0 * numberOp0 = numberOp0 ∧
    numberOp1 * numberOp1 = numberOp1 ∧
    numberOp2 * numberOp2 = numberOp2 := by
  exact ⟨chiralPlusSum_sq, chiralMinusSum_sq,
    chiralMinusSum_plusSum_anticommutator,
    numberOp0_idem, numberOp1_idem, numberOp2_idem⟩

end InfoGeometry.Physics.ColorCARStandardModel
