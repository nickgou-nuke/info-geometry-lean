import InfoGeometry.Clifford.Cl55ThreeColorChiralSums

/-!
# Native three-colour CAR surface

This owner uses the existing noncommutative `Cl(5,5)` carrier.  The former
matrix/tensor-product file was only a finite readout and is intentionally not
reintroduced here.  The three colour lanes are the native grade `+1`/`-1`
generators already owned by `Cl55ThreeColorChiralGenerators`.
-/

noncomputable section

namespace ColorCARStandardModel

open InfoGeometry.Clifford.Clifford55

abbrev CAR3 : Type := Cl55

def carAnn0 : CAR3 := chiralPlus55 0
def carAnn1 : CAR3 := chiralPlus55 1
def carAnn2 : CAR3 := chiralPlus55 2

def carCre0 : CAR3 := chiralMinus55 0
def carCre1 : CAR3 := chiralMinus55 1
def carCre2 : CAR3 := chiralMinus55 2

def vacuum : CAR3 := 1

def fureyGeneration : Submodule ℝ CAR3 :=
  Submodule.span ℝ {
    vacuum,
    carCre0, carCre1, carCre2,
    carCre0 * carCre1, carCre1 * carCre2, carCre0 * carCre2,
    carCre0 * carCre1 * carCre2
  }

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

theorem numberOp0_idem : numberOp0 * numberOp0 = numberOp0 := by
  exact numberOp_idem 0

theorem numberOp1_idem : numberOp1 * numberOp1 = numberOp1 := by
  exact numberOp_idem 1

theorem numberOp2_idem : numberOp2 * numberOp2 = numberOp2 := by
  exact numberOp_idem 2

def N_plus : Cl55 := chiralPlus55 0 * chiralMinus55 0
def N_minus : Cl55 := chiralMinus55 0 * chiralPlus55 0

theorem N_plus_add_N_minus : N_plus + N_minus = (1 : Cl55) := by
  simpa [N_plus, N_minus] using
    (chiralPlus55_minus55_anticommutator (0 : Fin 3) 0)

theorem N_plus_mul_N_minus : N_plus * N_minus = 0 := by
  have hp := chiralPlus55_sq (0 : Fin 3)
  have hm := chiralMinus55_sq (0 : Fin 3)
  change (chiralPlus55 0 * chiralMinus55 0) *
      (chiralMinus55 0 * chiralPlus55 0) = 0
  rw [show (chiralPlus55 0 * chiralMinus55 0) *
      (chiralMinus55 0 * chiralPlus55 0) =
      chiralPlus55 0 * (chiralMinus55 0 * chiralMinus55 0) *
        chiralPlus55 0 by noncomm_ring]
  rw [hm]
  simp

theorem N_minus_mul_N_plus : N_minus * N_plus = 0 := by
  have hp := chiralPlus55_sq (0 : Fin 3)
  have hm := chiralMinus55_sq (0 : Fin 3)
  change (chiralMinus55 0 * chiralPlus55 0) *
      (chiralPlus55 0 * chiralMinus55 0) = 0
  rw [show (chiralMinus55 0 * chiralPlus55 0) *
      (chiralPlus55 0 * chiralMinus55 0) =
      chiralMinus55 0 * (chiralPlus55 0 * chiralPlus55 0) *
        chiralMinus55 0 by noncomm_ring]
  rw [hp]
  simp

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

end ColorCARStandardModel
