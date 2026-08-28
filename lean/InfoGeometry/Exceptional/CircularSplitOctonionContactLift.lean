import InfoGeometry.Exceptional.CircularSplitOctonionFreudenthalIntertwiner
import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure

/-! A small, honest contact-grade interface for the existing circular charge
intertwiner.  Circular polarization is deliberately not identified with
contact degree. -/
namespace InfoGeometry.Exceptional.Freudenthal

noncomputable section

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

inductive CircularChargeAtom
  | plusPole | minusPole
  | plusRoot (i : Fin 3) | minusRoot (i : Fin 3)
  deriving DecidableEq

def circularCharge
    (rootMapPlus rootMapMinus : Fin 3 → J) : CircularChargeAtom → FreudenthalCharge J
  | .plusPole => embedPlusPole
  | .minusPole => embedMinusPole
  | .plusRoot i => embedPlusRoot rootMapPlus i
  | .minusRoot i => embedMinusRoot rootMapMinus i

def toMinusOne
    (rootMapPlus rootMapMinus : Fin 3 → J) (a : CircularChargeAtom) :
    FiveGradedCarrier D := injChargeMinus D (circularCharge rootMapPlus rootMapMinus a)

def toPlusOne
    (rootMapPlus rootMapMinus : Fin 3 → J) (a : CircularChargeAtom) :
    FiveGradedCarrier D := injChargePlus D (circularCharge rootMapPlus rootMapMinus a)

def Eminus : FiveGradedCarrier D := genEminus D
def Eplus : FiveGradedCarrier D := genEplus D

theorem circular_polar_bracket_minus
    (rootMapPlus rootMapMinus : Fin 3 → J) :
    fiveGradedBracket D
        (toMinusOne D rootMapPlus rootMapMinus .plusPole)
      (toMinusOne D rootMapPlus rootMapMinus .minusPole) =
      genEminus D 2 := by
  dsimp [toMinusOne, circularCharge]
  rw [fiveGradedBracket_chargeMinus_chargeMinus]
  simp [genEminus, embedPlusPole, embedMinusPole,
    FreudenthalCharge.symplecticForm]

theorem circular_polar_bracket_plus
    (rootMapPlus rootMapMinus : Fin 3 → J) :
    fiveGradedBracket D
        (toPlusOne D rootMapPlus rootMapMinus .plusPole)
      (toPlusOne D rootMapPlus rootMapMinus .minusPole) =
      genEplus D 2 := by
  dsimp [toPlusOne, circularCharge]
  rw [fiveGradedBracket_chargePlus_chargePlus]
    simp [genEplus, embedPlusPole, embedMinusPole,
    FreudenthalCharge.symplecticForm]

theorem circular_root_bracket_minus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    fiveGradedBracket D
        (toMinusOne D rootMapPlus rootMapMinus (.plusRoot i))
      (toMinusOne D rootMapPlus rootMapMinus (.minusRoot j)) =
      genEminus D (2 * (if i = j then (1 : ℝ) else 0)) := by
  dsimp [toMinusOne, circularCharge]
  rw [fiveGradedBracket_chargeMinus_chargeMinus]
  rw [omega_roots D rootMapPlus rootMapMinus h_ortho]
  rfl

theorem circular_root_bracket_plus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    fiveGradedBracket D
        (toPlusOne D rootMapPlus rootMapMinus (.plusRoot i))
      (toPlusOne D rootMapPlus rootMapMinus (.minusRoot j)) =
      genEplus D (2 * (if i = j then (1 : ℝ) else 0)) := by
  dsimp [toPlusOne, circularCharge]
  rw [fiveGradedBracket_chargePlus_chargePlus]
  rw [omega_roots D rootMapPlus rootMapMinus h_ortho]
  rfl

inductive ContactAtom
  | eMinus
  | minusOne (a : CircularChargeAtom)
  | plusOne (a : CircularChargeAtom)
  | ePlus
  deriving DecidableEq

def contactDegree : ContactAtom → ℤ
  | .eMinus => -2
  | .minusOne _ => -1
  | .plusOne _ => 1
  | .ePlus => 2

theorem contactDegree_eMinus : contactDegree .eMinus = (-2 : ℤ) := rfl
theorem contactDegree_minusOne (a) : contactDegree (.minusOne a) = (-1 : ℤ) := rfl
theorem contactDegree_plusOne (a) : contactDegree (.plusOne a) = (1 : ℤ) := rfl
theorem contactDegree_ePlus : contactDegree .ePlus = (2 : ℤ) := rfl

end
end InfoGeometry.Exceptional.Freudenthal
