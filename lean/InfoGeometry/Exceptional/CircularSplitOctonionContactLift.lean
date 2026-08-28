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

abbrev uPlus : CircularChargeAtom := .plusPole
abbrev uMinus : CircularChargeAtom := .minusPole
abbrev u1Up : CircularChargeAtom := .plusRoot 0
abbrev u2Up : CircularChargeAtom := .plusRoot 1
abbrev u3Up : CircularChargeAtom := .plusRoot 2
abbrev u1Down : CircularChargeAtom := .minusRoot 0
abbrev u2Down : CircularChargeAtom := .minusRoot 1
abbrev u3Down : CircularChargeAtom := .minusRoot 2

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
  rw [omega_poles D]
  simp [genEplus]

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
  simp [genEminus]

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
  simp [genEplus]

theorem circular_root_diagonal_bracket_minus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i : Fin 3) :
    fiveGradedBracket D
        (toMinusOne D rootMapPlus rootMapMinus (.plusRoot i))
      (toMinusOne D rootMapPlus rootMapMinus (.minusRoot i)) =
      genEminus D 2 := by
  simpa using circular_root_bracket_minus D rootMapPlus rootMapMinus h_ortho i i

theorem circular_root_diagonal_bracket_plus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i : Fin 3) :
    fiveGradedBracket D
        (toPlusOne D rootMapPlus rootMapMinus (.plusRoot i))
      (toPlusOne D rootMapPlus rootMapMinus (.minusRoot i)) =
      genEplus D 2 := by
  simpa using circular_root_bracket_plus D rootMapPlus rootMapMinus h_ortho i i

theorem circular_root_same_chirality_bracket_minus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (i j : Fin 3) :
    fiveGradedBracket D
        (toMinusOne D rootMapPlus rootMapMinus (.plusRoot i))
      (toMinusOne D rootMapPlus rootMapMinus (.plusRoot j)) = 0 := by
  dsimp [toMinusOne, circularCharge]
  rw [fiveGradedBracket_chargeMinus_chargeMinus]
  rw [omega_roots_same_plus]
  apply FiveGradedCarrier.ext <;> simp

theorem circular_root_same_chirality_bracket_plus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (i j : Fin 3) :
    fiveGradedBracket D
        (toPlusOne D rootMapPlus rootMapMinus (.minusRoot i))
      (toPlusOne D rootMapPlus rootMapMinus (.minusRoot j)) = 0 := by
  dsimp [toPlusOne, circularCharge]
  rw [fiveGradedBracket_chargePlus_chargePlus]
  rw [omega_roots_same_minus]
  apply FiveGradedCarrier.ext <;> simp

theorem circular_pole_root_bracket_minus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (i : Fin 3) :
    fiveGradedBracket D
        (toMinusOne D rootMapPlus rootMapMinus .plusPole)
      (toMinusOne D rootMapPlus rootMapMinus (.plusRoot i)) = 0 := by
  dsimp [toMinusOne, circularCharge]
  rw [fiveGradedBracket_chargeMinus_chargeMinus]
  rw [omega_pole_root_plus]
  apply FiveGradedCarrier.ext <;> simp

theorem circular_pole_root_bracket_plus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (i : Fin 3) :
    fiveGradedBracket D
        (toPlusOne D rootMapPlus rootMapMinus .minusPole)
      (toPlusOne D rootMapPlus rootMapMinus (.minusRoot i)) = 0 := by
  dsimp [toPlusOne, circularCharge]
  rw [fiveGradedBracket_chargePlus_chargePlus]
  rw [omega_pole_root_minus]
  apply FiveGradedCarrier.ext <;> simp

theorem circular_opposite_pole_root_bracket_minus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (i : Fin 3) :
    fiveGradedBracket D
        (toMinusOne D rootMapPlus rootMapMinus .minusPole)
      (toMinusOne D rootMapPlus rootMapMinus (.plusRoot i)) = 0 := by
  dsimp [toMinusOne, circularCharge]
  rw [fiveGradedBracket_chargeMinus_chargeMinus]
  simp [FreudenthalCharge.symplecticForm, embedMinusPole, embedPlusRoot]
  apply FiveGradedCarrier.ext <;> simp

theorem circular_opposite_pole_root_bracket_plus
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (i : Fin 3) :
    fiveGradedBracket D
        (toPlusOne D rootMapPlus rootMapMinus .plusPole)
      (toPlusOne D rootMapPlus rootMapMinus (.minusRoot i)) = 0 := by
  dsimp [toPlusOne, circularCharge]
  rw [fiveGradedBracket_chargePlus_chargePlus]
  simp [FreudenthalCharge.symplecticForm, embedPlusPole, embedMinusRoot]
  apply FiveGradedCarrier.ext <;> simp

theorem circular_mixed_bracket_readback
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a b : CircularChargeAtom) :
    fiveGradedBracket D
        (toMinusOne D rootMapPlus rootMapMinus a)
      (toPlusOne D rootMapPlus rootMapMinus b) =
      ⟨0, 0,
        mixedSymplecticBracket D
          (circularCharge rootMapPlus rootMapMinus a)
          (circularCharge rootMapPlus rootMapMinus b),
        FreudenthalCharge.symplecticForm D
          (circularCharge rootMapPlus rootMapMinus a)
          (circularCharge rootMapPlus rootMapMinus b),
        0, 0⟩ := by
  exact fiveGradedBracket_chargeMinus_chargePlus D
    (circularCharge rootMapPlus rootMapMinus a)
    (circularCharge rootMapPlus rootMapMinus b)

theorem circular_root_incidence
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    FreudenthalCharge.symplecticForm D
        (circularCharge rootMapPlus rootMapMinus (.plusRoot i))
        (circularCharge rootMapPlus rootMapMinus (.minusRoot j)) =
        (if i = j then 1 else 0) ∧
      FreudenthalCharge.symplecticForm D
        (circularCharge rootMapPlus rootMapMinus (.plusRoot i))
        (circularCharge rootMapPlus rootMapMinus (.plusRoot j)) = 0 ∧
      FreudenthalCharge.symplecticForm D
        (circularCharge rootMapPlus rootMapMinus (.minusRoot i))
        (circularCharge rootMapPlus rootMapMinus (.minusRoot j)) = 0 := by
  simp only [circularCharge]
  exact ⟨omega_roots D rootMapPlus rootMapMinus h_ortho i j,
    omega_roots_same_plus D rootMapPlus i j,
    omega_roots_same_minus D rootMapMinus i j⟩

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

theorem circular_chirality_not_contact_grading
    (a : CircularChargeAtom) :
    contactDegree (.minusOne a) = (-1 : ℤ) ∧
      contactDegree (.plusOne a) = (1 : ℤ) := by
  exact ⟨rfl, rfl⟩

end
end InfoGeometry.Exceptional.Freudenthal
