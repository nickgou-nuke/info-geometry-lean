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

def circularFlip : CircularChargeAtom → CircularChargeAtom
  | .plusPole => .minusPole
  | .minusPole => .plusPole
  | .plusRoot i => .minusRoot i
  | .minusRoot i => .plusRoot i

def contactFlip : ContactAtom → ContactAtom
  | .eMinus => .ePlus
  | .minusOne a => .plusOne a
  | .plusOne a => .minusOne a
  | .ePlus => .eMinus

def circularFlipContact : ContactAtom → ContactAtom
  | .eMinus => .eMinus
  | .minusOne a => .minusOne (circularFlip a)
  | .plusOne a => .plusOne (circularFlip a)
  | .ePlus => .ePlus

def peirceFlip : ContactAtom → ContactAtom := circularFlipContact

theorem circularFlip_involutive (a : CircularChargeAtom) :
    circularFlip (circularFlip a) = a := by
  cases a <;> rfl

theorem contactFlip_involutive (a : ContactAtom) :
    contactFlip (contactFlip a) = a := by
  cases a <;> rfl

theorem circularFlipContact_involutive (a : ContactAtom) :
    circularFlipContact (circularFlipContact a) = a := by
  cases a <;> simp [circularFlipContact, circularFlip_involutive]

theorem peirceFlip_involutive (a : ContactAtom) :
    peirceFlip (peirceFlip a) = a := by
  exact circularFlipContact_involutive a

theorem contactFlip_circularFlipContact_commute (a : ContactAtom) :
    contactFlip (circularFlipContact a) =
      circularFlipContact (contactFlip a) := by
  cases a <;> rfl

theorem contactFlip_peirceFlip_commute (a : ContactAtom) :
    contactFlip (peirceFlip a) = peirceFlip (contactFlip a) := by
  exact contactFlip_circularFlipContact_commute a

theorem contactFlip_comp_peirceFlip_eq_peirceFlip_comp_contactFlip :
    contactFlip ∘ peirceFlip = peirceFlip ∘ contactFlip := by
  funext a
  exact contactFlip_peirceFlip_commute a

def simultaneousFlip (a : ContactAtom) : ContactAtom :=
  contactFlip (circularFlipContact a)

theorem simultaneousFlip_eq_peirceFlip_contactFlip (a : ContactAtom) :
    simultaneousFlip a = peirceFlip (contactFlip a) := by
  exact contactFlip_peirceFlip_commute a

theorem simultaneousFlip_involutive (a : ContactAtom) :
    simultaneousFlip (simultaneousFlip a) = a := by
  rw [simultaneousFlip, simultaneousFlip,
    contactFlip_circularFlipContact_commute]
  simp [circularFlipContact_involutive, contactFlip_involutive]

theorem contactDegree_contactFlip (a : ContactAtom) :
    contactDegree (contactFlip a) = -contactDegree a := by
  cases a <;> rfl

theorem contactDegree_circularFlipContact (a : ContactAtom) :
    contactDegree (circularFlipContact a) = contactDegree a := by
  cases a <;> rfl

theorem contactDegree_simultaneousFlip (a : ContactAtom) :
    contactDegree (simultaneousFlip a) = -contactDegree a := by
  unfold simultaneousFlip
  rw [contactDegree_contactFlip, contactDegree_circularFlipContact]

def contactGradeFlipCarrier (u : FiveGradedCarrier D) : FiveGradedCarrier D :=
  ⟨u.plus2, u.plus1, u.zero_symp, u.zero_scale, u.minus1, u.minus2⟩

theorem contactGradeFlipCarrier_add
    (u v : FiveGradedCarrier D) :
    contactGradeFlipCarrier D (u + v) =
      contactGradeFlipCarrier D u + contactGradeFlipCarrier D v := by
  apply FiveGradedCarrier.ext <;> rfl

theorem contactGradeFlipCarrier_neg (u : FiveGradedCarrier D) :
    contactGradeFlipCarrier D (-u) =
      -contactGradeFlipCarrier D u := by
  apply FiveGradedCarrier.ext <;> rfl

theorem contactGradeFlipCarrier_involutive (u : FiveGradedCarrier D) :
    contactGradeFlipCarrier D (contactGradeFlipCarrier D u) = u := by
  apply FiveGradedCarrier.ext <;> rfl

def contactGradeFlipCarrierAddEquiv :
    FiveGradedCarrier D ≃+ FiveGradedCarrier D where
  toFun := contactGradeFlipCarrier D
  invFun := contactGradeFlipCarrier D
  left_inv := contactGradeFlipCarrier_involutive D
  right_inv := contactGradeFlipCarrier_involutive D
  map_add' := contactGradeFlipCarrier_add D

@[simp] theorem contactGradeFlipCarrierAddEquiv_apply
    (u : FiveGradedCarrier D) :
    contactGradeFlipCarrierAddEquiv D u = contactGradeFlipCarrier D u := rfl

@[simp] theorem contactGradeFlipCarrierAddEquiv_symm_apply
    (u : FiveGradedCarrier D) :
    (contactGradeFlipCarrierAddEquiv D).symm u =
      contactGradeFlipCarrier D u := rfl

theorem contactGradeFlipCarrier_toMinusOne
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a : CircularChargeAtom) :
    contactGradeFlipCarrier D
        (toMinusOne D rootMapPlus rootMapMinus a) =
      toPlusOne D rootMapPlus rootMapMinus a := by
  apply FiveGradedCarrier.ext <;> rfl

theorem contactGradeFlipCarrier_toPlusOne
    (rootMapPlus rootMapMinus : Fin 3 → J)
    (a : CircularChargeAtom) :
    contactGradeFlipCarrier D
        (toPlusOne D rootMapPlus rootMapMinus a) =
      toMinusOne D rootMapPlus rootMapMinus a := by
  apply FiveGradedCarrier.ext <;> rfl

theorem contactGradeFlipCarrier_zero_symp (u : FiveGradedCarrier D) :
    (contactGradeFlipCarrier D u).zero_symp = u.zero_symp := rfl

theorem contactGradeFlipCarrier_zero_scale (u : FiveGradedCarrier D) :
    (contactGradeFlipCarrier D u).zero_scale = u.zero_scale := rfl

theorem contactGradeFlipCarrier_genEminus (c : ℝ) :
    contactGradeFlipCarrier D (genEminus D c) = genEplus D c := by
  apply FiveGradedCarrier.ext <;> rfl

theorem contactGradeFlipCarrier_genEplus (c : ℝ) :
    contactGradeFlipCarrier D (genEplus D c) = genEminus D c := by
  apply FiveGradedCarrier.ext <;> rfl

theorem contactGradeFlipCarrier_extreme_bracket
    (a b : ℝ) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (genEminus D a) (genEminus D b)) =
      fiveGradedBracket D (genEplus D a) (genEplus D b) := by
  apply FiveGradedCarrier.ext
  all_goals simp [contactGradeFlipCarrier, fiveGradedBracket, genEminus, genEplus]

theorem contactGradeFlipCarrier_extreme_bracket_dual
    (a b : ℝ) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (genEplus D a) (genEplus D b)) =
      fiveGradedBracket D (genEminus D a) (genEminus D b) := by
  apply FiveGradedCarrier.ext <;>
    simp [contactGradeFlipCarrier, fiveGradedBracket, genEminus, genEplus]

theorem contactGradeFlipCarrier_extreme_mixed_bracket
    (a b : ℝ) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (genEminus D a) (genEplus D b)) =
      -(fiveGradedBracket D (genEplus D a) (genEminus D b)) := by
  apply FiveGradedCarrier.ext <;>
    simp [contactGradeFlipCarrier, fiveGradedBracket, genEminus, genEplus]
  all_goals ring

theorem contactGradeFlipCarrier_extreme_charge_intertwining
    (a : ℝ) (x : FreudenthalCharge J) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (genEminus D a) (injChargePlus D x)) =
      -(fiveGradedBracket D (genEplus D a) (injChargeMinus D x)) := by
  apply FiveGradedCarrier.ext <;>
    simp [contactGradeFlipCarrier, fiveGradedBracket, genEminus, genEplus,
      injChargeMinus, injChargePlus]

theorem contactGradeFlipCarrier_extreme_charge_intertwining_dual
    (a : ℝ) (x : FreudenthalCharge J) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (genEplus D a) (injChargeMinus D x)) =
      -(fiveGradedBracket D (genEminus D a) (injChargePlus D x)) := by
  apply FiveGradedCarrier.ext <;>
    simp [contactGradeFlipCarrier, fiveGradedBracket, genEminus, genEplus,
      injChargeMinus, injChargePlus]

theorem contactGradeFlipCarrier_zeroSymp_charge
    (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (injSympZero D T) (injChargeMinus D x)) =
      fiveGradedBracket D (injSympZero D T) (injChargePlus D x) := by
  apply FiveGradedCarrier.ext <;>
    simp [contactGradeFlipCarrier, fiveGradedBracket, injSympZero,
      injChargeMinus, injChargePlus]

theorem contactGradeFlipCarrier_zeroSymp_bracket
    (T U : SymplecticTKKZero D) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (injSympZero D T) (injSympZero D U)) =
      fiveGradedBracket D (injSympZero D T) (injSympZero D U) := by
  apply FiveGradedCarrier.ext <;>
    simp [contactGradeFlipCarrier, fiveGradedBracket, injSympZero]

theorem contactGradeFlipCarrier_scale_zeroSymp_bracket
    (c : ℝ) (T : SymplecticTKKZero D) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (genHscale D c) (injSympZero D T)) =
      fiveGradedBracket D (genHscale D c) (injSympZero D T) := by
  apply FiveGradedCarrier.ext <;>
    simp [contactGradeFlipCarrier, fiveGradedBracket, genHscale,
      injSympZero]

theorem contactGradeFlipCarrier_charge_zeroSymp_bracket
    (T : SymplecticTKKZero D) (x : FreudenthalCharge J) :
    contactGradeFlipCarrier D
        (fiveGradedBracket D (injChargeMinus D x) (injSympZero D T)) =
      fiveGradedBracket D (injChargePlus D x) (injSympZero D T) := by
  apply FiveGradedCarrier.ext <;>
    simp [contactGradeFlipCarrier, fiveGradedBracket, injSympZero,
      injChargeMinus, injChargePlus]

theorem contactGradeFlipCarrier_genHscale (c : ℝ) :
    contactGradeFlipCarrier D (genHscale D c) = genHscale D c := by
  apply FiveGradedCarrier.ext <;> rfl

theorem contactGradeFlipCarrier_injSympZero
    (T : SymplecticTKKZero D) :
    contactGradeFlipCarrier D (injSympZero D T) = injSympZero D T := by
  apply FiveGradedCarrier.ext <;> rfl

theorem circular_chirality_not_contact_grading
    (a : CircularChargeAtom) :
    contactDegree (.minusOne a) = (-1 : ℤ) ∧
      contactDegree (.plusOne a) = (1 : ℤ) := by
  exact ⟨rfl, rfl⟩

end
end InfoGeometry.Exceptional.Freudenthal
