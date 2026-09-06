import InfoGeometry.OperatorAlgebra.ProjectiveCenterQuotient
import InfoGeometry.Geometry.PenroseKleinTiling
import InfoGeometry.Twistor.SplitClifford55PureSpinorOrbitGeometry

/-!
# Pinor vacuum sheets for the split `(5,5)` lane

This file keeps three objects distinct:

* the existing projective pure-spinor vacuum in `Cl(5,5)`;
* the finite signed center `{+I,-I}` already owned by
  `ProjectiveCenterQuotient`;
* the explicit Klein glide relation owned by `PenroseKleinTiling`.

The names `pinPlus` and `pinMinus` below are sheet/sign labels.  They do not
construct the topological groups `Pin⁺(5,5)` and `Pin⁻(5,5)`: the repository
currently exposes only the abstract `PinLiftWitness` interface and the finite
signed-center carrier.  This owner therefore formalizes the nearest exact
bridge without silently promoting the interface to a group classification.
-/

namespace InfoGeometry.Canonical.TwistorPin55KleinVacuumBridge

open InfoGeometry.Geometry.PenroseKlein
open InfoGeometry.OperatorAlgebra.ProjectiveCenter
open InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
open InfoGeometry.Twistor.SplitClifford55PureSpinorOrbitGeometry

/-! ## The two labelled sheets -/

/-- The two Pinor vacuum sheet labels retained by the split `(5,5)` lane. -/
inductive PinorVacuumSheet
  | pinPlus
  | pinMinus
  deriving DecidableEq, Repr

@[simp] theorem pinorVacuumSheet_cases (s : PinorVacuumSheet) :
    s = .pinPlus ∨ s = .pinMinus := by
  cases s <;> simp

/-- The nontrivial Klein glide used for the minus sheet representative. -/
def pinorKleinGlide (p : ℝ × ℝ) : ℝ × ℝ :=
  (-p.1, p.2 + 1)

@[simp] theorem pinorKleinGlide_fst (p : ℝ × ℝ) :
    (pinorKleinGlide p).1 = -p.1 := by
  rfl

@[simp] theorem pinorKleinGlide_snd (p : ℝ × ℝ) :
    (pinorKleinGlide p).2 = p.2 + 1 := by
  rfl

def pinPlusVacuumRepresentative : ℝ × ℝ := (0, 0)

def pinMinusVacuumRepresentative : ℝ × ℝ :=
  pinorKleinGlide pinPlusVacuumRepresentative

@[simp] theorem pinMinusVacuumRepresentative_value :
    pinMinusVacuumRepresentative = (0, 1) := by
  norm_num [pinMinusVacuumRepresentative, pinorKleinGlide,
    pinPlusVacuumRepresentative]

/-- The two representatives are related by the existing Klein-bottle glide. -/
theorem pinMinusVacuumRepresentative_klein_twist :
    KleinBottleRel pinPlusVacuumRepresentative pinMinusVacuumRepresentative := by
  unfold pinMinusVacuumRepresentative
  exact penrose_klein_defect_localization 0 0

def pinorVacuumRepresentative : PinorVacuumSheet → ℝ × ℝ
  | .pinPlus => pinPlusVacuumRepresentative
  | .pinMinus => pinMinusVacuumRepresentative

theorem pinorVacuumRepresentative_pinPlus :
    pinorVacuumRepresentative .pinPlus = pinPlusVacuumRepresentative := by
  rfl

theorem pinorVacuumRepresentative_pinMinus :
    pinorVacuumRepresentative .pinMinus = pinMinusVacuumRepresentative := by
  rfl

/-! ## The actual pure-pinor vacuum carrier -/

/-- The existing projective pure-spinor vacuum, now read on the pinor lane. -/
def purePinorVacuum : ProjectivePureSpinorPoint :=
  vacuumProjectivePureSpinorPoint

theorem purePinorVacuum_isPureSpinor :
    purePinorVacuum.1 ∈ ProjectivePureSpinor := by
  exact purePinorVacuum.2

theorem purePinorVacuum_eq_existing :
    purePinorVacuum = vacuumProjectivePureSpinorPoint := by
  rfl

/--
The present finite carrier has one pure-pinor vacuum representative; the
Pin⁺/Pin⁻ distinction is carried by the sheet label and Klein representative,
not by an invented second projective-spinor point.
-/
def pinorVacuumPoint (_ : PinorVacuumSheet) : ProjectivePureSpinorPoint :=
  purePinorVacuum

@[simp] theorem pinorVacuumPoint_is_pure (s : PinorVacuumSheet) :
    (pinorVacuumPoint s).1 ∈ ProjectivePureSpinor := by
  exact purePinorVacuum_isPureSpinor

@[simp] theorem pinorVacuumPoint_sheet_independent (s t : PinorVacuumSheet) :
    pinorVacuumPoint s = pinorVacuumPoint t := by
  rfl

/-! ## The existing finite signed center -/

def pinorVacuumCenter : PinorVacuumSheet → PinCenter
  | .pinPlus => 0
  | .pinMinus => 1

@[simp] theorem pinorVacuumCenter_pinPlus :
    pinorVacuumCenter .pinPlus = 0 := by
  rfl

@[simp] theorem pinorVacuumCenter_pinMinus :
    pinorVacuumCenter .pinMinus = 1 := by
  rfl

theorem pinorVacuumCenter_action_pinPlus :
    (pinorVacuumCenter .pinPlus).I_neg = (1 : Spin32Matrix) := by
  simp [pinorVacuumCenter, PinCenter.I_neg]

theorem pinorVacuumCenter_action_pinMinus :
    (pinorVacuumCenter .pinMinus).I_neg = negId := by
  simp [pinorVacuumCenter, PinCenter.I_neg]

theorem pinorVacuumCenter_action_involutive (s : PinorVacuumSheet) :
    (pinorVacuumCenter s).I_neg * (pinorVacuumCenter s).I_neg = 1 := by
  exact projective_center_involution (pinorVacuumCenter s)

theorem pinorVacuumCenter_action_central (s : PinorVacuumSheet) (A : Spin32Matrix) :
    (pinorVacuumCenter s).I_neg * A = A * (pinorVacuumCenter s).I_neg := by
  exact projective_center_commutes (pinorVacuumCenter s) A

/-! ## The exact scope of the reformulation -/

theorem pinMinus_is_klein_related_to_pinPlus :
    KleinBottleRel
      (pinorVacuumRepresentative .pinPlus)
      (pinorVacuumRepresentative .pinMinus) := by
  simpa [pinorVacuumRepresentative] using
    pinMinusVacuumRepresentative_klein_twist

theorem pinorVacuum_has_pure_spinor_readout (s : PinorVacuumSheet) :
    (pinorVacuumPoint s).1 ∈ ProjectivePureSpinor := by
  exact pinorVacuumPoint_is_pure s

end InfoGeometry.Canonical.TwistorPin55KleinVacuumBridge
