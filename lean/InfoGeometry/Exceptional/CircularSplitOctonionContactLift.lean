import InfoGeometry.Exceptional.FreudenthalGenericJacobiClosure
import InfoGeometry.Exceptional.CircularSplitOctonionFreudenthalIntertwiner
import InfoGeometry.Algebra.CircularChiralCausalConeBasis
import InfoGeometry.OperatorAlgebra.ChiralOperatorEnvelope

/-!
# Circular split-octonion operator basis inside the Freudenthal contact grading

The circular Witt/Peirce chirality `u±, σᵢ±` is internal to one Freudenthal
charge space.  It must not be identified with the contact grades `±1`.
Accordingly this file embeds the full eight-dimensional circular basis into
both contact charge lanes, with separate extreme generators `E₋` and `E₊`.

This preserves the nondegenerate symplectic pairings

  ω(u₊,u₋)=1,   ω(σᵢ⁺,σⱼ⁻)=δᵢⱼ,

so the native five-graded bracket produces the extreme Heisenberg lanes.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal.CircularSplitOctonionContactLift

open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.OperatorAlgebra

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)
variable (rootMapPlus rootMapMinus : Fin 3 → J)

/-- User-facing aliases for the circular split-octonion basis. -/
abbrev uPlus : ChiralBasis := .uPlus
abbrev uMinus : ChiralBasis := .uMinus
abbrev u1Up : ChiralBasis := .up 0
abbrev u2Up : ChiralBasis := .up 1
abbrev u3Up : ChiralBasis := .up 2
abbrev u1Down : ChiralBasis := .down 0
abbrev u2Down : ChiralBasis := .down 1
abbrev u3Down : ChiralBasis := .down 2

/-- The same eight labels in the universal associative chiral operator envelope. -/
def operatorLabel : ChiralBasis → ChiralGenerator
  | .uPlus => .pPlus
  | .uMinus => .pMinus
  | .up i => .sPlus i
  | .down i => .sMinus i

@[simp] theorem operatorLabel_uPlus : operatorLabel uPlus = .pPlus := rfl
@[simp] theorem operatorLabel_uMinus : operatorLabel uMinus = .pMinus := rfl
@[simp] theorem operatorLabel_u1Up : operatorLabel u1Up = .sPlus 0 := rfl
@[simp] theorem operatorLabel_u2Up : operatorLabel u2Up = .sPlus 1 := rfl
@[simp] theorem operatorLabel_u3Up : operatorLabel u3Up = .sPlus 2 := rfl
@[simp] theorem operatorLabel_u1Down : operatorLabel u1Down = .sMinus 0 := rfl
@[simp] theorem operatorLabel_u2Down : operatorLabel u2Down = .sMinus 1 := rfl
@[simp] theorem operatorLabel_u3Down : operatorLabel u3Down = .sMinus 2 := rfl

/-- Circular split-octonion basis vector readback in the Freudenthal charge space. -/
def chargeOfCircular : ChiralBasis → FreudenthalCharge J
  | .uPlus => embedPlusPole
  | .uMinus => embedMinusPole
  | .up i => embedPlusRoot rootMapPlus i
  | .down i => embedMinusRoot rootMapMinus i

/-- Full circular operator basis embedded in contact grade `-1`. -/
def toMinusOne (b : ChiralBasis) : FiveGradedCarrier D :=
  injChargeMinus D (chargeOfCircular rootMapPlus rootMapMinus b)

/-- Full circular operator basis embedded in contact grade `+1`. -/
def toPlusOne (b : ChiralBasis) : FiveGradedCarrier D :=
  injChargePlus D (chargeOfCircular rootMapPlus rootMapMinus b)

/-- Extreme contact pole `E₋ ∈ 𝔤₋₂`. -/
def Eminus : FiveGradedCarrier D := genEminus D 1

/-- Extreme contact pole `E₊ ∈ 𝔤₊₂`. -/
def Eplus : FiveGradedCarrier D := genEplus D 1

/-- The full contact lift has two copies of the circular 8D operator basis plus
its two extreme poles. -/
inductive ContactAtom
  | eMinus
  | minusOne (b : ChiralBasis)
  | plusOne (b : ChiralBasis)
  | ePlus
deriving DecidableEq, Fintype

/-- Contact degree of each lifted atom. -/
def contactDegree : ContactAtom → ℤ
  | .eMinus => -2
  | .minusOne _ => -1
  | .plusOne _ => 1
  | .ePlus => 2

/-- Read a contact atom in the native Freudenthal five-graded carrier. -/
def toFiveGraded : ContactAtom → FiveGradedCarrier D
  | .eMinus => Eminus D
  | .minusOne b => toMinusOne D rootMapPlus rootMapMinus b
  | .plusOne b => toPlusOne D rootMapPlus rootMapMinus b
  | .ePlus => Eplus D

@[simp] theorem toFiveGraded_eMinus :
    toFiveGraded D rootMapPlus rootMapMinus .eMinus = genEminus D 1 := rfl

@[simp] theorem toFiveGraded_ePlus :
    toFiveGraded D rootMapPlus rootMapMinus .ePlus = genEplus D 1 := rfl

@[simp] theorem toFiveGraded_minusOne (b : ChiralBasis) :
    toFiveGraded D rootMapPlus rootMapMinus (.minusOne b) =
      injChargeMinus D (chargeOfCircular rootMapPlus rootMapMinus b) := rfl

@[simp] theorem toFiveGraded_plusOne (b : ChiralBasis) :
    toFiveGraded D rootMapPlus rootMapMinus (.plusOne b) =
      injChargePlus D (chargeOfCircular rootMapPlus rootMapMinus b) := rfl

/-- The circular poles retain their canonical symplectic pairing. -/
@[simp] theorem omega_charge_poles :
    FreudenthalCharge.symplecticForm D
      (chargeOfCircular rootMapPlus rootMapMinus uPlus)
      (chargeOfCircular rootMapPlus rootMapMinus uMinus) = 1 := by
  exact omega_poles D

/-- The circular root channels retain the Kronecker symplectic pairing. -/
theorem omega_charge_roots
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    FreudenthalCharge.symplecticForm D
      (chargeOfCircular rootMapPlus rootMapMinus (.up i))
      (chargeOfCircular rootMapPlus rootMapMinus (.down j)) =
      if i = j then 1 else 0 := by
  exact omega_roots D rootMapPlus rootMapMinus h_ortho i j

/-- Heisenberg closure of the pole pair in the negative contact lane. -/
theorem minusOne_pole_pair_to_Eminus :
    fiveGradedBracket D
      (toMinusOne D rootMapPlus rootMapMinus uPlus)
      (toMinusOne D rootMapPlus rootMapMinus uMinus) =
      genEminus D 2 := by
  apply FiveGradedCarrier.ext <;>
    simp [toMinusOne, chargeOfCircular, fiveGradedBracket, genEminus,
      omega_poles]

/-- Heisenberg closure of the pole pair in the positive contact lane. -/
theorem plusOne_pole_pair_to_Eplus :
    fiveGradedBracket D
      (toPlusOne D rootMapPlus rootMapMinus uPlus)
      (toPlusOne D rootMapPlus rootMapMinus uMinus) =
      genEplus D 2 := by
  apply FiveGradedCarrier.ext <;>
    simp [toPlusOne, chargeOfCircular, fiveGradedBracket, genEplus,
      omega_poles]

/-- Root-pair Heisenberg coefficient in the negative contact lane. -/
theorem minusOne_root_pair_minus2
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    (fiveGradedBracket D
      (toMinusOne D rootMapPlus rootMapMinus (.up i))
      (toMinusOne D rootMapPlus rootMapMinus (.down j))).minus2 =
      2 * (if i = j then 1 else 0) := by
  simp [toMinusOne, chargeOfCircular, fiveGradedBracket,
    omega_roots D rootMapPlus rootMapMinus h_ortho i j]

/-- Root-pair Heisenberg coefficient in the positive contact lane. -/
theorem plusOne_root_pair_plus2
    (h_ortho : ∀ i j : Fin 3,
      D.traceBilin (rootMapPlus i) (rootMapMinus j) = if i = j then 1 else 0)
    (i j : Fin 3) :
    (fiveGradedBracket D
      (toPlusOne D rootMapPlus rootMapMinus (.up i))
      (toPlusOne D rootMapPlus rootMapMinus (.down j))).plus2 =
      2 * (if i = j then 1 else 0) := by
  simp [toPlusOne, chargeOfCircular, fiveGradedBracket,
    omega_roots D rootMapPlus rootMapMinus h_ortho i j]

/-- Circular chirality is distinct from contact degree: both chiralities occur
inside each of the two contact charge lanes. -/
theorem circular_chirality_not_contact_grading :
    contactDegree (.minusOne uPlus) = contactDegree (.minusOne uMinus) ∧
    contactDegree (.plusOne uPlus) = contactDegree (.plusOne uMinus) := by
  constructor <;> rfl

end InfoGeometry.Exceptional.Freudenthal.CircularSplitOctonionContactLift
