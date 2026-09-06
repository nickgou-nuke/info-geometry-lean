import Mathlib
import InfoGeometry.Algebra.CircularChiralCarrierReadout
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Eight-generator circular chiral operator / Peirce bridge

This owner packages the already existing circular split-octonion generators in
the operator notation

`Eplus, u1up, u2up, u3up, Eminus, u1down, u2down, u3down`

and proves that they are exactly the native Zorn matrix units

`E11, U 0, U 1, U 2, E22, V 0, V 1, V 2`

and, through the existing canonical-vector equivalence, exactly the eight
vectors of `SplitOctonionCircularPeirceBasis.circularPeirceBasis`.

No identification with the Freudenthal five-graded generators `genEplus`,
`genEminus`, `injChargePlus`, or `injChargeMinus` is asserted here: those live
on a different carrier and require a genuine Zorn-to-Freudenthal charge map.
-/

noncomputable section

namespace InfoGeometry.Algebra.CircularChiralOperatorEightBridge

open InfoGeometry.Algebra.ZornVectorMatrix
open InfoGeometry.Algebra.CircularChiralCausalConeBasis
open InfoGeometry.Algebra.CircularChiralDerivationsFourteen
open InfoGeometry.Algebra.CircularChiralCarrierReadout
open InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.OperatorAlgebra

abbrev NativeOperator : Type := InfoGeometry.Algebra.ZornVectorMatrix ℝ

/-- Positive circular pole, operator-envelope readout of `u⁺`. -/
def Eplus : NativeOperator := chiralReadoutBasis (.pPlus)

/-- Negative circular pole, operator-envelope readout of `u⁻`. -/
def Eminus : NativeOperator := chiralReadoutBasis (.pMinus)

/-- Three positive circular null channels. -/
def u1up : NativeOperator := chiralReadoutBasis (.sPlus 0)
def u2up : NativeOperator := chiralReadoutBasis (.sPlus 1)
def u3up : NativeOperator := chiralReadoutBasis (.sPlus 2)

/-- Three negative circular null channels. -/
def u1down : NativeOperator := chiralReadoutBasis (.sMinus 0)
def u2down : NativeOperator := chiralReadoutBasis (.sMinus 1)
def u3down : NativeOperator := chiralReadoutBasis (.sMinus 2)

/-- Ordered operator frame in the same order as the native circular Peirce basis. -/
def operatorFrame : Fin 8 → NativeOperator
  | 0 => Eplus
  | 1 => u1up
  | 2 => u2up
  | 3 => u3up
  | 4 => Eminus
  | 5 => u1down
  | 6 => u2down
  | 7 => u3down
  | _ => 0

/-- The corresponding abstract eight-element chiral labels. -/
def chiralLabelFrame : Fin 8 → ChiralBasis
  | 0 => .uPlus
  | 1 => .up 0
  | 2 => .up 1
  | 3 => .up 2
  | 4 => .uMinus
  | 5 => .down 0
  | 6 => .down 1
  | 7 => .down 2
  | _ => .uPlus

/-- The corresponding operator-envelope labels. -/
def operatorLabelFrame : Fin 8 → ChiralGenerator
  | 0 => .pPlus
  | 1 => .sPlus 0
  | 2 => .sPlus 1
  | 3 => .sPlus 2
  | 4 => .pMinus
  | 5 => .sMinus 0
  | 6 => .sMinus 1
  | 7 => .sMinus 2
  | _ => .pPlus

/-- Constructor-level soldering of the abstract chiral basis to operator labels. -/
theorem label_frame_soldering (i : Fin 8) :
    chiralBasisToOperatorGenerator (chiralLabelFrame i) = operatorLabelFrame i := by
  fin_cases i <;> rfl

/-- The named operator frame is exactly the native readout of its label frame. -/
theorem operatorFrame_eq_chiralReadout (i : Fin 8) :
    operatorFrame i = chiralReadoutBasis (operatorLabelFrame i) := by
  fin_cases i <;> rfl

/-! ## Native Zorn matrix-unit readbacks -/

@[simp] theorem Eplus_eq_E11 : Eplus = E11 := by
  exact chiralReadoutBasis_pPlus_native_readout

@[simp] theorem Eminus_eq_E22 : Eminus = E22 := by
  exact chiralReadoutBasis_pMinus_native_readout

@[simp] theorem u1up_eq_U0 : u1up = U 0 := by
  exact chiralReadoutBasis_sPlus_native_readout 0

@[simp] theorem u2up_eq_U1 : u2up = U 1 := by
  exact chiralReadoutBasis_sPlus_native_readout 1

@[simp] theorem u3up_eq_U2 : u3up = U 2 := by
  exact chiralReadoutBasis_sPlus_native_readout 2

@[simp] theorem u1down_eq_V0 : u1down = V 0 := by
  exact chiralReadoutBasis_sMinus_native_readout 0

@[simp] theorem u2down_eq_V1 : u2down = V 1 := by
  exact chiralReadoutBasis_sMinus_native_readout 1

@[simp] theorem u3down_eq_V2 : u3down = V 2 := by
  exact chiralReadoutBasis_sMinus_native_readout 2

/-- Complete native multiplication-basis readback in one constant finite theorem. -/
theorem operatorFrame_native_readout (i : Fin 8) :
    operatorFrame i =
      match i with
      | 0 => E11
      | 1 => U 0
      | 2 => U 1
      | 3 => U 2
      | 4 => E22
      | 5 => V 0
      | 6 => V 1
      | 7 => V 2
      | _ => 0 := by
  fin_cases i <;> simp [operatorFrame]

/-! ## Circular Peirce readbacks -/

/-- Positive pole equals circular Peirce vector 0 after native carrier transport. -/
theorem Eplus_circularPeirce :
    Eplus = canonicalVectorEquiv (circularPeirceBasis 0) := by
  rw [Eplus_eq_E11, circularPeirceBasis_apply]
  simpa [circularFrame] using circular_scalarPlus_nativeE11.symm

/-- Positive channels are circular Peirce vectors 1,2,3. -/
theorem u1up_circularPeirce :
    u1up = canonicalVectorEquiv (circularPeirceBasis 1) := by
  rw [u1up_eq_U0, circularPeirceBasis_apply]
  simpa [circularFrame] using (circular_rootPlus_nativeU 0).symm

theorem u2up_circularPeirce :
    u2up = canonicalVectorEquiv (circularPeirceBasis 2) := by
  rw [u2up_eq_U1, circularPeirceBasis_apply]
  simpa [circularFrame] using (circular_rootPlus_nativeU 1).symm

theorem u3up_circularPeirce :
    u3up = canonicalVectorEquiv (circularPeirceBasis 3) := by
  rw [u3up_eq_U2, circularPeirceBasis_apply]
  simpa [circularFrame] using (circular_rootPlus_nativeU 2).symm

/-- Negative pole equals circular Peirce vector 4 after native carrier transport. -/
theorem Eminus_circularPeirce :
    Eminus = canonicalVectorEquiv (circularPeirceBasis 4) := by
  rw [Eminus_eq_E22, circularPeirceBasis_apply]
  simpa [circularFrame] using circular_scalarMinus_nativeE22.symm

/-- Negative channels are circular Peirce vectors 5,6,7. -/
theorem u1down_circularPeirce :
    u1down = canonicalVectorEquiv (circularPeirceBasis 5) := by
  rw [u1down_eq_V0, circularPeirceBasis_apply]
  simpa [circularFrame] using (circular_rootMinus_nativeV 0).symm

theorem u2down_circularPeirce :
    u2down = canonicalVectorEquiv (circularPeirceBasis 6) := by
  rw [u2down_eq_V1, circularPeirceBasis_apply]
  simpa [circularFrame] using (circular_rootMinus_nativeV 1).symm

theorem u3down_circularPeirce :
    u3down = canonicalVectorEquiv (circularPeirceBasis 7) := by
  rw [u3down_eq_V2, circularPeirceBasis_apply]
  simpa [circularFrame] using (circular_rootMinus_nativeV 2).symm

/-- The whole named operator frame is exactly the circular Peirce basis after
transport to the native vector-matrix carrier. -/
theorem operatorFrame_eq_circularPeirce (i : Fin 8) :
    operatorFrame i = canonicalVectorEquiv (circularPeirceBasis i) := by
  fin_cases i
  · exact Eplus_circularPeirce
  · exact u1up_circularPeirce
  · exact u2up_circularPeirce
  · exact u3up_circularPeirce
  · exact Eminus_circularPeirce
  · exact u1down_circularPeirce
  · exact u2down_circularPeirce
  · exact u3down_circularPeirce

/-- Injectivity of the named native operator frame follows from the genuine
circular Peirce basis and the carrier equivalence. -/
theorem operatorFrame_injective : Function.Injective operatorFrame := by
  intro i j hij
  have h := congrArg canonicalVectorEquiv.symm hij
  rw [operatorFrame_eq_circularPeirce i, operatorFrame_eq_circularPeirce j] at h
  exact circularPeirceBasis.injective h

/-- The eight named operators are pairwise distinct. -/
theorem operatorFrame_ne_of_ne {i j : Fin 8} (hij : i ≠ j) :
    operatorFrame i ≠ operatorFrame j := by
  intro h
  exact hij (operatorFrame_injective h)

end InfoGeometry.Algebra.CircularChiralOperatorEightBridge
