import Mathlib.Tactic
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
import InfoGeometry.Canonical.SuperchargeCARCCRBridge
import InfoGeometry.Canonical.WeylNormalizedCARCCRBridge
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge

Theorem-safe bridge between:

* binary Cantor words as path addresses;
* tilt/switch Clifford operators on a discrete code;
* Clifford generator readout;
* canonical CAR/CCR channels on the doubled Fock lane.

This file does not assert any new analytic limit, any new infinite tensor
product theorem, or any RH-level convergence claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.TypeIIIModularCantorSystem
open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.WeylNormalizedCARCCRBridge

/-- Finite binary Cantor words are the repo-owned path addresses. -/
abbrev BinaryWord := TypeIIIModularCantorSystem.BinaryWord

/-- Depth of a binary path code. -/
@[rep_depth operator]
def wordDepth (w : BinaryWord) : ℕ :=
  w.length

/-- A single binary refinement step increases depth by one. -/
@[rep_depth operator]
theorem binaryWord_child_length (w : BinaryWord) (b : Bool) :
    wordDepth (BinaryWord.child w b) = wordDepth w + 1 := by
  simp [wordDepth, BinaryWord.child]

/-- Every word lies in its own closed Cantor cylinder. -/
@[rep_depth operator]
theorem binaryWord_mem_closedCylinder_self (w : BinaryWord) :
    w ∈ BinaryWord.closedCylinder w := by
  simpa using (BinaryWord.mem_closedCylinder_self w)

/-- The binary Cantor cylinder splits into root, false child, and true child. -/
@[rep_depth operator]
theorem binaryWord_closedCylinder_split (w : BinaryWord) :
    BinaryWord.closedCylinder w =
      ({w} : Set BinaryWord)
        ∪ BinaryWord.closedCylinder (BinaryWord.child w false)
        ∪ BinaryWord.closedCylinder (BinaryWord.child w true) := by
  simpa using (BinaryWord.closedCylinder_split w)

/--
Binary readout of a tilt/switch system at a given Cantor address.

The bit `false` selects the tilt operator; the bit `true` selects the switch
operator.  The word length is the scale parameter.
-/
@[rep_depth operator]
structure BinaryWordTiltReadout (Op : Type*) [Ring Op] where
  tiltSwitch : TiltSwitchSystem Op
  word : BinaryWord

namespace BinaryWordTiltReadout

variable {Op : Type*} [Ring Op]
variable (P : BinaryWordTiltReadout Op)

/-- Scale readout of the binary code. -/
@[rep_depth operator]
def depth : ℕ :=
  P.word.length

/-- Bit readout at the current scale. -/
@[rep_depth operator]
def bitOperator : Bool → Op :=
  fun b => if b then P.tiltSwitch.S P.word.length else P.tiltSwitch.T P.word.length

@[simp] theorem bitOperator_false :
    P.bitOperator false = P.tiltSwitch.T P.word.length := rfl

@[simp] theorem bitOperator_true :
    P.bitOperator true = P.tiltSwitch.S P.word.length := rfl

/-- The false-bit operator squares to one. -/
@[rep_depth operator]
theorem bitOperator_false_sq :
    P.bitOperator false * P.bitOperator false = 1 := by
  simp [bitOperator, TiltSwitchSystem.local_tilt_sq]

/-- The true-bit operator squares to one. -/
@[rep_depth operator]
theorem bitOperator_true_sq :
    P.bitOperator true * P.bitOperator true = 1 := by
  simp [bitOperator, TiltSwitchSystem.local_switch_sq]

/-- The false/true bit operators anticommute at the same address. -/
@[rep_depth operator]
theorem bitOperator_anticomm :
    P.bitOperator false * P.bitOperator true + P.bitOperator true * P.bitOperator false = 0 := by
  simp [bitOperator, TiltSwitchSystem.local_tilt_switch_anticomm]

end BinaryWordTiltReadout

/-- Re-export of the Clifford generator square law. -/
@[rep_depth operator]
theorem cantorClifford_generator_sq
    {Op : Type*} [Ring Op]
    (R : CantorCliffordRepresentation Op) (i : ℕ) :
    R.gamma i * R.gamma i = 1 :=
  R.generator_sq i

/-- Re-export of the Clifford generator anticommutation law. -/
@[rep_depth operator]
theorem cantorClifford_generator_anticomm
    {Op : Type*} [Ring Op]
    (R : CantorCliffordRepresentation Op) {i j : ℕ} (hij : i ≠ j) :
    R.gamma i * R.gamma j + R.gamma j * R.gamma i = 0 := by
  simpa using (R.generator_anticomm (i := i) (j := j) hij)

/-- Re-export of the canonical primitive CAR channel. -/
@[rep_depth krein]
theorem canonicalCAR_channel
    {E : Type 0}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    CARBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = 0 :=
  parity_modular_supercharge_car_zero (E := E)

/-- Re-export of the canonical primitive CCR channel. -/
@[rep_depth krein]
theorem canonicalCCR_channel
    {E : Type 0}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    CCRBracket (E := E)
        (paritySuperchargeOp (E := E))
        (modularSuperchargeOp (E := E))
      = (2 : ℝ) • cptSuperchargeOp (E := E) :=
  parity_modular_supercharge_ccrBracket_eq_two_cpt (E := E)

/-- Re-export of the concrete split-`Cl(1,1)` CAR pair. -/
@[rep_depth krein]
theorem concreteSplitCl11CARPair
    {E : Type 0}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCARPair (E := E)
      (concreteCARAnnihilation (E := E))
      (concreteCARCreation (E := E)) :=
  concrete_car_pair

/-- Re-export of the concrete mixed split-`Cl(1,1)` CAR identity. -/
@[rep_depth krein]
theorem concreteSplitCl11CARMixed
    {E : Type 0}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    CARBracket (E := E)
        (concreteCARAnnihilation (E := E))
        (concreteCARCreation (E := E))
      = ContinuousLinearMap.id ℝ (DoubledSpace E) :=
  concrete_car_minus_plus

/-- Re-export of the Weyl-normalized concrete split-`Cl(1,1)` CAR pair. -/
@[rep_depth krein]
theorem concreteSplitCl11NormalizedCARPair
    {E : Type 0}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsCARPair (E := E)
      (concreteCl11ScaledCARPair (E := E)).normalizedAnnihilation
      (concreteCl11ScaledCARPair (E := E)).normalizedCreation :=
  concreteCl11ScaledCARPair_normalized_isCARPair

/-- The combined finite owner target is supplied by the repo-owned theorems. -/
theorem cantorBinaryTiltCARCCROwnerTarget :
    (∀ w : BinaryWord,
        wordDepth (BinaryWord.child w false) = wordDepth w + 1)
      ∧
      (∀ {Op : Type*} [Ring Op] (P : BinaryWordTiltReadout Op),
        P.bitOperator false * P.bitOperator false = 1
          ∧ P.bitOperator true * P.bitOperator true = 1
          ∧ P.bitOperator false * P.bitOperator true
              + P.bitOperator true * P.bitOperator false = 0)
      ∧
    (∀ {Op : Type*} [Ring Op] (R : CantorCliffordRepresentation Op),
        (∀ i : ℕ, R.gamma i * R.gamma i = 1)
          ∧
        (∀ {i j : ℕ}, i ≠ j → R.gamma i * R.gamma j + R.gamma j * R.gamma i = 0))
      ∧
      (∀ {E : Type 0}
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
        CARBracket (E := E)
            (paritySuperchargeOp (E := E))
            (modularSuperchargeOp (E := E)) = 0
          ∧
        CCRBracket (E := E)
            (paritySuperchargeOp (E := E))
            (modularSuperchargeOp (E := E))
          = (2 : ℝ) • cptSuperchargeOp (E := E)
          ∧
        IsCARPair (E := E)
          (concreteCARAnnihilation (E := E))
          (concreteCARCreation (E := E))
          ∧
        IsCARPair (E := E)
          (concreteCl11ScaledCARPair (E := E)).normalizedAnnihilation
          (concreteCl11ScaledCARPair (E := E)).normalizedCreation) := by
  constructor
  · intro w
    simpa [wordDepth] using (binaryWord_child_length w false)
  · constructor
    · intro Op _ P
      refine ⟨P.bitOperator_false_sq, ?_, P.bitOperator_anticomm⟩
      simpa using P.bitOperator_true_sq
    · constructor
      · intro Op _ R
        constructor
        · intro i
          exact R.generator_sq i
        · intro i j hij
          simpa using (R.generator_anticomm (i := i) (j := j) hij)
      · intro E _ _ _
        refine ⟨canonicalCAR_channel (E := E), ?_, ?_, ?_⟩
        · exact canonicalCCR_channel (E := E)
        · exact concreteSplitCl11CARPair (E := E)
        · exact concreteSplitCl11NormalizedCARPair (E := E)

end InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
