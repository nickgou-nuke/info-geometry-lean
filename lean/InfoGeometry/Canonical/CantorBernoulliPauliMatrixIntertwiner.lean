import Mathlib.Tactic
import InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
import InfoGeometry.Physics.ChiralPoincareSouriauBridge
import InfoGeometry.Physics.ChiralFourVectorOperatorSynthesis
import InfoGeometry.Physics.LorentzChiralCuntzBridge

/-!
# Finite Pauli/Cuntz matrix action on the one-particle Cantor carrier

This owner closes the finite representation edge behind the one-particle
Spin--Cantor map.  `Matrix.toLin'` acts on the two-dimensional spinor carrier;
the same matrix acts on the two branch vectors through the concrete Cuntz
matrix units.  No four-translation or infinite C*-completion is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner

open Matrix
open ContinuousLinearMap
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Physics.ChiralFourVectorOperatorSynthesis

abbrev SpinorSpace := SpinorCantorL2HilbertIntertwinerBridge.SpinorSpace
abbrev BoundedL2Operator :=
  InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization.BoundedL2Operator

def boolOfFin2 : Fin 2 → Bool
  | 0 => false
  | 1 => true

@[simp] theorem boolOfFin2_zero : boolOfFin2 0 = false := rfl
@[simp] theorem boolOfFin2_one : boolOfFin2 1 = true := rfl

def singletonMatrixUnit (i j : Fin 2) : BoundedL2Operator :=
  operatorMatrixUnit [boolOfFin2 i] [boolOfFin2 j]

def pauliCuntzMatrixRepresentation (A : Matrix (Fin 2) (Fin 2) ℂ) :
    BoundedL2Operator :=
  ∑ i : Fin 2, ∑ j : Fin 2, A i j • singletonMatrixUnit i j

private theorem singletonMatrixUnit_apply_branchVector
    (b c d : Bool) :
    operatorMatrixUnit [b] [c] (branchVector d) =
      if c = d then branchVector b else 0 := by
  have hcomp (b c : Bool) :
      operatorWordDag [b] (operatorWord [c] vacuumL2) =
        if b = c then vacuumL2 else 0 := by
    by_cases h : b = c
    · subst c
      simpa using ContinuousLinearMap.ext_iff.mp
        (operatorWordDag_comp_operatorWord [b]) vacuumL2
    · have hne : [b] ≠ [c] := by simpa using h
      have hz := ContinuousLinearMap.ext_iff.mp
        (operatorWordDag_comp_operatorWord_of_length_eq
          (u := [b]) (v := [c]) (by simp)
          hne) vacuumL2
      rw [if_neg h]
      exact hz
  dsimp [operatorMatrixUnit, branchVector]
  change operatorWord [b]
      (operatorWordDag [c]
        (normalizedPrependBitLpContinuousLinearMap d vacuumL2)) = _
  have hword : operatorWord [d] vacuumL2 =
      normalizedPrependBitLpContinuousLinearMap d vacuumL2 := by
    cases d <;> rfl
  rw [← hword]
  rw [hcomp]
  fin_cases b <;> cases c <;> cases d <;>
    simp [operatorWord, branchOperator, branchVector, vLeft, vRight]

theorem pauliCuntzMatrixRepresentation_basis
    (A : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 2) :
    pauliCuntzMatrixRepresentation A
        (spinorToCantorL2 (spinorBasis k)) =
      spinorToCantorL2 (Matrix.toEuclideanLin A (spinorBasis k)) := by
  classical
  fin_cases k
  · change pauliCuntzMatrixRepresentation A (spinorToCantorL2 (spinorBasis 0)) =
      spinorToCantorL2 (Matrix.toEuclideanLin A (spinorBasis 0))
    rw [spinorToCantorL2_basis_0]
    change (∑ i : Fin 2, ∑ j : Fin 2,
      A i j • singletonMatrixUnit i j (branchVector false)) = _
    simp only [Fin.sum_univ_two]
    simp only [singletonMatrixUnit]
    dsimp [boolOfFin2]
    have h00 := singletonMatrixUnit_apply_branchVector false false false
    have h01 := singletonMatrixUnit_apply_branchVector false true false
    have h10 := singletonMatrixUnit_apply_branchVector true false false
    have h11 := singletonMatrixUnit_apply_branchVector true true false
    rw [h00, h01, h10, h11]
    simp [Matrix.toEuclideanLin, spinorToCantorL2, spinorBasis, boolOfFin2]
  · change pauliCuntzMatrixRepresentation A (spinorToCantorL2 (spinorBasis 1)) =
      spinorToCantorL2 (Matrix.toEuclideanLin A (spinorBasis 1))
    rw [spinorToCantorL2_basis_1]
    change (∑ i : Fin 2, ∑ j : Fin 2,
      A i j • singletonMatrixUnit i j (branchVector true)) = _
    simp only [Fin.sum_univ_two]
    simp only [singletonMatrixUnit]
    dsimp [boolOfFin2]
    have h00 := singletonMatrixUnit_apply_branchVector false false true
    have h01 := singletonMatrixUnit_apply_branchVector false true true
    have h10 := singletonMatrixUnit_apply_branchVector true false true
    have h11 := singletonMatrixUnit_apply_branchVector true true true
    rw [h00, h01, h10, h11]
    simp [Matrix.toEuclideanLin, spinorToCantorL2, spinorBasis, boolOfFin2]

theorem pauliCuntzMatrixRepresentation_intertwines
    (A : Matrix (Fin 2) (Fin 2) ℂ) (x : SpinorSpace) :
    pauliCuntzMatrixRepresentation A (spinorToCantorL2 x) =
      spinorToCantorL2 (Matrix.toEuclideanLin A x) := by
  have hx : x = ∑ k : Fin 2, (x.ofLp k) • spinorBasis k := by
    ext k
    fin_cases k <;> simp [spinorBasis]
  rw [hx]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pauliCuntzMatrixRepresentation_basis]

/-! ## Pauli-soldered momentum specialization -/

open InfoGeometry.Physics.ChiralPoincareSouriauBridge

/-- The concrete Cantor action of a Pauli-soldered four-momentum matrix on the
first-level branch sector.  This is a bispinor/matrix action, not yet a family
of four translation generators on the full Cantor `L²` carrier. -/
def pauliCuntzMomentumRepresentation (P : FourMomentum) : BoundedL2Operator :=
  pauliCuntzMatrixRepresentation (pauliMomentum P)

theorem pauliCuntzMomentumRepresentation_intertwines
    (P : FourMomentum) (x : SpinorSpace) :
    pauliCuntzMomentumRepresentation P (spinorToCantorL2 x) =
      spinorToCantorL2 (Matrix.toEuclideanLin (pauliMomentum P) x) := by
  exact pauliCuntzMatrixRepresentation_intertwines (pauliMomentum P) x

/-- The soldered spin-connection matrix acts on the Cantor branch carrier by
    the same Pauli/Cuntz operator as the canonical four-momentum readout. -/
theorem solderedPauliCuntzRepresentation_intertwines
    (P : FourMomentum) (x : SpinorSpace) :
    pauliCuntzMatrixRepresentation
        (InfoGeometry.Physics.SolderingSpinConnectionBogoliubov.solder
          P.E P.px P.py P.pz)
        (spinorToCantorL2 x) =
      spinorToCantorL2 (Matrix.toEuclideanLin (pauliMomentum P) x) := by
  rw [soldering_eq_pauliMomentum P]
  exact pauliCuntzMatrixRepresentation_intertwines (pauliMomentum P) x

/-- Finite Lorentz covariance of the soldered Cantor action: the induced
    four-vector action agrees with chiral conjugation after transport. -/
theorem pauliCuntzMomentumRepresentation_lorentz_intertwines
    (g : InfoGeometry.Physics.LorentzChiralCuntzBridge.SL2C)
    (P : FourMomentum) (x : SpinorSpace) :
    pauliCuntzMomentumRepresentation
        (InfoGeometry.Physics.LorentzChiralCuntzBridge.spinLorentzAction g P)
        (spinorToCantorL2 x) =
      spinorToCantorL2
        (Matrix.toEuclideanLin
          (InfoGeometry.Physics.LorentzChiralCuntzBridge.chiralConjAct g
            (pauliMomentum P)) x) := by
  calc
    pauliCuntzMomentumRepresentation
        (InfoGeometry.Physics.LorentzChiralCuntzBridge.spinLorentzAction g P)
        (spinorToCantorL2 x) =
        spinorToCantorL2
          (Matrix.toEuclideanLin
            (pauliMomentum
              (InfoGeometry.Physics.LorentzChiralCuntzBridge.spinLorentzAction
                g P)) x) :=
      pauliCuntzMomentumRepresentation_intertwines
        (InfoGeometry.Physics.LorentzChiralCuntzBridge.spinLorentzAction g P) x
    _ = spinorToCantorL2
        (Matrix.toEuclideanLin
          (InfoGeometry.Physics.LorentzChiralCuntzBridge.chiralConjAct g
            (pauliMomentum P)) x) := by
      rw [InfoGeometry.Physics.LorentzChiralCuntzBridge.spinLorentzAction,
        InfoGeometry.Physics.LorentzChiralCuntzBridge.pauliMomentum_fourMomentumOfMatrix]

/-- The Cantor matrix action of the momentum extracted from a chiral
    supercharge anticommutator.  This packages the existing finite
    soldering theorem without claiming four independent translation
    generators on the full Cantor carrier. -/
def pauliCuntzSuperchargeMomentumRepresentation
    (S : ChiralSUSYMomentum) : BoundedL2Operator :=
  pauliCuntzMomentumRepresentation S.P

theorem pauliCuntzSuperchargeMomentumRepresentation_intertwines
    (S : ChiralSUSYMomentum)
    (x : SpinorSpace) :
    pauliCuntzSuperchargeMomentumRepresentation S (spinorToCantorL2 x) =
      spinorToCantorL2
        (Matrix.toEuclideanLin (momentumSpinorFromSupercharges S) x) := by
  calc
    pauliCuntzSuperchargeMomentumRepresentation S (spinorToCantorL2 x) =
        spinorToCantorL2 (Matrix.toEuclideanLin (pauliMomentum S.P) x) := by
      exact pauliCuntzMomentumRepresentation_intertwines S.P x
    _ = spinorToCantorL2
        (Matrix.toEuclideanLin (momentumSpinorFromSupercharges S) x) := by
      rw [momentum_from_supercharges S]

end InfoGeometry.Canonical.CantorBernoulliPauliMatrixIntertwiner
