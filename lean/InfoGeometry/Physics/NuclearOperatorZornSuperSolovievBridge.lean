import Mathlib
import InfoGeometry.Physics.NuclearOperatorSuperSoloviev
import InfoGeometry.Physics.OperatorZornMatrixAlgebra

/-!
# Operator-Zorn realization of the super Soloviev grading

`OperatorZornMatrix A` is the repository's associative transported `2 × 2`
operator-matrix owner.  It is deliberately distinct from genuine
non-associative split-octonion Zorn multiplication.

The existing Nambu--Gorkov chiral grading and Dirac block therefore provide a
native realization of the operator super-Soloviev parity theory:

* the grading squares to one;
* the Dirac block is internally odd;
* the Dirac square is internally even;
* a super-Hamiltonian with even diagonal Dirac-square channels and odd Dirac
off-diagonal channels is invariant under total Fock/internal parity.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge

open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.OperatorZornMatrix

variable {A : Type*} [Ring A] [StarRing A]

abbrev OZ := OperatorZornMatrix A

/-- The native operator-Zorn chiral grading as an internal parity datum. -/
def operatorZornParity : InternalParity (OperatorZornMatrix A) where
  gamma := (InfoGeometry.Physics.NCG.chiralGradingOperator : OZ)
  gamma_sq := by
    change (InfoGeometry.Physics.NCG.chiralGradingOperator : OZ) *
        InfoGeometry.Physics.NCG.chiralGradingOperator =
      (⟨1, 1, 0, 0⟩ : OZ)
    exact chiral_grading_sq_native (A := A)

/-- The native Nambu--Gorkov Dirac block is internally odd. -/
theorem dirac_internal_odd (Delta : A) :
    (operatorZornParity (A := A)).IsOdd
      (InfoGeometry.Physics.NCG.diracOperator Delta) := by
  unfold InternalParity.IsOdd InternalParity.act operatorZornParity
  have hanti := dirac_anticommutes_with_chirality_native (A := A) Delta
  have hswap :
      InfoGeometry.Physics.NCG.chiralGradingOperator *
          InfoGeometry.Physics.NCG.diracOperator Delta =
        -(InfoGeometry.Physics.NCG.diracOperator Delta *
          InfoGeometry.Physics.NCG.chiralGradingOperator) := by
    exact eq_neg_of_add_eq_zero_right hanti
  calc
    InfoGeometry.Physics.NCG.chiralGradingOperator *
        InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.chiralGradingOperator =
      -(InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.chiralGradingOperator) *
        InfoGeometry.Physics.NCG.chiralGradingOperator := by rw [hswap]
    _ = -InfoGeometry.Physics.NCG.diracOperator Delta *
        (InfoGeometry.Physics.NCG.chiralGradingOperator *
          InfoGeometry.Physics.NCG.chiralGradingOperator) := by
      noncomm_ring
    _ = -InfoGeometry.Physics.NCG.diracOperator Delta := by
      have hG := (operatorZornParity (A := A)).gamma_sq
      change InfoGeometry.Physics.NCG.chiralGradingOperator *
          InfoGeometry.Physics.NCG.chiralGradingOperator = (1 : OZ) at hG
      simpa only [mul_one] using
        congrArg (fun X : OZ => -InfoGeometry.Physics.NCG.diracOperator Delta * X) hG

/-- The square of the native Dirac block is internally even. -/
theorem dirac_square_internal_even (Delta : A) :
    (operatorZornParity (A := A)).IsEven
      (InfoGeometry.Physics.NCG.diracOperator Delta *
        InfoGeometry.Physics.NCG.diracOperator Delta) := by
  unfold InternalParity.IsEven InternalParity.act operatorZornParity
  let D : OperatorZornMatrix A := InfoGeometry.Physics.NCG.diracOperator Delta
  let G : OperatorZornMatrix A := InfoGeometry.Physics.NCG.chiralGradingOperator
  have hcomm : D * D * G = G * (D * D) := by
    simpa [D, G] using dirac_square_commutes_with_chirality_native (A := A) Delta
  calc
    G * (D * D) * G = (D * D * G) * G := by rw [hcomm]
    _ = D * D * (G * G) := by noncomm_ring
    _ = D * D := by
      have hG : G * G = 1 := (operatorZornParity (A := A)).gamma_sq
      rw [hG]
      simp

/-- Canonical super-Soloviev block built from one odd Dirac channel and its
even square. -/
def diracSuperHamiltonian (Delta : A) : Block2 (OperatorZornMatrix A) :=
  starBlockHamiltonian (A := OperatorZornMatrix A)
    (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta)
    (InfoGeometry.Physics.NCG.diracOperator Delta *
      InfoGeometry.Physics.NCG.diracOperator Delta)
    (InfoGeometry.Physics.NCG.diracOperator Delta)

/-- The operator-Zorn Dirac super-Hamiltonian is total-parity invariant. -/
theorem diracSuperHamiltonian_invariant (Delta : A) :
    totalParity (operatorZornParity (A := A)) *
        diracSuperHamiltonian Delta *
        totalParity (operatorZornParity (A := A)) =
      diracSuperHamiltonian Delta := by
  apply starBlock_invariant_of_internal_odd
  · unfold InternalParity.IsSelfAdjoint operatorZornParity
    apply (equivMatrix (A := A)).injective
    simp [InfoGeometry.Physics.NCG.chiralGradingOperator, toMatrix,
      starOp, ofMatrix, Matrix.star_apply]
  · exact dirac_square_internal_even Delta
  · exact dirac_square_internal_even Delta
  · exact dirac_internal_odd Delta

end InfoGeometry.Physics.NuclearOperatorZornSuperSolovievBridge

end noncomputable section
