/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteCARCCRCommonCarrier

/-!
# Hole-reflected cancellation of the finite CCR boundary anomaly

The equal-sign particle–hole lift of the finite CCR boundary defect is
Andreev-even.  The opposite-sign lift is Andreev-odd and therefore cancels
with its hole-reflected image.  This fixes the sign mismatch without
identifying the distinct CCR and CAR relations.
-/

namespace InfoGeometry.Canonical.FARAndreevCancellation

open InfoGeometry.Canonical.FiniteCARCCRCommonCarrier
open InfoGeometry.Physics
open InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction

/-- In any operator ring, a chiral grading turns a commuting diagonal
operator into an explicit mass commutator on the off-diagonal blocks. -/
theorem chiral_grading_twisted_mass_interaction
    {R : Type*} [Ring R] (C D M : R)
    (hD : C * D = D * C) (hM : C * M = M * C) :
    (InfoGeometry.Physics.chiralGrading * !![C, 0; 0, C] :
        InfoGeometry.Physics.BdGBlock R) *
        InfoGeometry.Physics.massiveBdGHamiltonian D M -
      InfoGeometry.Physics.massiveBdGHamiltonian D M *
        (InfoGeometry.Physics.chiralGrading * !![C, 0; 0, C]) =
      (2 : ℤ) • !![0, C * M; -(C * M), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.Physics.chiralGrading,
      InfoGeometry.Physics.massiveBdGHamiltonian, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
      mul_neg, neg_mul, neg_neg]
    <;> noncomm_ring [hD, hM]

/-- The finite twistor CCR defect is a nonzero matrix operator: its vacuum
diagonal entry is one. -/
theorem finite_twistor_CCR_boundary_nonzero :
    InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.commutator
        InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.twistorCoordinate
        InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.twistorDerivative ≠ 0 := by
  intro h
  have h00 := congrArg
    (fun X : InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.TwistorOperator => X 0 0) h
  rw [InfoGeometry.Canonical.FiniteTwistorCCRGeneratingFunction.finite_twistor_commutator] at h00
  norm_num at h00

private def cutoffCARReadoutAtZero : CutoffCARState →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun x ψ => x 0 * ψ 0)
      (fun x y ψ => by simp [add_mul])
      (fun c x ψ => by simp [smul_eq_mul, mul_left_comm, mul_comm])
      (fun x ψ χ => by simp [mul_add])
      (fun c x ψ => by
        change x 0 * (c * ψ 0) = c * (x 0 * ψ 0)
        ring))

/-- The lifted boundary defect acts nontrivially on the finite common carrier.
The readout detects its action on the level-zero cutoff state. -/
theorem finiteCCRBoundary_ne_zero : finiteCCRBoundary ≠ 0 := by
  intro hzero
  let x : CutoffState := Pi.single 0 (1 : ℂ)
  let ψ : InfoGeometry.Physics.NuclearTwoModeCARFiveGrade.Fock4 :=
    Pi.single 0 (1 : ℂ)
  have hread := congrArg
    (fun T : CutoffCAROperator => cutoffCARReadoutAtZero (T (x ⊗ₜ[ℂ] ψ))) hzero
  have hvalue :
      cutoffCARReadoutAtZero (finiteCCRBoundary (x ⊗ₜ[ℂ] ψ)) = 1 := by
    simp [finiteCCRBoundary, cutoffCCRAction, cutoffCARReadoutAtZero, x, ψ,
      Matrix.toLin'_apply]
    rw [finite_twistor_commutator]
    norm_num
  rw [hvalue] at hread
  norm_num at hread

/-- The signed particle–hole lift of the finite CCR boundary defect. -/
def finiteCCRBoundaryHoleLift : BdGBlock CutoffCAROperator :=
  chiralGrading * finiteCCRBoundaryBdGLift

/-- The chiral grading converts the equal-sign boundary lift into opposite
particle and hole signs. -/
theorem finiteCCRBoundaryHoleLift_eq_signed_blocks :
    finiteCCRBoundaryHoleLift = !![finiteCCRBoundary, 0; 0, -finiteCCRBoundary] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteCCRBoundaryHoleLift, finiteCCRBoundaryBdGLift,
      chiralGrading, Matrix.mul_apply, Fin.sum_univ_two]

/-- Andreev reflection exchanges the particle and hole boundary entries, so
the hole-reflected lift is sent to its additive inverse. -/
theorem andreev_reflection_negates_CCR_boundary_hole_lift :
    andreevSwap * finiteCCRBoundaryHoleLift * andreevSwap =
      -finiteCCRBoundaryHoleLift := by
  rw [finiteCCRBoundaryHoleLift_eq_signed_blocks]
  rw [andreevSwap_conj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.neg_apply]

/-- The boundary anomaly and its Andreev-reflected hole contribution cancel
exactly in the BdG block algebra. -/
theorem andreev_hole_cancels_CCR_boundary_anomaly :
    andreevSwap * finiteCCRBoundaryHoleLift * andreevSwap +
      finiteCCRBoundaryHoleLift = 0 := by
  rw [andreev_reflection_negates_CCR_boundary_hole_lift]
  exact neg_add_cancel finiteCCRBoundaryHoleLift

/-- Squaring the signed lift forgets the particle–hole sign and recovers the
same boundary-support projection in both BdG sectors. -/
theorem finiteCCRBoundaryHoleLift_square :
    finiteCCRBoundaryHoleLift * finiteCCRBoundaryHoleLift =
      finiteCCRBoundarySupportBdGLift := by
  rw [finiteCCRBoundaryHoleLift_eq_signed_blocks]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteCCRBoundarySupportBdGLift,
      finiteCCRBoundarySupport, Matrix.mul_apply, Fin.sum_univ_two,
      mul_neg, neg_mul, neg_neg]

/-- Chiral twisting turns the CCR boundary symmetry's commutation with the
CAR Hamiltonian into an explicit off-diagonal mass interaction.  This records
the operator term generated by the hole-reflected boundary defect. -/
theorem finiteCCRBoundaryHoleLift_mass_commutator :
    finiteCCRBoundaryHoleLift *
        InfoGeometry.Physics.massiveBdGHamiltonian
          finiteCARKinetic finiteCARMass -
      InfoGeometry.Physics.massiveBdGHamiltonian
          finiteCARKinetic finiteCARMass * finiteCCRBoundaryHoleLift =
      (2 : ℤ) • !![0, finiteCCRBoundary * finiteCARMass;
        -(finiteCCRBoundary * finiteCARMass), 0] := by
  rcases finiteCCRBoundary_commutes_with_CAR_mass_pair with ⟨hK, hM⟩
  simpa only [finiteCCRBoundaryHoleLift, finiteCCRBoundaryBdGLift] using
    chiral_grading_twisted_mass_interaction
      finiteCCRBoundary finiteCARKinetic finiteCARMass hK hM

/-- The Andreev-odd lift is nonzero because its particle block is the
nonzero common-carrier CCR boundary operator. -/
theorem finiteCCRBoundaryHoleLift_ne_zero : finiteCCRBoundaryHoleLift ≠ 0 := by
  intro hzero
  have h00 := congrArg (fun X : BdGBlock CutoffCAROperator => X 0 0) hzero
  rw [finiteCCRBoundaryHoleLift_eq_signed_blocks] at h00
  exact finiteCCRBoundary_ne_zero (by simpa using h00)

end InfoGeometry.Canonical.FARAndreevCancellation
