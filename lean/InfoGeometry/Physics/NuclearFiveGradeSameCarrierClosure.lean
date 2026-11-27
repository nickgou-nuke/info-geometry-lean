/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
import InfoGeometry.Physics.NuclearBdGTwoLevelExact
import InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
import InfoGeometry.Physics.OperatorRPABlock

/-!
# End-to-end same-carrier nuclear closure

This capstone records the concrete chain on one represented carrier:

* the two-mode CAR commutator Lie algebra acts by a native Lie homomorphism;
* the five adjoint grades are preserved;
* fermionic CAR and phonon CCR coexist and commute;
* a model-space idempotent compresses the represented Hamiltonian to the
  finite Soloviev QPNM block;
* the finite block is a scalar center plus a traceless BdG block;
* the BdG block has the exact square/spectral/particle-hole identities.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure

open Matrix
open InfoGeometry.Canonical.ZornDerivationLieCARCCREnvelope
open InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierRepresentation
open InfoGeometry.Physics.NuclearFiveGradeCommonCarrierLieHom
open InfoGeometry.Physics.NuclearFiveGradeSolovievCommonCompression
open InfoGeometry.Physics.NuclearBdGTwoLevelExact
open InfoGeometry.Physics.NuclearBdGSolovievAffineBridge
open InfoGeometry.Physics.SolovievQPNMEigenproblem
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev

local instance : LieRing M4R := LieRing.ofAssociativeRing
local instance : LieRing Operator := LieRing.ofAssociativeRing

/-- Complete same-carrier theorem packet. -/
theorem nuclear_same_carrier_closure_packet
    (X Y : M4R)
    (D E : NativeZornDerLie)
    (ξ Δ Eqp omega V C₀ C₁ : ℝ)
    (ψ : V2C) :
    commonRepresentationLieHom ⁅X, Y⁆ =
        ⁅commonRepresentationLieHom X,
          commonRepresentationLieHom Y⁆ ∧
      RepresentedHasGrade 2 (representation pairCreation) ∧
      RepresentedHasGrade (-2) (representation pairAnnihilation) ∧
      representation
          InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 *
          representation
            InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag +
        representation
            InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag *
          representation
            InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 = 1 ∧
      phononAnnihilation * phononCreation -
          phononCreation * phononAnnihilation = 1 ∧
      representation pairCreation * phononCreation =
          phononCreation * representation pairCreation ∧
      coefficientLift ((⁅D, E⁆ : NativeZornDerLie) : NativeZornEnd) =
        coefficientLift (D : NativeZornEnd) *
            coefficientLift (E : NativeZornEnd) -
          coefficientLift (E : NativeZornEnd) *
            coefficientLift (D : NativeZornEnd) ∧
      modelProjection * modelProjection = modelProjection ∧
      modelProjection
          (fullHamiltonian Eqp omega V
            (modelProjection (modelEmbed ![C₀, C₁]))) =
        modelEmbed (mulVec (qpnmMatrix Eqp omega V) ![C₀, C₁]) ∧
      qpnmMatrix Eqp omega V =
        solovievCenter Eqp omega •
            (1 : InfoGeometry.Physics.NuclearBdGSolovievAffineBridge.M2R) +
          bdgBlock (solovievBdGCoordinate omega) V ∧
      bdgBlock ξ Δ * bdgBlock ξ Δ =
        (ξ ^ 2 + Δ ^ 2) •
          (1 : InfoGeometry.Physics.NuclearBdGTwoLevelExact.M2R) ∧
      bdgBlock ξ Δ * bdgEigenbasis ξ Δ =
        bdgEigenbasis ξ Δ * bdgSpectrum ξ Δ ∧
      particleHole (particleHole ψ) = -ψ ∧
      particleHole (mulVec (bdgBlockC ξ Δ) ψ) =
        -mulVec (bdgBlockC ξ Δ) (particleHole ψ) := by
  refine ⟨commonRepresentationLieHom.map_lie X Y,
    representation_preserves_grade pairCreation_grade,
    representation_preserves_grade pairAnnihilation_grade,
    represented_mode1_CAR,
    phonon_CCR,
    representation_commutes_phononCreation pairCreation,
    ?_,
    modelProjection_idempotent,
    projected_fullHamiltonian_on_model Eqp omega V C₀ C₁,
    qpnm_eq_center_add_bdg Eqp omega V,
    bdgBlock_sq ξ Δ,
    bdg_eigenbasis_intertwines ξ Δ,
    particleHole_sq ψ,
    particleHole_anticommutes ξ Δ ψ⟩
  change coefficientLift
      ((D : NativeZornEnd) * (E : NativeZornEnd) -
        (E : NativeZornEnd) * (D : NativeZornEnd)) = _
  exact coefficientLift_commutator (D : NativeZornEnd) (E : NativeZornEnd)

/-- On the concrete two-mode CAR carrier, the off-diagonal defect in the
square of the signed RPA block built from pair creation and annihilation is
exactly the grade-zero occupation Cartan. Thus the mixed noncommutative
commutator records the conserved grading operator rather than a scalar
surrogate. -/
theorem pair_rpa_square_defect_is_grade_zero_cartan :
    (blockHamiltonian pairCreation (-pairCreation)
      pairAnnihilation (-pairAnnihilation) *
      blockHamiltonian pairCreation (-pairCreation)
        pairAnnihilation (-pairAnnihilation)) 0 1 = gradingOperator ∧
      gradingOperator ≠ 0 := by
  constructor
  · rw [InfoGeometry.Physics.OperatorRPABlock.rpa_square]
    change pairCreation * pairAnnihilation -
      pairAnnihilation * pairCreation = gradingOperator
    simpa [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm]
      using pair_extreme_bracket
  · rw [gradingOperator_eq_diagonal]
    intro hzero
    have h00 := congrFun (congrFun hzero 0) 0
    norm_num at h00

/-- The concrete CAR pair-annihilation operator is nonzero, so its scalar
backward amplitude vanishes exactly when the represented backward coupling
vanishes. -/
theorem pairAnnihilation_smul_eq_zero_iff (β : ℝ) :
    β • pairAnnihilation = 0 ↔ β = 0 := by
  have hpair : pairAnnihilation ≠ 0 := by
    intro h
    have h03 := congrFun (congrFun h 0) 3
    norm_num [pairAnnihilation,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2, Matrix.mul_apply,
      Fin.sum_univ_four] at h03
  constructor
  · intro h
    rcases smul_eq_zero.mp h with hβ | hzero
    · exact hβ
    · exact (hpair hzero).elim
  · rintro rfl
    simp

/-- A nonzero backward coupling need not reflect every individual forward
state: the first-mode annihilator lies in the left kernel of the pair
annihilator. This is statewise kernel behavior and does not contradict the
whole-sector iff above. -/
theorem nonzero_forward_state_unaffected_by_pair_coupling :
    ∃ x : M4R, x ≠ 0 ∧ pairAnnihilation ≠ 0 ∧
      (blockHamiltonian pairCreation (-pairCreation)
        pairAnnihilation (-pairAnnihilation)).mulVec ![x, 0] 1 = 0 := by
  have ha1 : InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 ≠ 0 := by
    intro h
    have h02 := congrFun (congrFun h 0) 2
    norm_num [InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1] at h02
  have hkernel : pairAnnihilation *
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pairAnnihilation,
        InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
        InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
        Matrix.mul_apply, Fin.sum_univ_four]
  have hpair : pairAnnihilation ≠ 0 := by
    intro h
    have h03 := congrFun (congrFun h 0) 3
    norm_num [pairAnnihilation,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2, Matrix.mul_apply,
      Fin.sum_univ_four] at h03
  refine ⟨InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1, ha1, ?_, ?_⟩
  · exact hpair
  · exact (InfoGeometry.Physics.OperatorRPABlock.rpa_forward_state_no_backward_output_iff
      pairCreation pairAnnihilation
      InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1).2 hkernel

/-- On the concrete two-mode CAR coefficient ring, the Tamm--Dancoff forward
sector is invariant precisely when the coefficient of pair annihilation is
zero. This instantiates the arbitrary-unital-ring characterization with the
actual CAR pair operators, rather than a scalar replacement for them. -/
theorem car_tda_forward_sector_iff_no_backward_pair
    (α β : ℝ) :
    (∀ x : M4R,
      (blockHamiltonian (α • pairCreation) (-(α • pairCreation))
        (β • pairAnnihilation) (-(β • pairAnnihilation))).mulVec ![x, 0] 1 = 0) ↔
      β = 0 := by
  rw [InfoGeometry.Physics.OperatorRPABlock.rpa_forward_sector_invariant_iff_backward_coupling_zero]
  exact pairAnnihilation_smul_eq_zero_iff β

/-- The noncommutative off-diagonal term in the scaled CAR RPA square is the
forward/backward amplitude product times the grade-zero Cartan. It is nonzero
when both amplitudes are nonzero, identifying the obstruction-generated
quantum-number channel exactly. -/
theorem car_rpa_square_defect_is_amplitude_weighted_cartan
    (α β : ℝ) :
    (blockHamiltonian (α • pairCreation) (-(α • pairCreation))
      (β • pairAnnihilation) (-(β • pairAnnihilation)) *
      blockHamiltonian (α • pairCreation) (-(α • pairCreation))
        (β • pairAnnihilation) (-(β • pairAnnihilation))) 0 1 =
      (α * β) • gradingOperator := by
  rw [InfoGeometry.Physics.OperatorRPABlock.rpa_square]
  change comm (α • pairCreation) (β • pairAnnihilation) =
    (α * β) • gradingOperator
  have hBracket : pairCreation * pairAnnihilation -
      pairAnnihilation * pairCreation = gradingOperator := by
    simpa [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm]
      using pair_extreme_bracket
  calc
    comm (α • pairCreation) (β • pairAnnihilation) =
        α • (β • (pairCreation * pairAnnihilation -
          pairAnnihilation * pairCreation)) := by
          rw [comm_smul_left, comm_smul_right]
          simp only [InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.comm]
    _ = (α * β) • gradingOperator := by
          rw [smul_smul]
          change (α * β) • (pairCreation * pairAnnihilation -
            pairAnnihilation * pairCreation) = _
          rw [hBracket]

end InfoGeometry.Physics.NuclearFiveGradeSameCarrierClosure
