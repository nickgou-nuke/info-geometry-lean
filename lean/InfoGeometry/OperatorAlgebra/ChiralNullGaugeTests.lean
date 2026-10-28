/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ChiralCouplingOperators
import InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
import InfoGeometry.OperatorAlgebra.InnerDivergenceCharge
import InfoGeometry.OperatorAlgebra.ProjectiveNullInversion
import InfoGeometry.OperatorAlgebra.ConservedOperatorFlow

/-! # Non-vacuous noncommutative regression witnesses and aggregate import -/

namespace InfoGeometry.OperatorAlgebra.ChiralNullGaugeTests

open Matrix
open scoped BigOperators
open ChiralCouplingOperators MaurerCartanFrameTransport InnerDivergenceCharge
open InfoGeometry.Algebra

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

def couplingBlock : Mat := !![1, 1; 0, 1]
def sourceStep : Mat := !![0, 1; 0, 0]
def sinkStep : Mat := !![0, 0; 1, 0]
def region : Mat := !![1, 0; 0, 0]

theorem couplingBlock_nonzero : couplingBlock ≠ 0 := by
  intro h
  have hh := congrArg (fun M : Mat => M 0 0) h
  norm_num [couplingBlock] at hh

/-- Both mass-square blocks are genuinely operator-valued and do not commute. -/
theorem gramian_blocks_noncommuting :
    (couplingBlock * couplingBlockᵀ) * (couplingBlockᵀ * couplingBlock) ≠
      (couplingBlockᵀ * couplingBlock) * (couplingBlock * couplingBlockᵀ) := by
  intro h
  have hh := congrArg (fun M : Mat => M 0 1) h
  norm_num [couplingBlock, Matrix.mul_apply, Fin.sum_univ_two] at hh

theorem one_way_channel_nonzero_square_zero :
    chiral couplingBlock 0 ≠ 0 ∧
      chiral couplingBlock 0 * chiral couplingBlock 0 = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ =>
      M (.inl 0) (.inr 0)) h
    norm_num [chiral, couplingBlock] at hh
  · exact upper_square_zero couplingBlock

/-- Determinant zero is not the square-zero condition. -/
theorem singular_not_square_zero :
    Matrix.det (region + sourceStep) = 0 ∧
      (region + sourceStep) * (region + sourceStep) ≠ 0 := by
  constructor
  · norm_num [region, sourceStep, Matrix.det_fin_two]
  · intro h
    have hh := congrArg (fun M : Mat => M 0 0) h
    norm_num [region, sourceStep, Matrix.mul_apply, Fin.sum_univ_two] at hh

/-- An inner gradient is not generally irrotational in noncommuting directions. -/
theorem nonzero_curl_gradient :
    innerCurl (![sourceStep, sinkStep])
      (innerGradient (![sourceStep, sinkStep]) sourceStep) 0 1 ≠ 0 := by
  rw [curl_gradient_defect]
  intro h
  have hh := congrArg (fun M : Mat => M 0 1) h
  norm_num [sourceStep, sinkStep, Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_two] at hh

/-- Equal and opposite local charges are exhibited inside one full matrix algebra. -/
theorem boundary_flux_witness :
    Matrix.trace (region * ⁅sourceStep, sinkStep⁆) = 1 ∧
      Matrix.trace ((1 - region) * ⁅sourceStep, sinkStep⁆) = -1 ∧
      Matrix.trace ⁅sourceStep, sinkStep⁆ = 0 := by
  norm_num [region, sourceStep, sinkStep, Ring.lie_def, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- A nonzero positive operator source is impossible without a boundary term. -/
theorem positive_source_obstruction {ι : Type*} [Fintype ι]
    (H F : ι → Mat) : innerDivergence H F ≠ couplingBlockᵀ * couplingBlock :=
  nonzero_gramian_not_divergence couplingBlock couplingBlock_nonzero H F

/-- The full existing derivation algebra, acting faithfully by identity inclusion. -/
def fullLane : DerivationLieLane ℝ Mat where
  L := NonAssocDerivation.derivations ℝ Mat
  lieRing := inferInstance
  lieAlgebra := inferInstance
  act := LieHom.id
  faithful := Function.injective_id

/-- Concrete noncommuting directions in that native derivation carrier. -/
def innerDirection (H : Mat) : fullLane.L :=
  ⟨{ toFun := fun A => H * A - A * H
     map_add' := by intro A B; noncomm_ring
     map_smul' := by intro c A; simp [mul_smul_comm, smul_mul_assoc, smul_sub] },
    by intro A B; dsimp; noncomm_ring⟩

@[simp] theorem action_innerDirection (H A : Mat) :
    fullLane.operatorAction (innerDirection H) A = H * A - A * H := rfl

def shearUnit : Matˣ where
  val := couplingBlock
  inv := !![1, -1; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [couplingBlock, Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [couplingBlock, Matrix.mul_apply, Fin.sum_univ_two]

/-- Flatness does not mean that the connection values commute. -/
theorem noncommuting_pure_gauge :
    InfoGeometry.OperatorAlgebra.DerivationDifferentialForms.connectionCurvature fullLane
      (gaugeForm fullLane shearUnit) = 0 ∧
    ⁅gaugeForm fullLane shearUnit (innerDirection sinkStep),
      gaugeForm fullLane shearUnit (innerDirection region)⁆ ≠ 0 := by
  refine ⟨gaugeForm_flat fullLane shearUnit, ?_⟩
  intro h
  have hh := congrArg (fun M : Mat => M 0 1) h
  norm_num [gaugeForm_apply, action_innerDirection, shearUnit, couplingBlock,
    sinkStep, region, Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_two] at hh

end InfoGeometry.OperatorAlgebra.ChiralNullGaugeTests
