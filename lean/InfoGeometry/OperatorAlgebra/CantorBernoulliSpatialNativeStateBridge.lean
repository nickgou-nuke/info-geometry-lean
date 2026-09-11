import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum

/-!
# Native spatial Bernoulli state

This owner packages the constant-vector functional on the concrete bounded
operator algebra as a Mathlib `PositiveLinearMap` and normalized state.  It
does not identify this spatial state with the gauge-invariant Cuntz word
kernel; the existing finite word-kernel owner proves that their off-diagonal
readouts differ.
-/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge

open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open CStarStateColimit.Native

abbrev B := BoundedL2Operator

def spatialFunctional : B →ₗ[ℂ] ℂ where
  toFun := cantorVacuumState
  map_add' A C := by
    dsimp [cantorVacuumState]
    simp [inner_add_right]
  map_smul' c A := by
    dsimp [cantorVacuumState]
    simp [inner_smul_right]

@[simp] theorem spatialFunctional_apply (A : B) :
    spatialFunctional A = cantorVacuumState A := rfl

theorem spatialFunctional_star_mul_self_nonneg (A : B) :
    0 ≤ spatialFunctional (star A * A) := by
  rw [spatialFunctional_apply]
  dsimp [cantorVacuumState]
  have h := ContinuousLinearMap.adjoint_inner_right A vacuumL2 (A vacuumL2)
  change 0 ≤ inner ℂ vacuumL2 ((ContinuousLinearMap.adjoint A) (A vacuumL2))
  rw [h]
  have him : (inner ℂ (A vacuumL2) (A vacuumL2)).im = 0 :=
    inner_self_im (𝕜 := ℂ) (A vacuumL2)
  exact Complex.nonneg_iff.mpr
    ⟨inner_self_nonneg (𝕜 := ℂ) (x := A vacuumL2), him.symm⟩

theorem spatialFunctional_monotone : Monotone spatialFunctional := by
  intro A C hAC
  rw [ContinuousLinearMap.le_def] at hAC
  have hpos := (ContinuousLinearMap.isPositive_iff (C - A)).mp hAC
  have hv := hpos.2 vacuumL2
  have hv' := Complex.nonneg_iff.mp hv
  apply Complex.le_def.mpr
  constructor
  · apply sub_nonneg.mp
    have hreal : 0 ≤ (inner ℂ vacuumL2 ((C - A) vacuumL2)).re := by
      calc
        0 ≤ (inner ℂ ((C - A) vacuumL2) vacuumL2).re := hv'.1
        _ = (inner ℂ vacuumL2 ((C - A) vacuumL2)).re :=
          (inner_re_symm (𝕜 := ℂ) vacuumL2 ((C - A) vacuumL2)).symm
    simpa [map_sub, spatialFunctional_apply, cantorVacuumState,
      inner_sub_right] using hreal
  · have him' :
        (inner ℂ vacuumL2 ((C - A) vacuumL2)).im =
          -(inner ℂ ((C - A) vacuumL2) vacuumL2).im := by
      exact inner_im_symm (𝕜 := ℂ) vacuumL2 ((C - A) vacuumL2)
    have him : (inner ℂ vacuumL2 ((C - A) vacuumL2)).im = 0 := by
      calc
        _ = -(inner ℂ ((C - A) vacuumL2) vacuumL2).im := him'
        _ = -0 := by rw [hv'.2]
        _ = 0 := neg_zero
    change (inner ℂ vacuumL2 (A vacuumL2)).im =
      (inner ℂ vacuumL2 (C vacuumL2)).im
    have him'' :
        (inner ℂ vacuumL2 (C vacuumL2)).im -
            (inner ℂ vacuumL2 (A vacuumL2)).im = 0 := by
      simpa [inner_sub_right] using him
    linarith

def spatialPositiveFunctional : B →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk spatialFunctional spatialFunctional_monotone

@[simp] theorem spatialPositiveFunctional_apply (A : B) :
    spatialPositiveFunctional A = cantorVacuumState A := rfl

theorem spatialPositiveFunctional_one :
    spatialPositiveFunctional (1 : B) = 1 := by
  rw [spatialPositiveFunctional_apply]
  exact cantorVacuumState_id

def spatialState : CStarStateColimit.Native.State B where
  functional := spatialPositiveFunctional
  normalized := spatialPositiveFunctional_one

@[simp] theorem spatialState_apply (A : B) :
    spatialState.functional A = cantorVacuumState A := rfl

theorem spatialState_projector (b : Bool) :
    spatialState.functional (P b) = (1 / 2 : ℂ) := by
  rw [spatialState_apply]
  exact cantorVacuumState_proj b

noncomputable def spatialPreGNSVacuum :
    spatialPositiveFunctional.PreGNS :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.preGNSVacuum
    spatialPositiveFunctional

theorem spatialPreGNS_expectation_recovery (A : B) :
    ⟪spatialPreGNSVacuum,
      spatialPositiveFunctional.leftMulMapPreGNS A spatialPreGNSVacuum⟫_ℂ =
        spatialPositiveFunctional A := by
  exact InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.preGNSVacuum_expectation
    spatialPositiveFunctional A

noncomputable def spatialGNSVacuum : spatialPositiveFunctional.GNS :=
  InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum
    spatialPositiveFunctional

theorem spatialGNSVacuum_norm : ‖spatialGNSVacuum‖ = 1 := by
  simpa [spatialGNSVacuum] using
    (InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsVacuum_norm_eq_one
      spatialPositiveFunctional spatialPositiveFunctional_one)

noncomputable abbrev spatialGNSRepresentation :=
  spatialPositiveFunctional.gnsStarAlgHom

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem spatialGNS_expectation_recovery (A : B) :
    ⟪spatialGNSVacuum,
      spatialGNSRepresentation A spatialGNSVacuum⟫_ℂ =
        spatialPositiveFunctional A := by
  exact InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gns_state_expectation_recovery
    spatialPositiveFunctional A

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem spatialGNS_cyclic :
    DenseRange (fun A : B =>
      spatialGNSRepresentation A spatialGNSVacuum) := by
  rw [show (fun A : B => spatialGNSRepresentation A spatialGNSVacuum) =
      fun A : B =>
        InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap
          spatialPositiveFunctional A by
    funext A
    exact
      (InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap_eq_gnsRepresentation
        spatialPositiveFunctional A).symm]
  exact InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum.gnsOrbitMap_denseRange
    spatialPositiveFunctional

end InfoGeometry.OperatorAlgebra.CantorBernoulliSpatialNativeStateBridge
