import InfoGeometry.OperatorAlgebra.QCCRResidual
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CStarCuntzFamilyTopology
import InfoGeometry.Canonical.CARCCRFockCuntzBridge
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
import Mathlib.Topology.Instances.Matrix

/-!
# CAR/CCR/Cuntz relations on an actual topological C⋆ realization

The algebraic `q`-CCR bridge is independent of a representation.  This file
connects its zero-parameter Cuntz readout to an existing Mathlib
`CStarCuntzFamily`, whose multiplication actions are continuous and already
packaged as `TopCat` morphisms.  No Fock-space existence theorem is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge

open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Physics.CStarCuntzTensorQuotient
open InfoGeometry.Physics.CStarCuntzTensorQuotient.CStarCuntzFamily

section

variable {A : Type*} [Ring A] [TopologicalSpace A] [T1Space A]
  [ContinuousMul A] [ContinuousSub A]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def qCcrResidualContinuousMap (q : A) :
    ContinuousMap (A × A) A :=
  { toFun := fun p => qCcrRelation p.1 p.2 q
    continuous_toFun := by
      exact ((continuous_fst.mul continuous_snd).sub
        ((continuous_const.mul continuous_snd).mul continuous_fst)).sub
        continuous_const }


def qCcrZeroLocus (q : A) : Set (A × A) :=
  (qCcrResidualContinuousMap q) ⁻¹' ({0} : Set A)

theorem qCcrZeroLocus_closed (q : A) :
    IsClosed (qCcrZeroLocus q) := by
  exact isClosed_singleton.preimage
    (qCcrResidualContinuousMap (A := A) q).continuous_toFun

end

section
variable {A ι : Type*} [CStarAlgebra A] [Fintype ι] [DecidableEq ι]

theorem cstar_cuntz_generator_qccr_zero
    (F : CStarCuntzFamily A ι) (i : ι) :
    qCcrRelation (star (F.S i)) (F.S i) 0 = 0 := by
    calc
    qCcrRelation (star (F.S i)) (F.S i) 0 =
        star (F.S i) * F.S i - 1 := by
          simp [qCcrRelation]
    _ = 0 := by
      rw [CStarCuntzFamily.isometry_relation (F := F) i]
      simp

/-! The zero-q Cuntz boundary is distinct from the fermionic boundary. -/

theorem cstar_cuntz_generator_not_car
    [Nontrivial A]
    (F : CStarCuntzFamily A ι) (i : ι) :
    ¬ qCcrRelation (star (F.S i)) (F.S i) (-1) = 0 := by
  intro hcar
  have hisometry :
      star (F.S i) * F.S i = 1 :=
    CStarCuntzFamily.isometry_relation (F := F) i
  have hcar' :
      star (F.S i) * F.S i + F.S i * star (F.S i) = 1 :=
    (qccr_fermionic_limit _ _).mp hcar
  have hrange : F.S i * star (F.S i) = 0 := by
    rw [hisometry] at hcar'
    have hsplit :
        (1 : A) + F.S i * star (F.S i) = 1 + 0 := by
      simpa using hcar'
    exact add_left_cancel hsplit
  have hone : (1 : A) = 0 := by
    calc
      (1 : A) =
          (star (F.S i) * F.S i) * (star (F.S i) * F.S i) := by
        rw [hisometry]
        simp
      _ = star (F.S i) *
          (F.S i * star (F.S i)) * F.S i := by
        noncomm_ring
      _ = 0 := by
        rw [hrange, mul_zero, zero_mul]
  exact one_ne_zero hone


theorem cstar_cuntz_generator_mem_qccr_zeroLocus
    (F : CStarCuntzFamily A ι) (i : ι) :
    (star (F.S i), F.S i) ∈ qCcrZeroLocus (A := A) (0 : A) := by
  exact cstar_cuntz_generator_qccr_zero (A := A) F i


theorem cstar_cuntz_generator_left_action_continuous
    (F : CStarCuntzFamily A ι) (i : ι) :
    Continuous (F.leftGeneratorAction i) :=
  (F.leftGeneratorAction i).continuous_toFun


theorem cstar_cuntz_generator_right_adjoint_action_continuous
    (F : CStarCuntzFamily A ι) (i : ι) :
    Continuous (F.rightAdjointGeneratorAction i) :=
  (F.rightAdjointGeneratorAction i).continuous_toFun
end

/-! ### Finite CAR readout in the same closed q-CCR geometry -/

section

def finiteCARQCCRResidualContinuousMap :
    ContinuousMap
      ((Matrix Bool Bool ℂ) × (Matrix Bool Bool ℂ)) (Matrix Bool Bool ℂ) :=
  qCcrResidualContinuousMap (A := Matrix Bool Bool ℂ) (-1)

def finiteCARQCCRMinusOneLocus :
    Set ((Matrix Bool Bool ℂ) × (Matrix Bool Bool ℂ)) :=
  qCcrZeroLocus (A := Matrix Bool Bool ℂ) (-1)


theorem finite_car_mem_qccr_minus_oneLocus :
    (FiniteSingleModeCARMatrixBridge.annMatrix2,
      FiniteSingleModeCARMatrixBridge.creMatrix2) ∈
      finiteCARQCCRMinusOneLocus := by
  simpa [finiteCARQCCRMinusOneLocus, qCcrZeroLocus] using
    (CARCCRFockCuntzBridge.finite_car_qccr_residual :
      qCcrRelation
      FiniteSingleModeCARMatrixBridge.annMatrix2
      FiniteSingleModeCARMatrixBridge.creMatrix2
      (-1) = 0
    )

theorem finite_car_qccr_minus_oneLocus_closed
    [T1Space (Matrix Bool Bool ℂ)] :
    IsClosed finiteCARQCCRMinusOneLocus := by
  exact isClosed_singleton.preimage
    finiteCARQCCRResidualContinuousMap.continuous_toFun

end

end InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
