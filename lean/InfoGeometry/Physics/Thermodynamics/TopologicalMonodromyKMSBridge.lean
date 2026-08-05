import InfoGeometry.OperatorAlgebra.HorizonKMS
import InfoGeometry.Physics.Algebra.TopologicalBraidMonodromyOperator

/-!
# Topological monodromy KMS readout

This module packages the existing square-zero monodromy flow as a KMS-style
readout datum on bounded operators.  The state is the zero functional, so the
flow invariance is genuine but deliberately minimal.  No spectral triple or
analytic KMS boundary theorem is claimed.
-/

namespace InfoGeometry.Physics.Thermodynamics.TopologicalMonodromyKMSBridge

open ContinuousLinearMap
open InfoGeometry.OperatorAlgebra.HorizonKMS

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

local instance : AddCommGroup EndH := inferInstance
local instance : Module ℝ EndH := inferInstance
noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- The unipotent monodromy flow as a KMS-style readout datum. -/
def unipotentMonodromyReadoutDatum
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H) :
    KMSReadoutDatum EndH where
  flow := fun t T => InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t * T
  state := fun _ => 0
  beta := 1
  beta_pos := by positivity
  flow_zero := by
    intro T
    simp [InfoGeometry.Physics.Algebra.continuousUnipotentFlow]
  flow_add := by
    intro s t T
    calc
      InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (s + t) * T =
          (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M s *
            InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t) * T := by
              rw [InfoGeometry.Physics.Algebra.continuousUnipotentFlow_add]
      _ = InfoGeometry.Physics.Algebra.continuousUnipotentFlow M s *
            (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t * T) := by
          rw [mul_assoc]
  flow_invariant := by
    intro t T
    simp

/--
The readout flow on the bounded-operator carrier is a continuous linear
equivalence with inverse at the negated parameter.
-/
noncomputable def unipotentMonodromyReadoutEquiv
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H)
    (t : ℝ) : EndH ≃L[ℝ] EndH := by
  let e : EndH ≃ₗ[ℝ] EndH :=
    { toLinearMap := ContinuousLinearMap.mul ℝ EndH
        (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t)
      invFun := ContinuousLinearMap.mul ℝ EndH
        (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (-t))
      left_inv := by
        intro T
        ext x
        change (((InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (-t)) *
            (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t)) * T) x =
          T x
        rw [InfoGeometry.Physics.Algebra.continuousUnipotentFlow_neg_mul (M := M) t]
        simp
      right_inv := by
        intro T
        ext x
        change (((InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t) *
            (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (-t))) * T) x =
          T x
        rw [InfoGeometry.Physics.Algebra.continuousUnipotentFlow_mul_neg (M := M) t]
        simp }
  exact ContinuousLinearEquiv.mk e
    (ContinuousLinearMap.mul ℝ EndH
      (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M t)).continuous
    (ContinuousLinearMap.mul ℝ EndH
      (InfoGeometry.Physics.Algebra.continuousUnipotentFlow M (-t))).continuous

omit [CompleteSpace H] in
theorem unipotentMonodromyReadoutEquiv_comp
    (M : InfoGeometry.Physics.Algebra.ContinuousMonodromyOperator H)
    (s t : ℝ) :
    (unipotentMonodromyReadoutEquiv (H := H) M t).trans
        (unipotentMonodromyReadoutEquiv (H := H) M s) =
      unipotentMonodromyReadoutEquiv (H := H) M (t + s) := by
  ext T x
  have h := InfoGeometry.Physics.Algebra.continuousUnipotentFlow_add (M := M) s t
  simpa [add_comm, unipotentMonodromyReadoutEquiv, ContinuousLinearMap.mul_apply] using
    congrArg (fun Y : EndH => Y (T x)) h

end

end InfoGeometry.Physics.Thermodynamics.TopologicalMonodromyKMSBridge
