import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Algebra.TopologicalBraidMonodromyOperator

/-!
# Dirac commutators of logarithmic monodromy

The scalar part of a Jordan-type monodromy is invisible to commutators.  This
owner records that cancellation for bounded real continuous linear operators;
it does not assert a spectral-triple or KMS theorem.
-/

namespace InfoGeometry.Physics.Algebra

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The commutator of two bounded continuous linear operators. -/
def operatorComm (A B : H →L[ℝ] H) : H →L[ℝ] H :=
  A.comp B - B.comp A

theorem continuous_comm :
    Continuous (fun p : (H →L[ℝ] H) × (H →L[ℝ] H) => operatorComm p.1 p.2) := by
  unfold operatorComm
  continuity

/-- The scalar-plus-nilpotent operator carried by a monodromy datum. -/
def monodromyOperator (M : ContinuousMonodromyOperator H) : H →L[ℝ] H :=
  M.lambda • ContinuousLinearMap.id ℝ H + M.N

/-- The scalar part of monodromy does not contribute to a Dirac commutator. -/
theorem monodromy_commutator_reduction
    (M : ContinuousMonodromyOperator H) (D : H →L[ℝ] H) :
    operatorComm D (monodromyOperator M) = operatorComm D M.N := by
  ext x
  simp only [operatorComm, monodromyOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [map_add, map_smul]
  abel

end InfoGeometry.Physics.Algebra
