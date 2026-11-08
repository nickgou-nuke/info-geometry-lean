import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

namespace InfoGeometry.OperatorAlgebra

variable (Algebra : Type*) [CStarAlgebra Algebra]

def IsTangentFunctional (functional : StrongDual ℂ Algebra) : Prop :=
  (∀ element, functional (star element) = star (functional element)) ∧ functional 1 = 0

def stateTangentSubmodule : Submodule ℝ (StrongDual ℂ Algebra) where
  carrier := {functional | IsTangentFunctional Algebra functional}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro first second first_tangent second_tangent
    constructor
    · intro element
      simp [first_tangent.1 element, second_tangent.1 element]
    · simp [first_tangent.2, second_tangent.2]
  smul_mem' := by
    intro scalar functional tangent
    constructor
    · intro element
      simp [tangent.1 element]
    · simp [tangent.2]

abbrev StateTangentVector := ↥(stateTangentSubmodule Algebra)

theorem isClosed_stateTangentSubmodule :
    IsClosed (stateTangentSubmodule Algebra : Set (StrongDual ℂ Algebra)) := by
  have evaluation (element : Algebra) :
      Continuous (fun functional : StrongDual ℂ Algebra => functional element) :=
    (ContinuousLinearMap.apply ℂ ℂ element).continuous
  have self_adjoint : IsClosed {functional : StrongDual ℂ Algebra |
      ∀ element, functional (star element) = star (functional element)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun element => isClosed_eq (evaluation (star element))
      (continuous_star.comp (evaluation element)))
  exact self_adjoint.inter (isClosed_eq (evaluation 1) continuous_const)

instance : CompleteSpace (StateTangentVector Algebra) :=
  (isClosed_stateTangentSubmodule Algebra).isComplete.completeSpace_coe

theorem tangent_vanishes_on_scalar (tangent : StateTangentVector Algebra) (scalar : ℂ) :
    tangent.val (algebraMap ℂ Algebra scalar) = 0 := by
  rw [_root_.Algebra.algebraMap_eq_smul_one, map_smul, tangent.property.2, smul_zero]

end InfoGeometry.OperatorAlgebra
