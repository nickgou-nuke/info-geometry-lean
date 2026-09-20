import InfoGeometry.Categorical.ZornColimitBraidCovariance

noncomputable section

namespace InfoGeometry.Categorical.ZornColimitBraidCovarianceTests

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Physics.B3PresentedGroup (B3 GL8)
open InfoGeometry.Physics.YangBaxterZornBridge (zornPhi)
open InfoGeometry.Categorical.ZornUHFColimit
open InfoGeometry.Categorical.ZornColimitBraidAction
open InfoGeometry.Categorical.ZornColimitBraidCovariance

example (transport : GL8) (braid : B3) :
    (Units.map zornColimitMatrixAction) transport * zornColimitBraidRepresentation braid *
        ((Units.map zornColimitMatrixAction) transport)⁻¹ =
      (Units.map zornColimitMatrixAction) (transport * zornPhi braid * transport⁻¹) := by
  exact colimit_braid_covariance transport
    ((MulAut.conj transport).toMonoidHom.comp zornPhi) (fun _ => rfl) braid

example (transport : GL8) (braid : B3) (stage : ℕ) (state : ZornStage stage) :
    (((Units.map zornColimitMatrixAction) transport *
        zornColimitBraidRepresentation braid⁻¹ *
        ((Units.map zornColimitMatrixAction) transport)⁻¹ :
          (Module.End ℂ ZornColimit)ˣ) : Module.End ℂ ZornColimit)
          ((colimit.ι zornStageFunctor stage).hom state) =
      (colimit.ι zornStageFunctor stage).hom
        (zornStagePointwise
          (transport * zornPhi braid⁻¹ * transport⁻¹ : GL8) stage state) := by
  exact colimit_braid_covariance_on_stage transport
    ((MulAut.conj transport).toMonoidHom.comp zornPhi) (fun _ => rfl) braid⁻¹ stage state

example (braid : B3) (source target : ℕ) (bond : source ≤ target)
    (state : ZornStage source) :
    stageBondLinear bond
        (zornStagePointwise (zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) source state) =
      zornStagePointwise (zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) target
        (stageBondLinear bond state) := by
  exact LinearMap.congr_fun (stage_braid_equivariant braid bond) state

#print axioms existsUnique_colimit_action
#print axioms conjugacy_of_generator_conjugacy
#print axioms colimit_action_unique_of_generators
#print axioms colimit_braid_covariance
#print axioms colimit_braid_covariance_on_stage

end InfoGeometry.Categorical.ZornColimitBraidCovarianceTests
