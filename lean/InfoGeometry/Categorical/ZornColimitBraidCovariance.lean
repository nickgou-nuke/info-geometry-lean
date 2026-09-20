import InfoGeometry.Categorical.ZornColimitBraidAction

noncomputable section

namespace InfoGeometry.Categorical.ZornColimitBraidCovariance

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Physics.B3PresentedGroup (B3 B3Gen GL8)
open InfoGeometry.Physics.YangBaxterZornBridge (zornPhi)
open InfoGeometry.Categorical.ZornUHFColimit
open InfoGeometry.Categorical.ZornColimitBraidAction (colimit_end_ext)

theorem stage_braid_equivariant (braid : B3) {source target : ℕ}
    (bond : source ≤ target) :
    (stageBondLinear bond).comp
        (zornStagePointwise (zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) source) =
      (zornStagePointwise (zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) target).comp
        (stageBondLinear bond) := by
  ext state word
  rfl

theorem conjugacy_of_generator_conjugacy {GroupCarrier : Type*} [Group GroupCarrier]
    (first second : B3 →* GroupCarrier) (transport : GroupCarrier)
    (on_generators : ∀ generator : B3Gen,
      transport * first (PresentedGroup.of generator) * transport⁻¹ =
        second (PresentedGroup.of generator)) (braid : B3) :
    transport * first braid * transport⁻¹ = second braid := by
  have equality : (MulAut.conj transport).toMonoidHom.comp first = second := by
    apply PresentedGroup.ext
    intro generator
    exact on_generators generator
  exact DFunLike.congr_fun equality braid

theorem colimit_action_unique_of_generators
    (candidate : B3 →* (Module.End ℂ ZornColimit)ˣ)
    (on_generators : ∀ (generator : B3Gen) stage (state : ZornStage stage),
      (candidate (PresentedGroup.of generator) : Module.End ℂ ZornColimit)
          ((colimit.ι zornStageFunctor stage).hom state) =
        (colimit.ι zornStageFunctor stage).hom
          (zornStagePointwise
            (zornPhi (PresentedGroup.of generator) : Matrix (Fin 8) (Fin 8) ℂ)
            stage state)) :
    candidate = zornColimitBraidRepresentation := by
  apply PresentedGroup.ext
  intro generator
  apply Units.ext
  apply colimit_end_ext
  intro stage state
  exact (on_generators generator stage state).trans
    (zornColimitBraidRepresentation_on_stage (PresentedGroup.of generator) stage state).symm

theorem colimit_braid_covariance
    (transport : GL8) (target : B3 →* GL8)
    (on_generators : ∀ generator : B3Gen,
      transport * zornPhi (PresentedGroup.of generator) * transport⁻¹ =
        target (PresentedGroup.of generator)) (braid : B3) :
    (Units.map zornColimitMatrixAction) transport * zornColimitBraidRepresentation braid *
        ((Units.map zornColimitMatrixAction) transport)⁻¹ =
      (Units.map zornColimitMatrixAction) (target braid) := by
  have equality := congrArg (Units.map zornColimitMatrixAction)
    (conjugacy_of_generator_conjugacy zornPhi target transport on_generators braid)
  simpa only [map_mul, map_inv, zornColimitBraidRepresentation, MonoidHom.comp_apply]
    using equality

theorem colimit_braid_covariance_on_stage
    (transport : GL8) (target : B3 →* GL8)
    (on_generators : ∀ generator : B3Gen,
      transport * zornPhi (PresentedGroup.of generator) * transport⁻¹ =
        target (PresentedGroup.of generator))
    (braid : B3) (stage : ℕ) (state : ZornStage stage) :
    (((Units.map zornColimitMatrixAction) transport *
        zornColimitBraidRepresentation braid *
        ((Units.map zornColimitMatrixAction) transport)⁻¹ :
          (Module.End ℂ ZornColimit)ˣ) : Module.End ℂ ZornColimit)
          ((colimit.ι zornStageFunctor stage).hom state) =
      (colimit.ι zornStageFunctor stage).hom
        (zornStagePointwise (target braid : Matrix (Fin 8) (Fin 8) ℂ) stage state) := by
  rw [colimit_braid_covariance transport target on_generators braid]
  exact zornColimitEnd_on_stage
    (zornStagePointwiseNatTrans (target braid : Matrix (Fin 8) (Fin 8) ℂ)) stage state

end InfoGeometry.Categorical.ZornColimitBraidCovariance
