import InfoGeometry.Categorical.ZornColimitStageAction
import InfoGeometry.Canonical.CanonicalZornBraidTransport

noncomputable section

namespace InfoGeometry.Categorical.ZornColimitBraidAction

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Categorical.ZornUHFColimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary (BitWord)
open InfoGeometry.Canonical.CanonicalZornBraidTransport
open InfoGeometry.Physics.QCDCanonicalComplexZornBridge (CanonicalZorn)
open InfoGeometry.Physics.YangBaxterZornBridge (zornPhi)
open InfoGeometry.Physics.B3PresentedGroup (B3)

theorem colimit_end_ext (first second : Module.End ℂ ZornColimit)
    (on_stage : ∀ stage (state : ZornStage stage),
      first ((colimit.ι zornStageFunctor stage).hom state) =
        second ((colimit.ι zornStageFunctor stage).hom state)) :
    first = second := by
  have equality : (ModuleCat.ofHom first : ZornColimit ⟶ ZornColimit) =
      ModuleCat.ofHom second := by
    apply colimit.hom_ext
    intro stage
    ext state
    exact on_stage stage state
  exact congrArg ModuleCat.Hom.hom equality

theorem colimit_action_unique
    (candidate : B3 →* (Module.End ℂ ZornColimit)ˣ)
    (lifts : ∀ braid stage (state : ZornStage stage),
      (candidate braid : Module.End ℂ ZornColimit)
          ((colimit.ι zornStageFunctor stage).hom state) =
        (colimit.ι zornStageFunctor stage).hom
          (zornStagePointwise (zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) stage state)) :
    candidate = zornColimitBraidRepresentation := by
  apply MonoidHom.ext
  intro braid
  apply Units.ext
  apply colimit_end_ext
  intro stage state
  exact (lifts braid stage state).trans
    (zornColimitBraidRepresentation_on_stage braid stage state).symm

theorem existsUnique_colimit_action :
    ∃! action : B3 →* (Module.End ℂ ZornColimit)ˣ,
      ∀ braid stage (state : ZornStage stage),
        (action braid : Module.End ℂ ZornColimit)
            ((colimit.ι zornStageFunctor stage).hom state) =
          (colimit.ι zornStageFunctor stage).hom
            (zornStagePointwise (zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) stage state) := by
  refine ⟨zornColimitBraidRepresentation, zornColimitBraidRepresentation_on_stage, ?_⟩
  intro candidate lifts
  exact colimit_action_unique candidate lifts

theorem canonical_stage_intertwines (braid : B3) (stage : ℕ)
    (state : BitWord stage → CanonicalZorn) :
    zornStagePointwise (zornPhi braid : Matrix (Fin 8) (Fin 8) ℂ) stage
        (fun word => coordinates (state word)) =
      fun word => coordinates
        ((braidRepresentation braid : Module.End ℂ CanonicalZorn) (state word)) := by
  funext word
  exact (coordinates_intertwines braid (state word)).symm

theorem canonical_colimit_intertwines (braid : B3) (stage : ℕ)
    (state : BitWord stage → CanonicalZorn) :
    (zornColimitBraidRepresentation braid : Module.End ℂ ZornColimit)
        ((colimit.ι zornStageFunctor stage).hom (fun word => coordinates (state word))) =
      (colimit.ι zornStageFunctor stage).hom
        (fun word => coordinates
          ((braidRepresentation braid : Module.End ℂ CanonicalZorn) (state word))) := by
  rw [zornColimitBraidRepresentation_on_stage, canonical_stage_intertwines]

end InfoGeometry.Categorical.ZornColimitBraidAction
