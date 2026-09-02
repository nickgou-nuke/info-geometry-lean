import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SugawaraFiveGradingObstruction

/-! Canonical singleton representatives for Heisenberg modes in the filtered
colimit.  The Virasoro/Sugawara action remains the existing current owner. -/
noncomputable section
namespace InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

open CategoryTheory CategoryTheory.Limits
open VirasoroProject
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SugawaraFiveGradingObstruction

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

noncomputable def heisenbergColimitMode (k : ℤ) :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) :=
  let s : Finset (Option ℤ) := {some k}
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    ⟨HeisenbergAlgebra.jgen 𝕜 k, by
      simpa [s] using heisenberg_mode_stage_contains_jgen (𝕜 := 𝕜) k⟩
  (colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x

theorem heisenbergFiniteModeColimitMap_mode (k : ℤ) :
    (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      HeisenbergAlgebra.jgen 𝕜 k := by
  let s : Finset (Option ℤ) := {some k}
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    ⟨HeisenbergAlgebra.jgen 𝕜 k, by
      simpa [s] using heisenberg_mode_stage_contains_jgen (𝕜 := 𝕜) k⟩
  change (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
      ((colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x) = _
  have h := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s
  have h' := congrArg (fun f => f.hom x) h
  simpa [heisenbergFiniteModeCocone, x] using h'

@[simp] theorem heisenbergFiniteModeColimitEquiv_mode (k : ℤ) :
    heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      HeisenbergAlgebra.jgen 𝕜 k :=
  heisenbergFiniteModeColimitMap_mode (𝕜 := 𝕜) k

theorem colimit_mode_map_packet (k : ℤ) :
    (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      HeisenbergAlgebra.jgen 𝕜 k) ∧
    (heisenbergFiniteModeColimitMap (𝕜 := 𝕜)).hom
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      HeisenbergAlgebra.jgen 𝕜 k := by
  exact ⟨heisenbergFiniteModeColimitEquiv_mode (𝕜 := 𝕜) k,
    heisenbergFiniteModeColimitMap_mode (𝕜 := 𝕜) k⟩

theorem chargedFock_vira_mode_shift
    (α : 𝕜) (n m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m) =
        -m • (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (n + m) := by
  rw [CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply]
  exact sugawara_current_mode_shift
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).trunc
    (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).comm n m

theorem chargedFock_colimit_mode_representation_readout
    (α : 𝕜) (m : ℤ) :
    chargedFockSpaceHeisenbergMode 𝕜 α m =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  rfl

end InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
