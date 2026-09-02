import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.SugawaraFiveGradingObstruction
import InfoGeometry.OperatorAlgebra.ModeShiftInterface

/-! Canonical singleton representatives for Heisenberg modes in the filtered
colimit.  The Virasoro/Sugawara action remains the existing current owner. -/
noncomputable section
namespace InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

open CategoryTheory CategoryTheory.Limits
open VirasoroProject
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.SugawaraFiveGradingObstruction
open InfoGeometry.OperatorAlgebra

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

theorem chargedFock_hasModeShift (α : 𝕜) :
    HasModeShift
      (fun n X =>
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator X)
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J
      (fun n m => n + m)
      (fun _ m => (-m : 𝕜)) := by
  intro n m
  simpa using chargedFock_vira_mode_shift α n m

theorem chargedFock_vira_mapsToModeSpanGrade (α : 𝕜) :
    MapsToGrade
      (ModeSpanGrade (R := 𝕜)
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J))
      (fun n X =>
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator X)
      (fun n m => n + m) := by
  apply HasModeShift.mapsToModeSpanGrade
    (R := 𝕜)
    (A := VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
      VirasoroProject.ChargedFockSpace 𝕜 α)
    (ι := ℤ)
    (hlinear := by
      intro n c X
      change _ * (c • X) - (c • X) * _ = _
      ext v
      simp [Algebra.smul_def]
      change _ = c •
        (((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)) (X v) -
          X ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
            (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n) v))
      rw [smul_sub])
  exact chargedFock_hasModeShift (𝕜 := 𝕜) α

theorem chargedFock_vira_mode_mem_shifted_span
    (α : 𝕜) (n m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m) ∈
      ModeSpanGrade (R := 𝕜)
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J) (n + m) := by
  apply HasModeShift.mode_mem_shifted_grade
    (chargedFock_hasModeShift (𝕜 := 𝕜) α)
  intro i c
  exact ⟨c, rfl⟩

theorem chargedFock_double_vira_mode_shift (α : 𝕜) (n m : ℤ) :
    ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
      (((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
          (VirasoroProject.VirasoroAlgebra.lgen 𝕜 n)).commutator
        ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m)) =
      (m * (n + m) : 𝕜) •
        (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J (n + (n + m)) := by
  have h := HasModeShift.comp
    (R := 𝕜)
    (A := VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
      VirasoroProject.ChargedFockSpace 𝕜 α)
    (ι := ℤ)
    (action₁ := fun r X =>
      ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator X)
    (action₂ := fun r X =>
      ((chargedFockSpaceCurrentHeisenbergRep 𝕜 α).currentSugawaraRepresentation
        (VirasoroProject.VirasoroAlgebra.lgen 𝕜 r)).commutator X)
    (mode := (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J)
    (shift₁ := fun r q => r + q)
    (shift₂ := fun r q => r + q)
    (coeff₁ := fun _ q => (-q : 𝕜))
    (coeff₂ := fun _ q => (-q : 𝕜))
    (hlinear := by
      intro r c X
      change _ * (c • X) - (c • X) * _ = c • (_ * X - X * _)
      ext v
      simp [Algebra.smul_def]
      rw [smul_sub])
    (chargedFock_hasModeShift (𝕜 := 𝕜) α)
    (chargedFock_hasModeShift (𝕜 := 𝕜) α)
  have hh := h n m
  ring_nf at hh ⊢
  have hs : (m : 𝕜) * (n + m : 𝕜) =
      (m : 𝕜) * n + (m : 𝕜) ^ 2 := by
    ring
  push_cast at hh
  rw [hs] at hh
  exact hh

theorem chargedFock_colimit_mode_representation_readout
    (α : 𝕜) (m : ℤ) :
    chargedFockSpaceHeisenbergMode 𝕜 α m =
      (chargedFockSpaceCurrentHeisenbergRep 𝕜 α).J m := by
  rfl

end InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
