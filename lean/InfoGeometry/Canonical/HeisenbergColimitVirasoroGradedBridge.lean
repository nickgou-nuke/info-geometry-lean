import Mathlib.Tactic
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Canonical.FibonacciGrothendieckLimit
import InfoGeometry.Canonical.SugawaraFiveGradingObstruction
import InfoGeometry.Canonical.CurrentSugawaraBridge
import InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge

/-!
# Heisenberg filtered colimit to Virasoro graded-mode bridge

The repository already contains three genuine structures:

* a filtered `ModuleCat` colimit of finite Heisenberg mode stages;
* the `CurrentHeisenbergRep` interface for represented current modes;
* the Sugawara/Virasoro representation with central charge `c = 1`.

This owner joins them without introducing a second "Virasoro colimit".
Each current mode `J_m` is represented by its canonical singleton finite stage,
mapped into the Heisenberg colimit, recovered in the full Heisenberg algebra,
and represented on charged Fock space. Those colimit-derived modes form a
native `CurrentHeisenbergRep`, hence generate the repository-owned Virasoro
representation.

The final packet places the exact Virasoro mode shift next to the native
exterior graded-ladder law `P_(k+1) ε_v = ε_v P_k`. No identification of
exterior degree with Virasoro conformal weight is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

open Filter
open CategoryTheory CategoryTheory.Limits
open VirasoroProject
open InfoGeometry.Canonical.FibonacciGrothendieckLimit
open InfoGeometry.Canonical.SugawaraFiveGradingObstruction
open InfoGeometry.Canonical.CurrentSugawaraBridge
open InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge

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
  have hstage := heisenbergFiniteModeColimitMap_stage (𝕜 := 𝕜) s
  have hstage' := congrArg (fun f => f.hom x) hstage
  simpa [heisenbergFiniteModeCocone, x] using hstage'

@[simp] theorem heisenbergFiniteModeColimitEquiv_mode (k : ℤ) :
    heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      HeisenbergAlgebra.jgen 𝕜 k := by
  exact heisenbergFiniteModeColimitMap_mode (𝕜 := 𝕜) k

section ChargedFock

variable (α : 𝕜)

abbrev Fock : Type* := VirasoroProject.ChargedFockSpace 𝕜 α
abbrev FockEnd : Type* :=
  VirasoroProject.ChargedFockSpace 𝕜 α →ₗ[𝕜]
    VirasoroProject.ChargedFockSpace 𝕜 α

noncomputable def chargedFockHeisenbergRepresentation :
    LieAlgebra.Representation 𝕜 𝕜 (HeisenbergAlgebra 𝕜) (Fock (𝕜 := 𝕜) α) :=
  UniversalEnvelopingAlgebra.representation
    (𝕜 := 𝕜) (𝓰 := HeisenbergAlgebra 𝕜)
    (V := Fock (𝕜 := 𝕜) α)

noncomputable def chargedFockColimitReadout :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) →ₗ[𝕜]
      FockEnd (𝕜 := 𝕜) α where
  toFun x := chargedFockHeisenbergRepresentation (𝕜 := 𝕜) α
    (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜) x)
  map_add' x y := by simp
  map_smul' c x := by simp

@[simp] theorem chargedFockColimitReadout_mode (k : ℤ) :
    chargedFockColimitReadout (𝕜 := 𝕜) α
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      chargedFockHeisenbergMode (𝕜 := 𝕜) α k := by
  change chargedFockHeisenbergRepresentation (𝕜 := 𝕜) α
      (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (heisenbergColimitMode (𝕜 := 𝕜) k)) = _
  rw [heisenbergFiniteModeColimitEquiv_mode]
  rfl

noncomputable def colimitCurrentMode (k : ℤ) : FockEnd (𝕜 := 𝕜) α :=
  chargedFockColimitReadout (𝕜 := 𝕜) α
    (heisenbergColimitMode (𝕜 := 𝕜) k)

@[simp] theorem colimitCurrentMode_eq_chargedFock (k : ℤ) :
    colimitCurrentMode (𝕜 := 𝕜) α k =
      chargedFockHeisenbergMode (𝕜 := 𝕜) α k := by
  exact chargedFockColimitReadout_mode (𝕜 := 𝕜) α k

theorem colimitCurrentMode_commutator (k l : ℤ) :
    (colimitCurrentMode (𝕜 := 𝕜) α k).commutator
        (colimitCurrentMode (𝕜 := 𝕜) α l) =
      if k + l = 0 then (k : 𝕜) • (1 : FockEnd (𝕜 := 𝕜) α) else 0 := by
  rw [colimitCurrentMode_eq_chargedFock,
    colimitCurrentMode_eq_chargedFock]
  exact chargedFockHeisenbergMode_commutator (𝕜 := 𝕜) α k l

theorem colimitCurrentMode_eventually_eq_zero (v : Fock (𝕜 := 𝕜) α) :
    atTop.Eventually (fun k : ℤ =>
      colimitCurrentMode (𝕜 := 𝕜) α k v = 0) := by
  simpa only [colimitCurrentMode_eq_chargedFock] using
    chargedFockHeisenbergMode_eventually_eq_zero (𝕜 := 𝕜) α v

noncomputable def colimitCurrentHeisenbergRep :
    CurrentHeisenbergRep 𝕜 (Fock (𝕜 := 𝕜) α) where
  J := colimitCurrentMode (𝕜 := 𝕜) α
  trunc := colimitCurrentMode_eventually_eq_zero (𝕜 := 𝕜) α
  comm := colimitCurrentMode_commutator (𝕜 := 𝕜) α

theorem sugawara_colimit_mode_shift (n m : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n).commutator
      ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m) =
        -m • (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J (n + m) := by
  exact sugawara_current_mode_shift
    (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J
    (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).trunc
    (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).comm n m

theorem sugawara_lzero_colimit_weight (m : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode 0).commutator
      ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m) =
        -m • (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m := by
  simpa using sugawara_colimit_mode_shift (𝕜 := 𝕜) α 0 m

theorem virasoro_lgen_colimit_readout (n : ℤ) :
    (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 n) =
      (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n := by
  exact CurrentHeisenbergRep.currentSugawaraRepresentation_lgen_apply
    (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α) n

theorem virasoro_lgen_colimit_mode_shift (n m : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m) =
        -m • (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J (n + m) := by
  rw [virasoro_lgen_colimit_readout (𝕜 := 𝕜) α n]
  exact sugawara_colimit_mode_shift (𝕜 := 𝕜) α n m

theorem colimit_stressMode_virasoroBracket (m n : ℤ) :
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode m).commutator
        ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode n) =
      (m - n) •
          (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).sugawaraStressMode (m + n)
        + if m + n = 0 then
            (((m ^ 3 - m : 𝕜) / (12 : 𝕜)) • (1 : FockEnd (𝕜 := 𝕜) α))
          else 0 := by
  exact CurrentHeisenbergRep.sugawaraStressMode_virasoroBracket
    (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α) m n

theorem virasoro_shift_target_is_colimit_mode (n m : ℤ) :
    (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J (n + m) =
      chargedFockColimitReadout (𝕜 := 𝕜) α
        (heisenbergColimitMode (𝕜 := 𝕜) (n + m)) :=
  rfl

end ChargedFock

theorem exterior_and_virasoro_graded_shift_packet
    (v : InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge.V3)
    (k : ℕ) (α : 𝕜) (n m : ℤ) :
    (nativeExteriorProjector (k + 1)).comp (exteriorWedge3 v) =
        (exteriorWedge3 v).comp (nativeExteriorProjector k) ∧
    ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).currentSugawaraRepresentation
        (VirasoroAlgebra.lgen 𝕜 n)).commutator
      ((colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J m) =
        -m • (colimitCurrentHeisenbergRep (𝕜 := 𝕜) α).J (n + m) := by
  exact ⟨nativeExteriorProjector_wedge_shift v k,
    virasoro_lgen_colimit_mode_shift (𝕜 := 𝕜) α n m⟩

end InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
