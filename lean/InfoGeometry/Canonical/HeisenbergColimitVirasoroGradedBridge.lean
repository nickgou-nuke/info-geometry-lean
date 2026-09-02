import Mathlib.Tactic
import InfoGeometry.Canonical.HeisenbergFiniteModeColimit
import InfoGeometry.Canonical.FibonacciGrothendieckLimit
import InfoGeometry.Canonical.SugawaraFiveGradingObstruction
import InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge

/-!
# Heisenberg filtered colimit to Virasoro graded-mode bridge

The repository already contains two genuine structures:

* a filtered `ModuleCat` colimit of finite Heisenberg mode stages;
* a Sugawara representation satisfying `[L_n,J_m] = -m J_(n+m)`.

This owner joins them without introducing a second "Virasoro colimit".
Each abstract current mode `J_m` is represented by its canonical singleton
finite stage, mapped into the Heisenberg colimit, recovered in the full
Heisenberg algebra, and then represented on charged Fock space.  The Sugawara
mode-shift theorem therefore acts on modes obtained from the categorical
colimit itself.

The final packet places this next to the native exterior graded-ladder law
`P_(k+1) ε_v = ε_v P_k`.  No identification of exterior degree with Virasoro
conformal weight is asserted; both are proved instances of graded shift
operators on their respective carriers.
-/

noncomputable section

namespace InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge

open Filter
open CategoryTheory CategoryTheory.Limits
open VirasoroProject
open InfoGeometry.Canonical.FibonacciGrothendieckLimit
open InfoGeometry.Canonical.SugawaraFiveGradingObstruction
open InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- Canonical colimit representative of the Heisenberg current mode `J_k`,
coming from the singleton finite stage `{some k}`. -/
noncomputable def heisenbergColimitMode (k : ℤ) :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) :=
  let s : Finset (Option ℤ) := {some k}
  let x : heisenbergFiniteModeStage (𝕜 := 𝕜) s :=
    ⟨HeisenbergAlgebra.jgen 𝕜 k, by
      simpa [s] using heisenberg_mode_stage_contains_jgen (𝕜 := 𝕜) k⟩
  (colimit.ι (heisenbergFiniteModeDiagram (𝕜 := 𝕜)) s).hom x

/-- The filtered-colimit comparison map recovers the original abstract
Heisenberg generator from its canonical singleton-stage representative. -/
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

/-- The colimit equivalence sends the canonical mode representative to `J_k`. -/
@[simp] theorem heisenbergFiniteModeColimitEquiv_mode (k : ℤ) :
    heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      HeisenbergAlgebra.jgen 𝕜 k := by
  exact heisenbergFiniteModeColimitMap_mode (𝕜 := 𝕜) k

section ChargedFock

variable (α : 𝕜)

abbrev Fock := VirasoroProject.ChargedFockSpace 𝕜 α
abbrev FockEnd := Fock (𝕜 := 𝕜) α →ₗ[𝕜] Fock (𝕜 := 𝕜) α

/-- Charged-Fock representation of the full abstract Heisenberg algebra. -/
noncomputable def chargedFockHeisenbergRepresentation :
    LieAlgebra.Representation 𝕜 𝕜 (HeisenbergAlgebra 𝕜) (Fock (𝕜 := 𝕜) α) :=
  UniversalEnvelopingAlgebra.representation
    (𝕜 := 𝕜) (𝓰 := HeisenbergAlgebra 𝕜)
    (V := Fock (𝕜 := 𝕜) α)

/-- Read an element of the filtered Heisenberg colimit as an operator on the
charged Fock space. -/
noncomputable def chargedFockColimitReadout :
    (heisenbergFiniteModeColimit (𝕜 := 𝕜) : Type _) →ₗ[𝕜]
      FockEnd (𝕜 := 𝕜) α :=
  (chargedFockHeisenbergRepresentation (𝕜 := 𝕜) α).comp
    (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)).toLinearMap

/-- The categorical colimit representative of mode `k` reads exactly as the
repository-owned charged-Fock Heisenberg current operator. -/
@[simp] theorem chargedFockColimitReadout_mode (k : ℤ) :
    chargedFockColimitReadout (𝕜 := 𝕜) α
        (heisenbergColimitMode (𝕜 := 𝕜) k) =
      chargedFockHeisenbergMode (𝕜 := 𝕜) α k := by
  change chargedFockHeisenbergRepresentation (𝕜 := 𝕜) α
      (heisenbergFiniteModeColimitEquiv (𝕜 := 𝕜)
        (heisenbergColimitMode (𝕜 := 𝕜) k)) = _
  rw [heisenbergFiniteModeColimitEquiv_mode]
  rfl

/-- The colimit-derived mode family.  It is definitionally the charged-Fock
readout of canonical singleton-stage colimit representatives. -/
noncomputable def colimitCurrentMode (k : ℤ) : FockEnd (𝕜 := 𝕜) α :=
  chargedFockColimitReadout (𝕜 := 𝕜) α
    (heisenbergColimitMode (𝕜 := 𝕜) k)

@[simp] theorem colimitCurrentMode_eq_chargedFock (k : ℤ) :
    colimitCurrentMode (𝕜 := 𝕜) α k =
      chargedFockHeisenbergMode (𝕜 := 𝕜) α k := by
  exact chargedFockColimitReadout_mode (𝕜 := 𝕜) α k

/-- The colimit-derived current modes satisfy the exact Heisenberg central
commutator required by Sugawara. -/
theorem colimitCurrentMode_commutator (k l : ℤ) :
    (colimitCurrentMode (𝕜 := 𝕜) α k).commutator
        (colimitCurrentMode (𝕜 := 𝕜) α l) =
      if k + l = 0 then (k : 𝕜) • (1 : FockEnd (𝕜 := 𝕜) α) else 0 := by
  rw [colimitCurrentMode_eq_chargedFock,
    colimitCurrentMode_eq_chargedFock]
  exact chargedFockHeisenbergMode_commutator (𝕜 := 𝕜) α k l

/-- The colimit-derived current family is locally truncated on every charged
Fock vector, so the Sugawara sums are well-defined. -/
theorem colimitCurrentMode_eventually_eq_zero (v : Fock (𝕜 := 𝕜) α) :
    atTop.Eventually (fun k : ℤ =>
      colimitCurrentMode (𝕜 := 𝕜) α k v = 0) := by
  simpa [colimitCurrentMode_eq_chargedFock] using
    chargedFockHeisenbergMode_eventually_eq_zero (𝕜 := 𝕜) α v

/-- Sugawara/Virasoro acts on the categorical-colimit current modes by the
exact shift law `[L_n,J_m] = -m J_(n+m)`. -/
theorem sugawara_colimit_mode_shift (n m : ℤ) :
    (sugawaraGen
        (colimitCurrentMode_eventually_eq_zero (𝕜 := 𝕜) α) n).commutator
      (colimitCurrentMode (𝕜 := 𝕜) α m) =
        -m • colimitCurrentMode (𝕜 := 𝕜) α (n + m) := by
  exact sugawara_current_mode_shift
    (colimitCurrentMode (𝕜 := 𝕜) α)
    (colimitCurrentMode_eventually_eq_zero (𝕜 := 𝕜) α)
    (colimitCurrentMode_commutator (𝕜 := 𝕜) α) n m

/-- The zero Sugawara mode grades every colimit current mode with eigenvalue
`-m`: `[L_0,J_m] = -m J_m`. -/
theorem sugawara_lzero_colimit_weight (m : ℤ) :
    (sugawaraGen
        (colimitCurrentMode_eventually_eq_zero (𝕜 := 𝕜) α) 0).commutator
      (colimitCurrentMode (𝕜 := 𝕜) α m) =
        -m • colimitCurrentMode (𝕜 := 𝕜) α m := by
  simpa using sugawara_colimit_mode_shift (𝕜 := 𝕜) α 0 m

/-- A Virasoro mode sends the colimit label `m` to the colimit label `n+m`.
This is the precise categorical mode-string statement: the target current again
comes from a canonical finite-stage representative in the same filtered
colimit. -/
theorem virasoro_shift_target_is_colimit_mode (n m : ℤ) :
    colimitCurrentMode (𝕜 := 𝕜) α (n + m) =
      chargedFockColimitReadout (𝕜 := 𝕜) α
        (heisenbergColimitMode (𝕜 := 𝕜) (n + m)) :=
  rfl

end ChargedFock

/-- Exterior creation and Virasoro/Sugawara current action are two native
instances of a graded shift law on different carriers.  This theorem packages
their exact statements without identifying the two gradings. -/
theorem exterior_and_virasoro_graded_shift_packet
    {V3 : Type*} [AddCommGroup V3] [Module ℝ V3]
    (v : InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge.V3)
    (k : ℕ)
    (α : 𝕜) (n m : ℤ) :
    (nativeExteriorProjector (k + 1)).comp (exteriorWedge3 v) =
        (exteriorWedge3 v).comp (nativeExteriorProjector k) ∧
    (sugawaraGen
        (colimitCurrentMode_eventually_eq_zero (𝕜 := 𝕜) α) n).commutator
      (colimitCurrentMode (𝕜 := 𝕜) α m) =
        -m • colimitCurrentMode (𝕜 := 𝕜) α (n + m) := by
  exact ⟨nativeExteriorProjector_wedge_shift v k,
    sugawara_colimit_mode_shift (𝕜 := 𝕜) α n m⟩

end InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
