import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import InfoGeometry.Algebraic.ProjectiveOperatorReadout

/-!
InfoGeometry/Algebraic/ProjectiveReadoutShadow.lean

Compatibility of projective operator readouts.
No coordinates. No complex substrate.
-/

noncomputable section

namespace InfoGeometry.Algebraic

open Filter
open scoped Topology

/--
A shadow/transport map between two projective operator readouts.

This is the operator-first replacement for coordinate comparison.

The fields say:
* the group actions are intertwined;
* the rotor cocycles are intertwined;
* the phase/readout maps are intertwined;
* the operator actions are intertwined.
-/
structure ProjectiveReadoutShadow
    {G₁ G₂ X₁ X₂ R₁ R₂ Op₁ Op₂ : Type*}
    [Group G₁] [Group G₂]
    [MulAction G₁ X₁] [MulAction G₂ X₂]
    [Group R₁] [Group R₂]
    [Group Op₁] [Group Op₂]
    (P₁ : ProjectiveOperatorReadout G₁ X₁ R₁ Op₁)
    (P₂ : ProjectiveOperatorReadout G₂ X₂ R₂ Op₂) where
  mapGroup : G₁ →* G₂
  mapBase : X₁ → X₂
  mapRotor : R₁ →* R₂
  mapOperator : Op₁ →* Op₂

  action_shadow :
    ∀ g x, mapBase (g • x) = mapGroup g • mapBase x

  cocycle_shadow :
    ∀ g x, mapRotor (P₁.cocycle g x) =
      P₂.cocycle (mapGroup g) (mapBase x)

  phase_shadow :
    ∀ r, mapOperator (P₁.phase r) =
      P₂.phase (mapRotor r)

  operator_shadow :
    ∀ g x, mapOperator (P₁.op g x) =
      P₂.op (mapGroup g) (mapBase x)

namespace ProjectiveReadoutShadow

variable
    {G₁ G₂ X₁ X₂ R₁ R₂ Op₁ Op₂ : Type*}
    [Group G₁] [Group G₂]
    [MulAction G₁ X₁] [MulAction G₂ X₂]
    [Group R₁] [Group R₂]
    [Group Op₁] [Group Op₂]
    {P₁ : ProjectiveOperatorReadout G₁ X₁ R₁ Op₁}
    {P₂ : ProjectiveOperatorReadout G₂ X₂ R₂ Op₂}

/--
A shadow map sends stabilizers to stabilizers.

This is the operator-level replacement for “the fixed point coordinates agree.”
-/
def mapStabilizer
    (M : ProjectiveReadoutShadow P₁ P₂)
    (x : X₁) :
    MulAction.stabilizer G₁ x →*
      MulAction.stabilizer G₂ (M.mapBase x) where
  toFun h :=
    ⟨M.mapGroup (h : G₁), by
      calc
        M.mapGroup (h : G₁) • M.mapBase x
            = M.mapBase ((h : G₁) • x) := by
                simpa using (M.action_shadow (h : G₁) x).symm
        _ = M.mapBase x := by
              rw [h.property]⟩
  map_one' := by
    ext
    simp
  map_mul' h k := by
    ext
    simp

/--
Stabilizer rotor anomalies are preserved by the shadow map.
-/
theorem stabilizerRotor_shadow
    (M : ProjectiveReadoutShadow P₁ P₂)
    (x : X₁)
    (h : MulAction.stabilizer G₁ x) :
    M.mapRotor ((P₁.stabilizerRotorHom x) h) =
      (P₂.stabilizerRotorHom (M.mapBase x)) (M.mapStabilizer x h) := by
  change
    M.mapRotor (P₁.cocycle (h : G₁) x) =
      P₂.cocycle (M.mapGroup (h : G₁)) (M.mapBase x)
  exact M.cocycle_shadow (h : G₁) x

/--
Operator-level stabilizer anomalies are preserved by the shadow map.
-/
theorem stabilizerPhase_shadow
    (M : ProjectiveReadoutShadow P₁ P₂)
    (x : X₁)
    (h : MulAction.stabilizer G₁ x) :
    M.mapOperator ((P₁.stabilizerPhaseHom x) h) =
      (P₂.stabilizerPhaseHom (M.mapBase x)) (M.mapStabilizer x h) := by
  change
    M.mapOperator (P₁.phase (P₁.cocycle (h : G₁) x)) =
      P₂.phase (P₂.cocycle (M.mapGroup (h : G₁)) (M.mapBase x))
  rw [M.phase_shadow, M.cocycle_shadow]

/--
Boundary/cusp/decompactification cocycle limits are preserved by a continuous
rotor shadow map.

This is the operator-first replacement for comparing coordinate rays.
-/
theorem boundaryCocycleLimit_shadow
    [TopologicalSpace R₁] [TopologicalSpace R₂]
    (M : ProjectiveReadoutShadow P₁ P₂)
    (hcont : Continuous M.mapRotor)
    {A : Type*}
    {L : Filter A}
    {ray : A → X₁}
    {g : G₁}
    {r : R₁}
    (hlim :
      Tendsto
        (fun a : A => P₁.cocycle g (ray a))
        L
        (𝓝 r)) :
    Tendsto
      (fun a : A =>
        P₂.cocycle (M.mapGroup g) (M.mapBase (ray a)))
      L
      (𝓝 (M.mapRotor r)) := by
  have hmap :
      Tendsto
        (fun a : A => M.mapRotor (P₁.cocycle g (ray a)))
        L
        (𝓝 (M.mapRotor r)) :=
    (hcont.tendsto r).comp hlim
  have hfun :
      (fun a : A =>
        P₂.cocycle (M.mapGroup g) (M.mapBase (ray a)))
      =
      (fun a : A =>
        M.mapRotor (P₁.cocycle g (ray a))) := by
    funext a
    exact (M.cocycle_shadow g (ray a)).symm
  rw [hfun]
  exact hmap

end ProjectiveReadoutShadow

end InfoGeometry.Algebraic
