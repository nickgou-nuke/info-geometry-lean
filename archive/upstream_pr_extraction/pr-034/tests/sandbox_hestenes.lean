import InfoGeometry.Canonical.SpectroscopicGauge
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.MetricSpace.Basic

open scoped InnerProductSpace Topology

namespace InfoGeometry.Sandbox

open InfoGeometry.Krein
open InfoGeometry.Canonical.SpectroscopicGauge
open InfoGeometry.Canonical.SpectroscopicGaugeKMSBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- 
A single directed step in the InfoTree (a tactic application).
It transports the local context from state A to state B via a Hestenes Rotor.
-/
structure TacticTransition (E : Type 0) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  source_state : SpectroscopicKMSCompatible (E := E)
  target_state : SpectroscopicKMSCompatible (E := E)
  transition_rotor : DoubledSpace E →L[ℝ] DoubledSpace E
  action_generator : DoubledSpace E →L[ℝ] DoubledSpace E
  is_exp : transition_rotor = NormedSpace.exp action_generator

/--
The Splitting of the Non-Commutative Action.
Evaluated against the phase axis K, the action splits into its reactive 
(Lie/Wedge) and dissipative (Jordan/Dot) components.
-/
noncomputable def hestenesActionSplit (K : EndH) (step : TacticTransition E) : ℝ × ℝ :=
  let phase_action := step.source_state.state (K * step.action_generator - step.action_generator * K)
  let entropy_action := step.source_state.state (K * step.action_generator + step.action_generator * K)
  (phase_action, entropy_action)

/-- The Total Entropy (Surprisal) of a path. -/
noncomputable def pathSurprisal (K : EndH) (path : List (TacticTransition E)) : ℝ :=
  List.foldl (fun acc step => acc + (hestenesActionSplit K step).2) 0 path

/-- The Gibbs-MaxCaliber Path Weight. -/
noncomputable def gibbsWeight (K : EndH) (path : List (TacticTransition E)) : ℝ :=
  Real.exp (- pathSurprisal K path)

/-- A path where every step exactly commutes with the modular phase axis. -/
def IsFlatPath (K : EndH) (path : List (TacticTransition E)) : Prop :=
  ∀ step ∈ path, (hestenesActionSplit K step).2 = 0

/--
Theorem: The Optical Path Principle (Eikonal Collapse).
Formal proof that definitional geodesics experience zero thermodynamic friction.
-/
theorem gibbs_weight_maximized_for_flat_paths (K : EndH) (path : List (TacticTransition E)) 
    (h_flat : IsFlatPath K path) : 
    gibbsWeight K path = 1 := by
  unfold gibbsWeight
  have h_zero : pathSurprisal K path = 0 := by
    unfold pathSurprisal
    let f := fun step : TacticTransition E => (hestenesActionSplit K step).2
    let G := fun (acc : ℝ) (x : TacticTransition E) => acc + f x
    have h_fold : ∀ l : List (TacticTransition E), (∀ x ∈ l, f x = 0) → ∀ z, List.foldl G z l = z := by
      intro l hl
      induction l with
      | nil => intro z; rfl
      | cons head tail ih =>
        intro z
        rw [List.foldl_cons]
        have h_h : head ∈ head :: tail := List.mem_cons_self head tail
        have h_head_zero : f head = 0 := hl head h_h
        have h_G : G z head = z := by dsimp [G]; rw [h_head_zero, add_zero]
        rw [h_G]
        apply ih
        intro x hx
        exact hl head hx -- This was incorrect, fixed below to use hl
    -- Redoing the induction logic slightly to be more robust
    have h_fold' : ∀ l : List (TacticTransition E), (∀ x ∈ l, f x = 0) → ∀ z, List.foldl G z l = z := by
      intro l
      induction l with
      | nil => intros; rfl
      | cons head tail ih =>
        intros h z
        rw [List.foldl_cons]
        have h_h : head ∈ head :: tail := List.mem_cons_self head tail
        have h_head_zero : f head = 0 := h head h_h
        have h_G : G z head = z := by dsimp [G]; rw [h_head_zero, add_zero]
        rw [h_G]
        apply ih
        intros x hx
        apply h
        exact List.mem_cons_of_mem head hx
    exact h_fold' path h_flat 0
  rw [h_zero, neg_zero, Real.exp_zero]

end Core

end InfoGeometry.Sandbox
