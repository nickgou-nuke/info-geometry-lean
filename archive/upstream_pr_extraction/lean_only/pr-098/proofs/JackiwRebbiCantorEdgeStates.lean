import proofs.DiracResolventZeroModeTripotent
import proofs.GlideDiracSelectionRule
import proofs.SpectralCPTKleinBottle
import proofs.TrappedHarmonicModes
import proofs.ChiralConeAlgebraFinality

/-!
# Jackiw--Rebbi edge states on the Cantor/Klein boundary

This module formalizes the finite boundary-localization layer:

* the Klein/CPT glide fixes the critical core `σ = 1/2`;
* the glide-axis selection rule extinguishes odd modes;
* the Fourier--Mellin Dirac symbol has an exact boundary zero-mode at
  zero momentum;
* that zero-mode is the finite shadow of a Jackiw--Rebbi edge state trapped on
  the boundary defect.

The analytic PDE/domain-wall proof of the Jackiw--Rebbi mechanism is outside
this finite module; here we record the exact finite kernel and selection
arithmetic proved by the imported layers.
-/

noncomputable section

namespace JackiwRebbiCantorEdgeStates

open Complex

/-- Finite boundary Dirac operator on the Klein/CPT core. -/
def boundaryDirac (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  DiracResolventZeroModeTripotent.sI_minus_X s 0 0

/-- A concrete boundary zero-mode vector. -/
def boundaryZeroMode : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

@[simp] theorem boundaryDirac_core_apply (s : ℂ) :
    boundaryDirac s = DiracResolventZeroModeTripotent.sI_minus_X s 0 0 := rfl

/-- At the Jackiw--Rebbi core `s = 0`, the finite boundary operator vanishes. -/
theorem boundaryDirac_core_zero : boundaryDirac 0 = 0 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [boundaryDirac, DiracResolventZeroModeTripotent.sI_minus_X]
    · simp [boundaryDirac, DiracResolventZeroModeTripotent.sI_minus_X]
  · fin_cases j
    · simp [boundaryDirac, DiracResolventZeroModeTripotent.sI_minus_X]
    · simp [boundaryDirac, DiracResolventZeroModeTripotent.sI_minus_X]

/-- The core zero operator annihilates the boundary zero-mode vector. -/
theorem boundaryZeroMode_killed_by_core :
    (boundaryDirac 0).mulVec boundaryZeroMode = 0 := by
  rw [boundaryDirac_core_zero]
  ext i
  simp

/-- The Klein/CPT glide fixes the critical line `σ = 1/2`. -/
theorem klein_core_fixed_line (s : SpectralCPTKleinBottle.SpectralCylinder) :
    SpectralCPTKleinBottle.cptGlide s = s ↔
      SpectralCPTKleinBottle.criticalCore s :=
  SpectralCPTKleinBottle.cptGlide_fixed_iff_criticalCore s

/-- Odd glide-axis modes are extinguished. -/
theorem odd_glide_modes_extinguished {k : ℕ} {c : ℂ}
    (hodd : Odd k) (hrel : c = GlideDiracSelectionRule.pgPhase k * c) :
    c = 0 :=
  GlideDiracSelectionRule.pg_fixed_axis_extinction hodd hrel

/-- The local `3 + 1` parafermion edge-lane census. -/
inductive ParafermionEdgeLane where
  | singlet
  | colorOne
  | colorTwo
  | colorThree
  deriving DecidableEq, Repr

/-- At localization scale all four lanes are edge-state labels; asymptotic
observability is still decided by the wallpaper/GNS selection layer. -/
def laneIsEdgeState : ParafermionEdgeLane → Bool
  | .singlet => true
  | .colorOne => true
  | .colorTwo => true
  | .colorThree => true

def parafermionEdgeLanes : List ParafermionEdgeLane :=
  [.singlet, .colorOne, .colorTwo, .colorThree]

@[simp] theorem parafermion_edge_lane_count :
    parafermionEdgeLanes.length = 4 := rfl

/-- The four local parafermion lanes are all edge-state labels in this finite
Jackiw--Rebbi bookkeeping layer. -/
theorem all_parafermion_lanes_are_edge_states :
    laneIsEdgeState ParafermionEdgeLane.singlet = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorOne = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorTwo = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorThree = true := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Boundary localization combines the finite zero-mode equation with the Klein
core selection rule. -/
theorem jackiw_rebbi_edge_localization :
    boundaryDirac 0 = 0 ∧
    (boundaryDirac 0).mulVec boundaryZeroMode = 0 ∧
    (∀ (s : SpectralCPTKleinBottle.SpectralCylinder),
      SpectralCPTKleinBottle.cptGlide s = s ↔
        SpectralCPTKleinBottle.criticalCore s) ∧
    (∀ {k : ℕ} {c : ℂ}, Odd k → c = GlideDiracSelectionRule.pgPhase k * c → c = 0) ∧
    parafermionEdgeLanes.length = 4 ∧
    laneIsEdgeState ParafermionEdgeLane.singlet = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorOne = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorTwo = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorThree = true ∧
    ChiralConeAlgebraFinality.sPlus * ChiralConeAlgebraFinality.sPlus = 0 ∧
    ChiralConeAlgebraFinality.sMinus * ChiralConeAlgebraFinality.sMinus = 0 := by
  have hDirac : boundaryDirac 0 = 0 := boundaryDirac_core_zero
  have hMode : (boundaryDirac 0).mulVec boundaryZeroMode = 0 :=
    boundaryZeroMode_killed_by_core
  have hKlein :
      ∀ (s : SpectralCPTKleinBottle.SpectralCylinder),
        SpectralCPTKleinBottle.cptGlide s = s ↔
          SpectralCPTKleinBottle.criticalCore s :=
    klein_core_fixed_line
  have hOdd :
      ∀ {k : ℕ} {c : ℂ}, Odd k → c = GlideDiracSelectionRule.pgPhase k * c → c = 0 :=
    odd_glide_modes_extinguished
  have hLaneCount : parafermionEdgeLanes.length = 4 :=
    parafermion_edge_lane_count
  have hSinglet : laneIsEdgeState ParafermionEdgeLane.singlet = true :=
    all_parafermion_lanes_are_edge_states.1
  have hColorOne : laneIsEdgeState ParafermionEdgeLane.colorOne = true :=
    all_parafermion_lanes_are_edge_states.2.1
  have hColorTwo : laneIsEdgeState ParafermionEdgeLane.colorTwo = true :=
    all_parafermion_lanes_are_edge_states.2.2.1
  have hColorThree : laneIsEdgeState ParafermionEdgeLane.colorThree = true :=
    all_parafermion_lanes_are_edge_states.2.2.2
  have hSPlus : ChiralConeAlgebraFinality.sPlus * ChiralConeAlgebraFinality.sPlus = 0 :=
    ChiralConeAlgebraFinality.sPlus_sq_zero
  have hSMinus : ChiralConeAlgebraFinality.sMinus * ChiralConeAlgebraFinality.sMinus = 0 :=
    ChiralConeAlgebraFinality.sMinus_sq_zero
  refine And.intro hDirac ?_
  refine And.intro hMode ?_
  refine And.intro hKlein ?_
  refine And.intro hOdd ?_
  refine And.intro hLaneCount ?_
  refine And.intro hSinglet ?_
  refine And.intro hColorOne ?_
  refine And.intro hColorTwo ?_
  refine And.intro hColorThree ?_
  refine And.intro hSPlus hSMinus

/-- Final synthesis: the finite Jackiw--Rebbi edge-state kernel, the Klein core,
and the glide extinction rule line up on the same localization mechanism. -/
theorem jackiw_rebbi_cantor_edge_states_synthesis :
    boundaryDirac 0 = 0 ∧
    (boundaryDirac 0).mulVec boundaryZeroMode = 0 ∧
    (∀ (s : SpectralCPTKleinBottle.SpectralCylinder),
      SpectralCPTKleinBottle.cptGlide s = s ↔
        SpectralCPTKleinBottle.criticalCore s) ∧
    (∀ {k : ℕ} {c : ℂ}, Odd k → c = GlideDiracSelectionRule.pgPhase k * c → c = 0) ∧
    parafermionEdgeLanes.length = 4 ∧
    laneIsEdgeState ParafermionEdgeLane.singlet = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorOne = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorTwo = true ∧
    laneIsEdgeState ParafermionEdgeLane.colorThree = true ∧
    ChiralConeAlgebraFinality.sPlus * ChiralConeAlgebraFinality.sPlus = 0 ∧
    ChiralConeAlgebraFinality.sMinus * ChiralConeAlgebraFinality.sMinus = 0 ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.fundamental = true ∧
    TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.firstOvertone = true := by
  have hDirac : boundaryDirac 0 = 0 := boundaryDirac_core_zero
  have hMode : (boundaryDirac 0).mulVec boundaryZeroMode = 0 :=
    boundaryZeroMode_killed_by_core
  have hKlein :
      ∀ (s : SpectralCPTKleinBottle.SpectralCylinder),
        SpectralCPTKleinBottle.cptGlide s = s ↔
          SpectralCPTKleinBottle.criticalCore s :=
    klein_core_fixed_line
  have hOdd :
      ∀ {k : ℕ} {c : ℂ}, Odd k → c = GlideDiracSelectionRule.pgPhase k * c → c = 0 :=
    odd_glide_modes_extinguished
  have hLaneCount : parafermionEdgeLanes.length = 4 :=
    parafermion_edge_lane_count
  have hSinglet : laneIsEdgeState ParafermionEdgeLane.singlet = true :=
    all_parafermion_lanes_are_edge_states.1
  have hColorOne : laneIsEdgeState ParafermionEdgeLane.colorOne = true :=
    all_parafermion_lanes_are_edge_states.2.1
  have hColorTwo : laneIsEdgeState ParafermionEdgeLane.colorTwo = true :=
    all_parafermion_lanes_are_edge_states.2.2.1
  have hColorThree : laneIsEdgeState ParafermionEdgeLane.colorThree = true :=
    all_parafermion_lanes_are_edge_states.2.2.2
  have hSPlus : ChiralConeAlgebraFinality.sPlus * ChiralConeAlgebraFinality.sPlus = 0 :=
    ChiralConeAlgebraFinality.sPlus_sq_zero
  have hSMinus : ChiralConeAlgebraFinality.sMinus * ChiralConeAlgebraFinality.sMinus = 0 :=
    ChiralConeAlgebraFinality.sMinus_sq_zero
  have hFundamental :
      TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.fundamental = true :=
    TrappedHarmonicModes.fundamental_trapped
  have hFirstOvertone :
      TrappedHarmonicModes.ModeTrapped TrappedHarmonicModes.HarmonicMode.firstOvertone = true :=
    TrappedHarmonicModes.first_overtone_trapped
  refine And.intro hDirac ?_
  refine And.intro hMode ?_
  refine And.intro hKlein ?_
  refine And.intro hOdd ?_
  refine And.intro hLaneCount ?_
  refine And.intro hSinglet ?_
  refine And.intro hColorOne ?_
  refine And.intro hColorTwo ?_
  refine And.intro hColorThree ?_
  refine And.intro hSPlus ?_
  refine And.intro hSMinus ?_
  refine And.intro hFundamental hFirstOvertone

#check jackiw_rebbi_cantor_edge_states_synthesis

end JackiwRebbiCantorEdgeStates

end noncomputable section
