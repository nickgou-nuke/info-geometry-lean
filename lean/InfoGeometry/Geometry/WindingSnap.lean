/-
InfoGeometry/Geometry/WindingSnap.lean

Bridge from residue winding to TopologicalSnap obstruction flows.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.SpectralDivisors
import InfoGeometry.OperatorAlgebra.TopologicalSnap

noncomputable section

namespace InfoGeometry.Geometry.WindingSnap

open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Geometry.SpectralDivisors
open InfoGeometry.OperatorAlgebra.TopologicalSnap

/-! ## 1. Winding obstruction flows -/

/--
A winding obstruction flow.

This packages the integer winding as the conserved obstruction used by
`TopologicalSnap`.
-/
structure WindingObstructionFlow
    (State : Type*) where
  /-- Integer winding/topological charge of a state. -/
  winding : State → ℤ
  /-- Flat/trivial sector. -/
  Flat : Set State
  /-- Admissible flow. -/
  flow : ℝ → State → State
  /-- Flat states have zero winding. -/
  flat_winding_zero :
    ∀ x : State, x ∈ Flat → winding x = 0
  /-- The flow preserves winding. -/
  flow_preserves_winding :
    ∀ t x, winding (flow t x) = winding x

/-- Convert a winding obstruction flow to the generic `TopologicalSnap` flow. -/
def WindingObstructionFlow.toConserved
    {State : Type*}
    (F : WindingObstructionFlow State) :
    ConservedObstructionFlow State ℤ where
  invariant := F.winding
  Flat := F.Flat
  flow := F.flow
  flat_invariant_zero := F.flat_winding_zero
  flow_preserves_invariant := F.flow_preserves_winding

namespace WindingObstructionFlow

variable {State : Type*}
variable (F : WindingObstructionFlow State)

/-- Flow invariance of the stored winding, as a theorem accessor. -/
theorem winding_flow_eq
    (t : ℝ)
    (x : State) :
    F.winding (F.flow t x) = F.winding x :=
  F.flow_preserves_winding t x

/-- Flat states have zero winding. -/
theorem winding_eq_zero_of_flat
    {x : State}
    (hx : x ∈ F.Flat) :
    F.winding x = 0 :=
  F.flat_winding_zero x hx

/--
The flow of a flat state has zero winding.

This uses only winding preservation, not invariance of the flat set itself.
-/
theorem winding_flow_eq_zero_of_flat
    (t : ℝ)
    {x : State}
    (hx : x ∈ F.Flat) :
    F.winding (F.flow t x) = 0 := by
  rw [F.flow_preserves_winding t x]
  exact F.flat_winding_zero x hx

/-- A state with nonzero winding cannot flow to the flat sector. -/
theorem nonzero_winding_cannot_flow_to_flat
    {x : State}
    (hx : F.winding x ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat :=
  F.toConserved.nontrivial_cannot_flow_to_flat hx t

end WindingObstructionFlow

/-! ## 1A. Region flow bridge -/

/--
If a region-flow winding agrees with the residue winding, then the boundary
integral is invariant under the flow.
-/
theorem boundaryIntegral_flow_eq
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    (W : WindingNumberDatum I N ω)
    (F : WindingObstructionFlow Region)
    (hlink : ∀ Ω : Region, W.winding Ω = F.winding Ω)
    (t : ℝ)
    (Ω : Region) :
    I.boundaryIntegral (F.flow t Ω) ω =
      I.boundaryIntegral Ω ω := by
  apply W.boundaryIntegral_eq_of_winding_eq
  rw [hlink (F.flow t Ω), hlink Ω]
  exact F.flow_preserves_winding t Ω

/--
If a region is flat and the region-flow winding agrees with the residue
winding, then the flowed region has zero boundary integral.
-/
theorem boundaryIntegral_flow_eq_zero_of_flat
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    (W : WindingNumberDatum I N ω)
    (F : WindingObstructionFlow Region)
    (hlink : ∀ Ω : Region, W.winding Ω = F.winding Ω)
    (t : ℝ)
    {Ω : Region}
    (hΩ : Ω ∈ F.Flat) :
    I.boundaryIntegral (F.flow t Ω) ω = 0 := by
  apply W.boundaryIntegral_eq_zero_of_winding_zero
  rw [hlink (F.flow t Ω)]
  exact F.winding_flow_eq_zero_of_flat t hΩ

/-! ## 2. Residue readout for states -/

/--
A readout connecting states to residue regions.

This removes the need to repeatedly pass an explicit hypothesis
`F.winding x = W.winding (stateRegion x)`.
-/
def StateResidueReadout
    {State Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (N : PhaseResidueNormalizer Value)
    (ω : OperatorOneForm Point Tangent Value)
    (W : WindingNumberDatum I N ω)
    (F : WindingObstructionFlow State) :=
  {stateRegion : State → Region //
    ∀ x : State,
      F.winding x = W.winding (stateRegion x)}

namespace StateResidueReadout

variable
    {State Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {W : WindingNumberDatum I N ω}
    {F : WindingObstructionFlow State}

variable (R : StateResidueReadout I N ω W F)

abbrev stateRegion : State → Region := R.1

theorem winding_eq_regionWinding
    (x : State) :
    F.winding x = W.winding (R.stateRegion x) :=
  R.2 x

def mk
    (stateRegion : State → Region)
    (winding_eq_regionWinding :
      ∀ x : State,
        F.winding x = W.winding (stateRegion x)) :
    StateResidueReadout I N ω W F :=
  ⟨stateRegion, winding_eq_regionWinding⟩

/-- Recover the nonzero residue hypothesis from the witness packet. -/
theorem boundaryIntegral_ne_zero_of_witness
    {x : State}
    (Wz : I.boundaryIntegral (R.stateRegion x) ω ≠ 0) :
    I.boundaryIntegral (R.stateRegion x) ω ≠ 0 :=
  Wz

/-- Nonzero analytic residue obstructs relaxation into the flat sector. -/
theorem nonzero_boundaryIntegral_cannot_flow_to_flat
    {x : State}
    (hx :
      I.boundaryIntegral (R.stateRegion x) ω ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  apply F.nonzero_winding_cannot_flow_to_flat
  intro hFx
  have hRegion :
      W.winding (R.stateRegion x) = 0 := by
    rw [← R.winding_eq_regionWinding x]
    exact hFx
  exact hx
    (WindingNumberDatum.boundaryIntegral_eq_zero_of_winding_zero W hRegion)

/-- Witness-routed residue obstruction theorem. -/
theorem nonzero_boundaryIntegral_cannot_flow_to_flat_of_witness
    {x : State}
    (Wz : I.boundaryIntegral (R.stateRegion x) ω ≠ 0)
    (t : ℝ) :
  F.flow t x ∉ F.Flat :=
  R.nonzero_boundaryIntegral_cannot_flow_to_flat
    (R.boundaryIntegral_ne_zero_of_witness Wz) t

/-- Equivalent version using nonzero region winding. -/
theorem nonzero_region_winding_cannot_flow_to_flat
    {x : State}
    (hx :
      W.winding (R.stateRegion x) ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  apply F.nonzero_winding_cannot_flow_to_flat
  intro hFx
  exact hx
    (by
      rw [← R.winding_eq_regionWinding x]
      exact hFx)

end StateResidueReadout

/-! ## 3. Index readout for states -/

/-- A readout connecting states to topological index cycles. -/
def StateIndexReadout
    {State Region Point Tangent Value Cycle : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (N : PhaseResidueNormalizer Value)
    (ω : OperatorOneForm Point Tangent Value)
    (W : WindingNumberDatum I N ω)
    (T :
      SpectralDivisors.TopologicalIndexDatum
        (I := I) (N := N) (ω := ω) W Cycle)
    (F : WindingObstructionFlow State) :=
  {cycleOf : State → Cycle //
    ∀ x : State,
      F.winding x = T.index (cycleOf x)}

namespace StateIndexReadout

variable
    {State Region Point Tangent Value Cycle : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {W : WindingNumberDatum I N ω}
    {T :
      SpectralDivisors.TopologicalIndexDatum
        (I := I) (N := N) (ω := ω) W Cycle}
    {F : WindingObstructionFlow State}

variable (R : StateIndexReadout I N ω W T F)

abbrev cycleOf : State → Cycle := R.1

theorem winding_eq_index
    (x : State) :
    F.winding x = T.index (R.cycleOf x) :=
  R.2 x

def mk
    (cycleOf : State → Cycle)
    (winding_eq_index :
      ∀ x : State,
        F.winding x = T.index (cycleOf x)) :
    StateIndexReadout I N ω W T F :=
  ⟨cycleOf, winding_eq_index⟩

/-- Nonzero topological index obstructs relaxation into the flat sector. -/
theorem nonzero_index_cannot_flow_to_flat
    {x : State}
    (hx :
      T.index (R.cycleOf x) ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  apply F.nonzero_winding_cannot_flow_to_flat
  intro hFx
  exact hx
    (by
      rw [← R.winding_eq_index x]
      exact hFx)

/-- Nonzero boundary residue of the associated index cycle obstructs relaxation. -/
theorem nonzero_boundaryIntegral_cannot_flow_to_flat
    {x : State}
    (hx :
      I.boundaryIntegral (T.regionOf (R.cycleOf x)) ω ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  apply R.nonzero_index_cannot_flow_to_flat
  exact
    (SpectralDivisors.TopologicalIndexDatum.boundaryIntegral_ne_zero_iff_index_ne_zero
      T (R.cycleOf x)).mp hx

/-- Nonzero spectral flow obstructs relaxation into the flat sector. -/
theorem nonzero_spectralFlow_cannot_flow_to_flat
    {x : State}
    (hx :
      T.spectralFlow (R.cycleOf x) ≠ 0)
    (t : ℝ) :
    F.flow t x ∉ F.Flat := by
  apply R.nonzero_index_cannot_flow_to_flat
  intro hIndex
  exact hx
    (by
      rw [← T.index_eq_spectralFlow (R.cycleOf x)]
      exact hIndex)

end StateIndexReadout

end InfoGeometry.Geometry.WindingSnap
