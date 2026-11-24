/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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
  R.nonzero_boundaryIntegral_cannot_flow_to_flat Wz t

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

/-- Recover the nonzero residue property from the property packet. -/
theorem boundaryIntegral_ne_zero_of_property
    {x : State}
    (Wz : I.boundaryIntegral (R.stateRegion x) ω ≠ 0) :
    I.boundaryIntegral (R.stateRegion x) ω ≠ 0 :=
  Wz

/-- Witness-routed residue obstruction theorem. -/
theorem nonzero_boundaryIntegral_cannot_flow_to_flat_of_property
    {x : State}
    (Wz : I.boundaryIntegral (R.stateRegion x) ω ≠ 0)
    (t : ℝ) :
  F.flow t x ∉ F.Flat :=
  R.nonzero_boundaryIntegral_cannot_flow_to_flat
    (R.boundaryIntegral_ne_zero_of_property Wz) t

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

/-! ## 4. Geometric Stokes vanishing and Gauss--Bonnet quantization -/

section StokesGaussBonnet

/-- **Geometric Stokes analyticity (closedness ⇒ vanishing boundary integral).**
If the geometric derivative `d_geo ω` vanishes pointwise, then the boundary
integral of `ω` vanishes on every region `Ω`. -/
theorem boundaryIntegral_eq_zero_of_geometricDerivative_zero
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    (I : GeometricIntegralBackend Region Point Tangent Value)
    (ω : OperatorOneForm Point Tangent Value)
    (hClosed : ∀ p : Point, I.geometricDerivative ω p = 0)
    (Ω : Region) :
    I.boundaryIntegral Ω ω = 0 := by
  rw [I.stokes_eq Ω ω]
  exact I.volumeIntegral_zero_of_pointwise_zero Ω (I.geometricDerivative ω) hClosed

/-- **Closed-form winding vanishing.**
If `d_geo ω = 0` everywhere, then any certified winding datum assigns `0` to
every region `Ω`. -/
theorem winding_eq_zero_of_geometricDerivative_zero
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    (W : WindingNumberDatum I N ω)
    (hClosed : ∀ p : Point, I.geometricDerivative ω p = 0)
    (Ω : Region) :
    W.winding Ω = 0 := by
  have h0 : I.boundaryIntegral Ω ω = 0 :=
    boundaryIntegral_eq_zero_of_geometricDerivative_zero I ω hClosed Ω
  have hPeriod : ((W.winding Ω : ℤ) : ℝ) • N.phasePeriod = ((0 : ℤ) : ℝ) • N.phasePeriod := by
    calc
      ((W.winding Ω : ℤ) : ℝ) • N.phasePeriod = I.boundaryIntegral Ω ω :=
        (W.boundaryIntegral_eq_winding_smul Ω).symm
      _ = 0 := h0
      _ = ((0 : ℤ) : ℝ) • N.phasePeriod := by simp
  exact N.integer_period_injective hPeriod

/-- **Gauss--Bonnet defect quantization.**
The volume integral of the geometric curvature `d_geo ω` over `Ω` equals the
integer winding charge times the phase period. -/
theorem volumeIntegral_geometricDerivative_eq_winding_smul
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    (W : WindingNumberDatum I N ω)
    (Ω : Region) :
    I.volumeIntegral Ω (I.geometricDerivative ω) =
      ((W.winding Ω : ℤ) : ℝ) • N.phasePeriod := by
  rw [← I.stokes_eq Ω ω]
  exact W.boundaryIntegral_eq_winding_smul Ω

/-- **Gauss--Bonnet cobordism difference.**
Two regions with equal winding have equal curvature volume integrals; in
general, the difference of their curvature integrals is quantized by the
difference of their winding numbers. -/
theorem volumeIntegral_sub_eq_winding_sub_smul
    {Region Point Tangent Value : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    (W : WindingNumberDatum I N ω)
    (Ω₁ Ω₂ : Region) :
    I.volumeIntegral Ω₁ (I.geometricDerivative ω) -
        I.volumeIntegral Ω₂ (I.geometricDerivative ω) =
      (((W.winding Ω₁ - W.winding Ω₂ : ℤ) : ℝ)) • N.phasePeriod := by
  rw [volumeIntegral_geometricDerivative_eq_winding_smul W Ω₁,
    volumeIntegral_geometricDerivative_eq_winding_smul W Ω₂]
  push_cast
  rw [sub_smul]

end StokesGaussBonnet

end InfoGeometry.Geometry.WindingSnap
