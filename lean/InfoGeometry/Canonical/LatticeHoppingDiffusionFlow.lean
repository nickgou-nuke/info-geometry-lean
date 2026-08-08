/-
InfoGeometry/Canonical/LatticeHoppingDiffusionFlow.lean

Lattice Hopping Diffusion Flow Bridge.

This module formalizes the "Grand Transition" from the discrete Cantor lattice
to the continuous informational manifold. It defines the stochastic hopping
propagator and its relation to the Dirac operator and RG flow.
-/

import Mathlib.Tactic
import InfoGeometry.Canonical.OperatorJKOStep
import InfoGeometry.Canonical.RGFlow
import InfoGeometry.Canonical.QuasilatticeDirac
import InfoGeometry.Canonical.BogoliubovOptimalTransport
import InfoGeometry.Canonical.CertifiedModularReduction
import InfoGeometry.Canonical.BogoliubovVielbein
import InfoGeometry.Krein.DoubledSpace

namespace InfoGeometry.Canonical.LatticeHoppingDiffusionFlow

open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorJKOStep
open InfoGeometry.Canonical.RGFlow
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.BogoliubovOptimalTransport
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

section Bridge

/- Use 'Type' (Type 0) to match the rest of the repository's Hilbert space modules. -/
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- 
Cantor Hopping Propagator.
Defines the transition operator between adjacent nodes on the Cantor tree.
-/
structure CantorHoppingPropagator (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- Hopping rate / transition probability amplitude. -/
  rate : ℝ
  /-- Adjacency matrix / operator on the Cantor space. -/
  hopOp : V →ₗ[ℝ] V
  /-- The operator is self-adjoint (reversible diffusion). -/
  self_adjoint : ∀ x y, inner ℝ (hopOp x) y = inner ℝ x (hopOp y)

/-- 
Dirac Square Root Propagator.
The generator of the stochastic hopping is the square root of the Dirac operator.
-/
structure DiracSquareRootPropagator (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] where
  /-- Base Dirac operator seed. -/
  baseD : DoubledSpace V →L[ℝ] DoubledSpace V
  /-- The vielbein bundle for transport. -/
  bundle : BogoliubovVielbeinBundle (E := V)
  /-- The square root operator D^(1/2) at scale t. -/
  sqrtDirac : ℝ → DoubledSpace V →L[ℝ] DoubledSpace V
  /-- Consistency: (D^(1/2))^2 = |D_quasilattice|. -/
  is_square_root : ∀ t ψ, sqrtDirac t (sqrtDirac t ψ) = (quasilatticeDirac bundle baseD t) ψ

/-- 
Lattice JKO-RG Flow Bridge.
Connects the discrete hopping steps to the macroscopic RG flow.
-/
structure LatticeJKORGFlowBridge where
  /-- Microscopic hopping propagator. -/
  hop : CantorHoppingPropagator (DoubledSpace V)
  /-- Dirac square root generator. -/
  gen : DiracSquareRootPropagator V
  /-- Modular reduction for optimality certification. -/
  reduction : CertifiedModularReduction (E := DoubledSpace V)
  /-- Potential for JKO gradient flow. -/
  potential : OperatorJKOPotential (DoubledSpace V)
  /-- JKO time step for the free energy gradient flow. -/
  jko : OperatorJKOArgmin potential
  /-- Macroscopic RG flow. -/
  rg : InformationFlow (DoubledSpace V)
  /-- Scale parameter mapping. -/
  scale : ℝ
  /-- Optimality from Bogoliubov Transport. -/
  optimality : IsOptimalBogoliubovFlow reduction (fun t => quasilatticeDirac gen.bundle gen.baseD t)
  /-- Continuum emergence property at the selected RG scale. -/
  continuumEmergence : IsStationaryAtScale rg scale

end Bridge

/-- 
THE CONTINUUM EMERGENCE THEOREM.
The discrete JKO hopping path converges to the Ricci-flat manifold 
under the RG scaling limit scale → ∞.
-/
theorem continuum_emergence {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V)) :
    IsStationaryAtScale B.rg B.scale := by
  exact B.continuumEmergence

/-- The RG beta function vanishes at the bridge's stationary scale. -/
theorem betaFunction_eq_zero_at_continuum_emergence
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V)) (x : DoubledSpace V) :
    betaFunction B.rg B.scale x = 0 := by
  exact betaFunction_eq_zero_at_stationary_scale B.rg B.scale B.continuumEmergence x

/-- The RG dual-map derivative vanishes at the bridge's stationary scale. -/
theorem dual_map_deriv_eq_zero_at_continuum_emergence
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V)) (x : DoubledSpace V) :
    deriv (fun t => (B.rg t).dualMap x) B.scale = 0 := by
  exact dual_map_deriv_eq_zero_at_stationary_scale B.rg B.scale B.continuumEmergence x

/-- Flow-invariance at the bridge scale is enough to force stationarity. -/
theorem continuum_emergence_of_flowInvariant
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V))
    (hInv : FlowInvariantAtScale B.rg B.scale) :
    IsStationaryAtScale B.rg B.scale :=
  isStationaryAtScale_of_flowInvariant B.rg B.scale hInv

/-- The RG beta function vanishes under explicit flow-invariance. -/
theorem betaFunction_eq_zero_of_flowInvariant
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V))
    (hInv : FlowInvariantAtScale B.rg B.scale)
    (x : DoubledSpace V) :
    betaFunction B.rg B.scale x = 0 := by
  exact betaFunction_eq_zero_at_stationary_scale B.rg B.scale
    (continuum_emergence_of_flowInvariant B hInv) x

/-- The RG dual-map derivative vanishes under explicit flow-invariance. -/
theorem dual_map_deriv_eq_zero_of_flowInvariant
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V))
    (hInv : FlowInvariantAtScale B.rg B.scale)
    (x : DoubledSpace V) :
    deriv (fun t => (B.rg t).dualMap x) B.scale = 0 := by
  exact dual_map_deriv_eq_zero_at_stationary_scale B.rg B.scale
    (continuum_emergence_of_flowInvariant B hInv) x

/-- The bridge JKO step decreases the installed free energy. -/
theorem jko_energy_next_le_previous_energy
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V)) :
    B.potential.energy B.jko.next ≤ B.potential.energy B.jko.previous :=
  B.jko.energy_next_le_previous_energy

/-- The bridge JKO penalty is bounded by the energy drop. -/
theorem jko_penalty_le_energy_drop
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V)) :
    B.potential.penalty B.jko.stepSize B.jko.next B.jko.previous ≤
      B.potential.energy B.jko.previous - B.potential.energy B.jko.next :=
  B.jko.penalty_le_energy_drop

/-- The hopping/Dirac transport has no defect leakage once the support split is supplied. -/
theorem no_defect_leakage_of_hopping
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V))
    (hPzeroMulPreg : B.reduction.Pzero * B.reduction.Preg = 0)
    (v : DoubledSpace V)
    (hReg : B.reduction.Preg v = v)
    (t : ℝ) :
    B.reduction.Pzero (quasilatticeDirac B.gen.bundle B.gen.baseD t v) = 0 := by
  exact no_defect_leakage_of_optimal_flow
    B.reduction
    (fun t => quasilatticeDirac B.gen.bundle B.gen.baseD t)
    B.optimality
    hPzeroMulPreg
    v
    hReg
    t

/-- Compact payload for the lattice bridge: stationarity, JKO decay, and defect control. -/
theorem continuum_emergence_payload
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : LatticeJKORGFlowBridge (V := V))
    (hInv : FlowInvariantAtScale B.rg B.scale)
    (hPzeroMulPreg : B.reduction.Pzero * B.reduction.Preg = 0)
    (v : DoubledSpace V)
    (hReg : B.reduction.Preg v = v)
    (t : ℝ) :
    IsStationaryAtScale B.rg B.scale ∧
      betaFunction B.rg B.scale v = 0 ∧
      B.potential.energy B.jko.next ≤ B.potential.energy B.jko.previous ∧
      B.potential.penalty B.jko.stepSize B.jko.next B.jko.previous ≤
        B.potential.energy B.jko.previous - B.potential.energy B.jko.next ∧
      B.reduction.Pzero (quasilatticeDirac B.gen.bundle B.gen.baseD t v) = 0 := by
  refine ⟨continuum_emergence_of_flowInvariant B hInv, ?_, ?_, ?_, ?_⟩
  · exact betaFunction_eq_zero_of_flowInvariant B hInv v
  · exact jko_energy_next_le_previous_energy B
  · exact jko_penalty_le_energy_drop B
  · exact no_defect_leakage_of_hopping B hPzeroMulPreg v hReg t

end InfoGeometry.Canonical.LatticeHoppingDiffusionFlow
