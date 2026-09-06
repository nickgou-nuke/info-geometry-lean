import Mathlib
import InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine
import InfoGeometry.Canonical.LatticeHoppingDiffusionFlow
import InfoGeometry.Canonical.ContinuumPropagatorLimitBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeOptimalTransportBridge

Bridge packet for the missing dissipative half:

* the grand-canonical thermodynamic force,
* the JKO / Dirac square-root hopping layer,
* the RG stationary-scale continuum emergence,
* and the propagator-to-modular-flow limit.

This file does not add new analytic axioms. It packages the existing owner
surfaces so downstream code can project the transport engine, the lattice
hopping layer, and the continuum limit from one proof-carrying packet.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeOptimalTransport

open InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine
open InfoGeometry.Canonical.LatticeHoppingDiffusionFlow
open InfoGeometry.Canonical.ContinuumPropagatorLimitBridge
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.RGFlow
open InfoGeometry.Canonical
open InfoGeometry.Krein

/--
Prime optimal transport bridge.

This packages:
* the grand-canonical engine,
* the discrete lattice hopping / JKO / RG layer,
* and the continuum propagator limit.
-/
@[rep_depth transport]
structure PrimeOptimalTransportBridge
    (V Orbit E Op H Finite Alg Symmetry : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- Grand-canonical thermodynamic owner surface. -/
  engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry

  /-- Lattice hopping, Dirac square root, JKO, and RG owner surface. -/
  hopping : LatticeJKORGFlowBridge (V := V)

  /-- Continuum propagator limit bridge on the same real Hilbert carrier. -/
  propagator : ContinuumFlowLimitBridge (E := V)

namespace Bridge

variable
    {V Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : PrimeOptimalTransportBridge V Orbit E Op H Finite Alg Symmetry)

/-- The grand-canonical Massieu potential is the logarithm of the partition. -/
@[rep_depth transport]
theorem massieuPlanckPotential_eq_log_partition (s : ℂ) :
    B.engine.massieuPlanckPotential s =
      (B.engine.thermodynamicBridge.grandCanonical.logPartition s.re : ℂ) :=
  B.engine.massieuPlanckPotential_eq_log_partition s

/-- The grand-canonical force is the explicit-formula Wasserstein field. -/
@[rep_depth transport]
theorem thermodynamicForce_eq_explicitFormula (x : H) :
    B.engine.thermodynamicForce x =
      B.engine.thermodynamicBridge.explicitFormula.wassersteinField x :=
  B.engine.thermodynamicForce_eq_explicitFormula x

/-- The lattice JKO path decreases the installed free energy. -/
@[rep_depth transport]
theorem jko_energy_next_le_previous_energy :
    B.hopping.potential.energy B.hopping.jko.next ≤
      B.hopping.potential.energy B.hopping.jko.previous :=
  InfoGeometry.Canonical.LatticeHoppingDiffusionFlow.jko_energy_next_le_previous_energy
    B.hopping

/-- The lattice JKO penalty is bounded by the energy drop. -/
@[rep_depth transport]
theorem jko_penalty_le_energy_drop :
    B.hopping.potential.penalty B.hopping.jko.stepSize B.hopping.jko.next B.hopping.jko.previous ≤
      B.hopping.potential.energy B.hopping.jko.previous - B.hopping.potential.energy B.hopping.jko.next :=
  InfoGeometry.Canonical.LatticeHoppingDiffusionFlow.jko_penalty_le_energy_drop
    B.hopping

/-- The hopping/Dirac transport has no defect leakage. -/
@[rep_depth transport]
theorem no_defect_leakage_of_hopping
    (hPzeroMulPreg : B.hopping.reduction.Pzero * B.hopping.reduction.Preg = 0)
    (v : DoubledSpace V)
    (hReg : B.hopping.reduction.Preg v = v)
    (t : ℝ) :
    B.hopping.reduction.Pzero
      (InfoGeometry.Canonical.QuasilatticeDirac.quasilatticeDirac
        B.hopping.gen.bundle B.hopping.gen.baseD t v) = 0 := by
  exact InfoGeometry.Canonical.LatticeHoppingDiffusionFlow.no_defect_leakage_of_hopping
    B.hopping hPzeroMulPreg v hReg t

/-- RG stationarity at the bridge scale. -/
@[rep_depth transport]
theorem continuum_emergence :
    IsStationaryAtScale B.hopping.rg B.hopping.scale :=
  InfoGeometry.Canonical.LatticeHoppingDiffusionFlow.continuum_emergence B.hopping

/-- RG beta function vanishes at the continuum-emergence scale. -/
@[rep_depth transport]
theorem betaFunction_eq_zero_at_continuum_emergence (x : DoubledSpace V) :
    betaFunction B.hopping.rg B.hopping.scale x = 0 :=
  InfoGeometry.Canonical.LatticeHoppingDiffusionFlow.betaFunction_eq_zero_at_continuum_emergence
    B.hopping x

/-- The bridge propagator records the same continuum-flow consistency as its capstone. -/
@[rep_depth transport]
theorem propagator_flow_consistency :
    B.propagator.continuumFlow = B.propagator.propagator.modularData.toAdditiveModularFlow := by
  simpa using B.propagator.hFlowConsistency

/-- Bridge-level payload bundling the stationarity, decay, and defect-control witnesses. -/
@[rep_depth transport]
theorem continuum_emergence_payload
    (hInv : FlowInvariantAtScale B.hopping.rg B.hopping.scale)
    (hPzeroMulPreg : B.hopping.reduction.Pzero * B.hopping.reduction.Preg = 0)
    (v : DoubledSpace V)
    (hReg : B.hopping.reduction.Preg v = v)
    (t : ℝ) :
    IsStationaryAtScale B.hopping.rg B.hopping.scale ∧
      betaFunction B.hopping.rg B.hopping.scale v = 0 ∧
      B.hopping.potential.energy B.hopping.jko.next ≤ B.hopping.potential.energy B.hopping.jko.previous ∧
      B.hopping.potential.penalty B.hopping.jko.stepSize B.hopping.jko.next B.hopping.jko.previous ≤
        B.hopping.potential.energy B.hopping.jko.previous - B.hopping.potential.energy B.hopping.jko.next ∧
      B.hopping.reduction.Pzero
        (quasilatticeDirac B.hopping.gen.bundle B.hopping.gen.baseD t v) = 0 := by
  simpa using
    InfoGeometry.Canonical.LatticeHoppingDiffusionFlow.continuum_emergence_payload B.hopping
      hInv hPzeroMulPreg v hReg t

end Bridge

end InfoGeometry.Canonical.PrimeOptimalTransport
