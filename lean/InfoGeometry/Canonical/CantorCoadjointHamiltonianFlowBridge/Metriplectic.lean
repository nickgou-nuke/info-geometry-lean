import Mathlib.Tactic
import InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge.Basic

/-!
# InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge.Metriplectic

Metriplectic theorems for the Coadjoint Hamiltonian Flow of the Information Crystal.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge

open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic
open InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge
open InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge
open VirasoroProject

namespace CantorCoadjointHamiltonianFlowBridge

variable
    {Orbit E Op H Finite Alg : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : CantorCoadjointHamiltonianFlowBridge Orbit E Op H Finite Alg)

/-- The coadjoint-orbit metriplectic second law is available from the owner layer. -/
@[rep_depth transport]
theorem coadjoint_orbit_metriplectic_second_law (x : Orbit) :
    0 ≤ B.dynamics.totalEntropyRate x :=
  InfiniteCoadjointOrbitMetriplecticContext.coadjoint_orbit_metriplectic_second_law
    (C := B.dynamics) x

/-- Packed coadjoint-orbit metriplectic outputs are available from the owner layer. -/
@[rep_depth transport]
theorem full_coadjoint_orbit_metriplectic_theorem (x : Orbit) :
    B.dynamics.isOnCoadjointOrbit (B.dynamics.moment x)
      ∧ B.dynamics.isOnCoadjointOrbit (B.dynamics.moment (B.dynamics.reversibleVectorField x))
      ∧ B.dynamics.isOnCoadjointOrbit (B.dynamics.moment (B.dynamics.metricVectorField x))
      ∧ B.dynamics.reversibleEntropyRate x = 0
      ∧ 0 ≤ B.dynamics.metricEntropyRate x
      ∧ B.dynamics.totalEntropyRate x = B.dynamics.metricEntropyRate x
      ∧ 0 ≤ B.dynamics.totalEntropyRate x :=
  InfiniteCoadjointOrbitMetriplecticContext.full_coadjoint_orbit_metriplectic_theorem
    (C := B.dynamics) x

end CantorCoadjointHamiltonianFlowBridge

end InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge
