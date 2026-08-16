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

end CantorCoadjointHamiltonianFlowBridge

end InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge
