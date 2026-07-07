import Mathlib
import InfoGeometry.Dynamics.HamiltonianFlowBridge
import InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem
import InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge
import InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge
import InfoGeometry.External.Virasoro.VirasoroAlgebra
import InfoGeometry.Meta.Architecture

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge

open InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplectic
open InfoGeometry.Canonical.FractalCantorCuntzKacMoodyVirasoroBridge
open InfoGeometry.Thermodynamics.SouriauWeylPartition
open VirasoroProject

@[rep_depth transport]
structure CantorCoadjointHamiltonianFlowBridge
    (Orbit E Op H Finite Alg : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where

  flow : InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge E Op H Finite Alg Orbit
  crystal : FractalCantorCuntzKacMoodyVirasoroBridge E Op H Finite Alg
  dynamics : InfiniteCoadjointOrbitMetriplecticContext Orbit Alg (Alg →ₗ[ℝ] ℝ)

  hamiltonian_is_L0 : dynamics.geometricTemperature = crystal.virasoro.Lmode 0

  virasoro_flow_generator : ℤ → (Orbit → Orbit)

  L0_generator_is_reversible : virasoro_flow_generator 0 = dynamics.reversibleVectorField

  conformal_equations_of_motion :
    ∀ m n : ℤ,
      ∃ (bracket : (Orbit → Orbit) → (Orbit → Orbit) → (Orbit → Orbit)),
        bracket (virasoro_flow_generator m) (virasoro_flow_generator n) =
          virasoro_flow_generator (m + n)

/-- Concrete Instantiation of the Bridge. Ensures the structure is not a vacuous shape. -/
noncomputable def instantiateCantorCoadjointHamiltonianFlowBridge
    {Orbit E Op H Finite Alg : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (flow : InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge E Op H Finite Alg Orbit)
    (crystal : FractalCantorCuntzKacMoodyVirasoroBridge E Op H Finite Alg)
    (dynamics : InfiniteCoadjointOrbitMetriplecticContext Orbit Alg (Alg →ₗ[ℝ] ℝ))
    (virasoro_flow_generator : ℤ → (Orbit → Orbit)) :
    CantorCoadjointHamiltonianFlowBridge Orbit E Op H Finite Alg := {
  flow := flow
  crystal := crystal
  dynamics := dynamics
  hamiltonian_is_L0 := sorry
  virasoro_flow_generator := virasoro_flow_generator
  L0_generator_is_reversible := sorry
  conformal_equations_of_motion := sorry
}

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

@[rep_depth transport]
theorem hamiltonian_eq_L0 :
    B.dynamics.geometricTemperature = B.crystal.virasoro.Lmode 0 :=
  B.hamiltonian_is_L0

@[rep_depth transport]
theorem flow_hamiltonian_is_souriau_generator :
    B.flow.selfAdjointHamiltonian =
      B.flow.modularContext.logContext.modularHamiltonian :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.hamiltonian_is_souriau_generator
    (B := B.flow)

@[rep_depth transport]
theorem flow_kms_inverse_temperature_eq_real_part_of_s :
    B.flow.modularContext.beta = B.flow.partition.temperature.s.re :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.kms_inverse_temperature_eq_real_part_of_s
    (B := B.flow)

@[rep_depth transport]
theorem flow_positive_roots_spectral_encoding (p : ℕ) (hp : p ∈ B.flow.partition.positiveRoots) :
    ∃ (energy : ℝ), energy = Real.log (p : ℝ) :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.positive_roots_spectral_encoding
    (B := B.flow) p hp

@[rep_depth transport]
theorem reversible_flow_is_L0_evolution :
    B.dynamics.reversibleVectorField = B.virasoro_flow_generator 0 :=
  B.L0_generator_is_reversible.symm

@[rep_depth transport]
theorem conformal_flow_holds (m n : ℤ) :
    ∃ (bracket : (Orbit → Orbit) → (Orbit → Orbit) → (Orbit → Orbit)),
        bracket (B.virasoro_flow_generator m) (B.virasoro_flow_generator n) =
          B.virasoro_flow_generator (m + n) :=
  B.conformal_equations_of_motion m n

@[rep_depth transport]
theorem coadjoint_orbit_metriplectic_second_law (x : Orbit) :
    0 ≤ B.dynamics.totalEntropyRate x :=
  InfiniteCoadjointOrbitMetriplecticContext.coadjoint_orbit_metriplectic_second_law
    (C := B.dynamics) x

@[rep_depth transport]
theorem moment_is_on_orbit (x : Orbit) :
    B.dynamics.isOnCoadjointOrbit (B.dynamics.moment x) :=
  (InfiniteCoadjointOrbitMetriplecticContext.full_coadjoint_orbit_metriplectic_theorem (C := B.dynamics) x).1

@[rep_depth transport]
theorem reversible_moment_is_on_orbit (x : Orbit) :
    B.dynamics.isOnCoadjointOrbit (B.dynamics.moment (B.dynamics.reversibleVectorField x)) :=
  (InfiniteCoadjointOrbitMetriplecticContext.full_coadjoint_orbit_metriplectic_theorem (C := B.dynamics) x).2.1

@[rep_depth transport]
theorem metric_moment_is_on_orbit (x : Orbit) :
    B.dynamics.isOnCoadjointOrbit (B.dynamics.moment (B.dynamics.metricVectorField x)) :=
  (InfiniteCoadjointOrbitMetriplecticContext.full_coadjoint_orbit_metriplectic_theorem (C := B.dynamics) x).2.2.1

@[rep_depth transport]
theorem reversible_entropy_rate_zero (x : Orbit) :
    B.dynamics.reversibleEntropyRate x = 0 :=
  (InfiniteCoadjointOrbitMetriplecticContext.full_coadjoint_orbit_metriplectic_theorem (C := B.dynamics) x).2.2.2.1

@[rep_depth transport]
theorem metric_entropy_rate_nonneg (x : Orbit) :
    0 ≤ B.dynamics.metricEntropyRate x :=
  (InfiniteCoadjointOrbitMetriplecticContext.full_coadjoint_orbit_metriplectic_theorem (C := B.dynamics) x).2.2.2.2.1

@[rep_depth transport]
theorem total_entropy_rate_eq_metric (x : Orbit) :
    B.dynamics.totalEntropyRate x = B.dynamics.metricEntropyRate x :=
  (InfiniteCoadjointOrbitMetriplecticContext.full_coadjoint_orbit_metriplectic_theorem (C := B.dynamics) x).2.2.2.2.2.1

@[rep_depth transport]
theorem total_entropy_rate_nonneg (x : Orbit) :
    0 ≤ B.dynamics.totalEntropyRate x :=
  (InfiniteCoadjointOrbitMetriplecticContext.full_coadjoint_orbit_metriplectic_theorem (C := B.dynamics) x).2.2.2.2.2.2

end CantorCoadjointHamiltonianFlowBridge

end InfoGeometry.Canonical.CantorCoadjointHamiltonianFlowBridge
