import Mathlib.Tactic
import InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
import InfoGeometry.Dynamics.HamiltonianFlowBridge
import InfoGeometry.Canonical.BogoliubovOptimalTransport
import InfoGeometry.Canonical.CertifiedModularReduction
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.GrandCanonicalHamiltonianFlowBridge

Bridge packet linking the grand-canonical thermodynamic engine with the
Hamiltonian flow owner surface and the certified Bogoliubov regular lane.

This file does not add new analytic axioms. It only packages the existing
owner surfaces so downstream layers can project:

- the grand-canonical force as an explicit-formula vector field,
- the Hamiltonian as the Souriau/Tomita generator,
- the Bogoliubov canonical flow as an optimal regular-lane transport.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Canonical.GrandCanonicalHamiltonianFlowBridge

open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
open InfoGeometry.Dynamics.HamiltonianFlowBridge
open InfoGeometry.Canonical.BogoliubovOptimalTransport
open InfoGeometry.Canonical

/--
Grand-canonical Hamiltonian-flow bridge.

The thermodynamic state is carried on `H`, the Hamiltonian-flow owner surface
is carried explicitly, and the regular Bogoliubov lane is certified separately.
-/
@[rep_depth transport]
structure GrandCanonicalHamiltonianFlowBridge
    (Orbit E Op H Finite Alg Symmetry : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where
  /-- Grand-canonical thermodynamic bridge on the Hilbert carrier. -/
  thermodynamic : GrandCanonicalThermodynamicBridge H

  /-- The dynamic Hamiltonian-flow owner surface. -/
  flow : InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge
      E Op H Finite Alg Symmetry

  /-- Certified regular-lane Bogoliubov transport on the same Hilbert carrier. -/
  bogoliubov : CertifiedModularReduction (E := H)

namespace Bridge

variable
    {Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (B : GrandCanonicalHamiltonianFlowBridge Orbit E Op H Finite Alg Symmetry)

/-- The grand-canonical force is the explicit-formula Wasserstein field. -/
@[rep_depth transport]
theorem thermodynamicForce_eq_explicitFormula (x : H) :
    B.thermodynamic.logForce.thermodynamicForce x =
      B.thermodynamic.explicitFormula.wassersteinField x :=
  B.thermodynamic.force_matches_explicitFormula x

/-- The Hamiltonian on the flow owner surface is the Souriau generator. -/
@[rep_depth transport]
theorem flow_hamiltonian_is_souriau_generator :
    B.flow.selfAdjointHamiltonian =
      B.flow.modularContext.logContext.modularHamiltonian :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.hamiltonian_is_souriau_generator
    (B := B.flow)

/-- The modular inverse temperature is the real part of the complex temperature. -/
@[rep_depth transport]
theorem flow_kms_inverse_temperature_eq_real_part_of_s :
    B.flow.modularContext.beta = B.flow.partition.temperature.s.re :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.kms_inverse_temperature_eq_real_part_of_s
    (B := B.flow)

/-- Positive roots are spectrally encoded as logarithmic energies. -/
@[rep_depth transport]
theorem flow_positive_roots_spectral_encoding (p : ℕ) (hp : p ∈ B.flow.partition.positiveRoots) :
    ∃ (energy : ℝ), energy = Real.log (p : ℝ) :=
  InfoGeometry.Dynamics.HamiltonianFlowBridge.HamiltonianFlowBridge.positive_roots_spectral_encoding
    (B := B.flow) p hp

/-- The canonical Bogoliubov flow on the certified reduction is optimal. -/
@[rep_depth transport, capstone]
theorem bogoliubovFlow_isOptimal :
    IsOptimalBogoliubovFlow B.bogoliubov (canonicalBogoliubovFlow B.bogoliubov) := by
  exact InfoGeometry.Canonical.BogoliubovOptimalTransport.canonicalBogoliubovFlow_isOptimal
    (c := B.bogoliubov)

end Bridge

end InfoGeometry.Canonical.GrandCanonicalHamiltonianFlowBridge
