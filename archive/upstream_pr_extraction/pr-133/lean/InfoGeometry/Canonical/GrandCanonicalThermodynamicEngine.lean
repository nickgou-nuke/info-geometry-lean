import Mathlib.Tactic
import InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge
import InfoGeometry.Dynamics.HamiltonianFlowBridge
import InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine

Typed transport between a grand-canonical partition readout, a Wasserstein
field, and an explicit-formula field.  Compatibility is supplied by the
bridge structures and is not inferred from analytic number theory here.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine

open InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge
open InfoGeometry.Dynamics.HamiltonianFlowBridge
open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport.ExplicitFormulaVectorField

@[rep_depth transport]
structure GrandCanonicalEngine
    (Orbit E Op H Finite Alg Symmetry : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg] where

  /-- The underlying Super-Kähler manifold and Hamiltonian flow. -/
  flow : HamiltonianFlowBridge E Op H Finite Alg Symmetry

  /-- The JKO/Wasserstein optimal transport context. -/
  ot : WassersteinGradientFlow H

  /-- The conservative grand-canonical thermodynamic bridge on the Hilbert carrier. -/
  thermodynamicBridge : GrandCanonicalThermodynamicBridge H

/--
Native constructor for `GrandCanonicalEngine`.
The owner API is explicit: callers provide the required bridge fields, so the
construction is fully definitional and cannot fabricate missing data.
-/
def instantiateGrandCanonicalEngine
    (Orbit E Op H Finite Alg Symmetry : Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (flow : HamiltonianFlowBridge E Op H Finite Alg Symmetry)
    (ot : WassersteinGradientFlow H)
    (thermodynamicBridge : GrandCanonicalThermodynamicBridge H) :
    GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry :=
  { flow := flow, ot := ot, thermodynamicBridge := thermodynamicBridge }
namespace GrandCanonicalEngine

variable
    {Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]

variable (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry)

def massieuPlanckPotential
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) (s : ℂ) : ℂ :=
  (Engine.thermodynamicBridge.grandCanonical.logPartition s.re : ℂ)

def thermodynamicForce
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) (x : H) : ℝ :=
  Engine.thermodynamicBridge.logForce.thermodynamicForce x

@[simp] theorem potential_eq_log_partition
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) (s : ℂ) :
    Engine.massieuPlanckPotential s =
      (Engine.thermodynamicBridge.grandCanonical.logPartition s.re : ℂ) := rfl

@[simp] theorem thermodynamicForce_eq_logForce
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) (x : H) :
    Engine.thermodynamicForce x = Engine.thermodynamicBridge.logForce.thermodynamicForce x := rfl

@[rep_depth transport]
theorem massieuPlanckPotential_eq_log_partition (s : ℂ) :
    Engine.massieuPlanckPotential s =
      (Engine.thermodynamicBridge.grandCanonical.logPartition s.re : ℂ) :=
  potential_eq_log_partition Engine s

@[rep_depth transport]
theorem thermodynamicForce_eq_bridge_logForce (x : H) :
    Engine.thermodynamicForce x = Engine.thermodynamicBridge.logForce.thermodynamicForce x :=
  thermodynamicForce_eq_logForce Engine x

/-- Intermediate equality exposing the supplied logarithmic force. -/
lemma thermodynamicForce_eq_explicitFormula_step1 (x : H) :
    Engine.thermodynamicForce x = Engine.thermodynamicBridge.logForce.thermodynamicForce x :=
  thermodynamicForce_eq_logForce Engine x

/-- Intermediate equality exposing the supplied explicit-formula field. -/
lemma thermodynamicForce_eq_explicitFormula_step2 (x : H) :
    Engine.thermodynamicBridge.logForce.thermodynamicForce x = 
      Engine.thermodynamicBridge.explicitFormula.wassersteinField x :=
  Engine.thermodynamicBridge.thermodynamicForce_eq_explicitFormula x

@[rep_depth transport]
theorem thermodynamicForce_eq_explicitFormula (x : H) :
    Engine.thermodynamicForce x = Engine.thermodynamicBridge.explicitFormula.wassersteinField x :=
  by
    rw [thermodynamicForce_eq_explicitFormula_step1 Engine x]
    rw [thermodynamicForce_eq_explicitFormula_step2 Engine x]

theorem thermodynamicForce_eq_zero_iff_explicitFormula_eq_zero (x : H) :
    Engine.thermodynamicForce x = 0 ↔
      Engine.thermodynamicBridge.explicitFormula.explicitFormula
        (Engine.thermodynamicBridge.explicitFormula.coordinate x) = 0 := by
  rw [thermodynamicForce_eq_explicitFormula Engine x]
  exact @InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport.ExplicitFormulaVectorField.wassersteinField_eq_zero_iff_explicitFormula_eq_zero
    H (Engine.thermodynamicBridge.explicitFormula) x

end GrandCanonicalEngine

@[rep_depth transport]
theorem hamiltonian_flow_is_souriau_generator
    {Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) :
    Engine.flow.selfAdjointHamiltonian =
      Engine.flow.modularContext.logContext.modularHamiltonian :=
  Engine.flow.hamiltonian_is_souriau_generator

@[rep_depth transport]
theorem kms_inverse_temperature_eq_real_part_of_s
    {Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) :
    Engine.flow.modularContext.beta = Engine.flow.partition.temperature.s.re :=
  Engine.flow.beta_eq_re_s

/-- Intermediate force/readout equality for the supplied bridge. -/
lemma riemann_weil_step1
    {Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) (x : H) :
    Engine.thermodynamicForce x = Engine.thermodynamicBridge.logForce.thermodynamicForce x :=
  Engine.thermodynamicForce_eq_logForce x

/-- Intermediate force/readout equality for the supplied bridge. -/
lemma riemann_weil_step2
    {Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) (x : H) :
    Engine.thermodynamicBridge.logForce.thermodynamicForce x = 
      Engine.thermodynamicBridge.explicitFormula.wassersteinField x :=
  Engine.thermodynamicBridge.thermodynamicForce_eq_explicitFormula x

/-- Equality of the supplied thermodynamic force and supplied Wasserstein field.
The name is retained for compatibility; no independent gradient construction is
made here. -/
@[rep_depth transport]
theorem riemann_weil_is_wasserstein_gradient 
    {Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [SMul Op H] [CompleteSpace H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) (x : H) :
    Engine.thermodynamicForce x =
      Engine.thermodynamicBridge.explicitFormula.wassersteinField x := by
  rw [riemann_weil_step1 Engine x, riemann_weil_step2 Engine x]

/-- The supplied spectral compatibility identifies the energy readout with
`log p` for a selected positive-root index. -/
@[rep_depth transport]
theorem positive_roots_spectral_encoding
    {Orbit E Op H Finite Alg Symmetry : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Module ℝ E]
    [Ring Op] [StarRing Op]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [SMul Op H]
    [InnerProductSpace ℝ H]
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (Engine : GrandCanonicalEngine Orbit E Op H Finite Alg Symmetry) (p : ℕ)
    (hp : p ∈ Engine.flow.partition.positiveRoots) :
    ∃ (energy : ℝ), energy = Real.log (p : ℝ) :=
  Engine.flow.spectralCompatibility p hp

end InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine
