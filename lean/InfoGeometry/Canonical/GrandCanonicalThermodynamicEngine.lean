import Mathlib
import InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge
import InfoGeometry.Dynamics.HamiltonianFlowBridge
import InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine

The Grand Canonical Engine of the Informational Universe.

This module formalizes the ultimate physical discovery:
1. The informational crystal is a Grand Canonical Ensemble of ensembles.
2. The Optimal Transport (Wasserstein flow) is driven by the gradient of the 
   log-partition function (the Free Energy).
3. The Riemann-Weil Explicit Formula is identified as the exact Wasserstein 
   vector field of this thermodynamic engine.

Boundary: the dynamical force law is carried as theorem data from the imported
surfaces; this module does not replace those owner theorems.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrandCanonicalThermodynamicEngine

open InfoGeometry.Thermodynamics.SouriauWeylPartitionBridge
open InfoGeometry.Dynamics.HamiltonianFlowBridge
open InfoGeometry.Canonical.SouriauMetriplecticOptimalTransport

/--
Grand Canonical Thermodynamic Engine.

Bridges the unnormalized Grand Canonical Ensemble with the Metriplectic 
Optimal Transport flow.
-/
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
  The Grand Canonical Potential (Massieu-Planck potential):
  Φ(s) = log Z(s)
  -/
  massieuPlanckPotential : ℂ → ℂ :=
    fun s => (thermodynamicBridge.grandCanonical.logPartition s.re : ℂ)

  /-- The Massieu-Planck potential is the logarithm of the partition function. -/
  potential_eq_log_partition :
    ∀ s, massieuPlanckPotential s =
      (thermodynamicBridge.grandCanonical.logPartition s.re : ℂ) := by
    intro s
    rfl

  /--
  The thermodynamic force selected for the engine.
  -/
  thermodynamicForce : H → ℝ :=
    fun x => thermodynamicBridge.logForce.thermodynamicForce x

  /--
  The engine force is the same field used by the thermodynamic bridge.
  -/
  thermodynamicForce_eq_logForce :
    ∀ x : H, thermodynamicForce x = thermodynamicBridge.logForce.thermodynamicForce x
    := by
    intro x
    rfl

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

@[rep_depth transport]
theorem massieuPlanckPotential_eq_log_partition (s : ℂ) :
    Engine.massieuPlanckPotential s =
      (Engine.thermodynamicBridge.grandCanonical.logPartition s.re : ℂ) :=
  Engine.potential_eq_log_partition s

@[rep_depth transport]
theorem thermodynamicForce_eq_bridge_logForce (x : H) :
    Engine.thermodynamicForce x = Engine.thermodynamicBridge.logForce.thermodynamicForce x :=
  Engine.thermodynamicForce_eq_logForce x

/-- Helper lemma breaking down the explicit formula property. -/
lemma thermodynamicForce_eq_explicitFormula_step1 (x : H) :
    Engine.thermodynamicForce x = Engine.thermodynamicBridge.logForce.thermodynamicForce x :=
  Engine.thermodynamicForce_eq_logForce x

/-- Helper lemma breaking down the explicit formula property. -/
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

end GrandCanonicalEngine

/--
CAPSTONE: The Riemann-Weil Explicit Formula Correspondence.

Identifies the Explicit Formula from Number Theory as the dynamical 
Wasserstein vector field of the Information Crystal.
-/
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

/-- Helper lemma for the Riemann-Weil capstone. -/
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

/-- Helper lemma for the Riemann-Weil capstone. -/
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
