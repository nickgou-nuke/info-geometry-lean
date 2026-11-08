import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorSurprisal
import InfoGeometry.Canonical.RedLineCausalConeMonodromy

set_option linter.unusedSectionVars false

/-!
# Operator Surprisal and Log-Volume Topological Generators

This module collects three type-distinct logarithmic constructions already
owned by the repository:

1. an operator-surprisal commutator generating a hyperbolic boost;
2. the logarithmic pole form whose contour integral records winding;
3. a red-line log-Jacobian potential whose exponential recovers a Jacobian.

The packet theorem records that these three owner results hold
simultaneously.  It does not identify their carriers, does not prove an
equivalence between them, and does not identify generic state surprisal with
Boltzmann macroentropy.
-/

namespace InfoGeometry.Canonical.SurprisalTopologicalGeometryGenerator

open Complex
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.OperatorSurprisal
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D
open InfoGeometry.Canonical.RedLineCausalConeMonodromy
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-- The logarithmic pole-form coefficient `1 / z`.

Its winding theorem is independent of any identification with a state
surprisal operator or a Boltzmann multiplicity operator.
-/
noncomputable def surprisalDeRhamGenerator (z : ℂ) : ℂ :=
  1 / z

/--
**Main Theorem 1: Surprisal Generates Hyperbolic Modular Boosts**
The surprisal operator $S_{\text{surprisal}}(\beta)$ acts on the boundary nilpotents to generate hyperbolic boosts:
$$[S_{\text{surprisal}}(\beta), N] = (2\beta) \cdot N.$$
-/
theorem surprisal_generates_modular_geometry (β : ℝ) :
    InfoGeometry.Canonical.OperatorSurprisal.surprisal β * N - N * InfoGeometry.Canonical.OperatorSurprisal.surprisal β = (2 * β) • N :=
  surprisal_generates_hyperbolic_boost β

/--
**Main Theorem 2: The logarithmic pole form records winding.**
The normalized contour integral around the singularity is the integral
winding number:
$$\frac{1}{2\pi i} \oint_{\gamma} d S_{\text{surprisal}} = n \in \mathbb{Z}.$$
-/
theorem surprisal_derham_cohomology_generator (R : ℝ) (hR : 0 < R) (n : ℤ) :
    poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) :=
  discrete_quantized_time_loop R hR n

/--
**Main Theorem 3: Operator-surprisal and log-volume theorem packet.**

The conjunction preserves the native meaning of each component:

1. the operator-surprisal commutator identity;
2. the logarithmic pole winding identity;
3. exponentiation of the red-line log-Jacobian potential.

No equality or equivalence between the three logarithmic owners is asserted.
-/
theorem operatorSurprisal_logVolume_topological_packet
    (β : ℝ) (R : ℝ) (hR : 0 < R) (n : ℤ)
    (data : SpinorialFlowJacobianData Map) (φ : Map) :
    (InfoGeometry.Canonical.OperatorSurprisal.surprisal β * N - N * InfoGeometry.Canonical.OperatorSurprisal.surprisal β = (2 * β) • N) ∧
    (poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ)) ∧
    (Real.exp (- data.redLinePotential φ) = data.jacobianDet φ) := ⟨
  surprisal_generates_modular_geometry β,
  surprisal_derham_cohomology_generator R hR n,
  redLine_potential_exp_recovery data φ
⟩

/-- Historical compatibility name for
`operatorSurprisal_logVolume_topological_packet`. -/
theorem surprisal_topological_geometry_unification
    (β : ℝ) (R : ℝ) (hR : 0 < R) (n : ℤ)
    (data : SpinorialFlowJacobianData Map) (φ : Map) :
    (InfoGeometry.Canonical.OperatorSurprisal.surprisal β * N -
        N * InfoGeometry.Canonical.OperatorSurprisal.surprisal β =
          (2 * β) • N) ∧
    (poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ)) ∧
    (Real.exp (- data.redLinePotential φ) = data.jacobianDet φ) :=
  operatorSurprisal_logVolume_topological_packet β R hR n data φ

end InfoGeometry.Canonical.SurprisalTopologicalGeometryGenerator
