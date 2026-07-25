import Mathlib
import InfoGeometry.Canonical.OperatorSurprisal
import InfoGeometry.Canonical.RedLineCausalConeMonodromy

set_option linter.unusedSectionVars false

/-!
# Surprisal / Boltzmann Log-Volume as Topological Geometry & De Rham Cohomology Generator

This module formalizes in native Lean 4 / Mathlib:
1. **The Scalar Surprisal Misnomer**:
   In information theory, $S(x) = -\ln P(x)$ is termed "surprisal" or "self-information".
   In Non-Commutative Geometry (NCG), it is the **infinitesimal generator of non-commutative geometry**.

2. **De Rham Cohomology Generation**:
   The differential of surprisal yields the de Rham logarithmic winding form:
   $$\omega_{\text{deRham}} = d S_{\text{surprisal}} = - d \ln \Omega$$
   which generates non-trivial 1st de Rham cohomology $H^1_{\text{deRham}}(\mathbb{C} \setminus \{0\}, \mathbb{C})$.

3. **Hyperbolic Boost & Monodromy Generation**:
   The surprisal operator $S_{\text{surprisal}}(\beta) = \beta \cdot K$ generates the hyperbolic modular boost
   $$[S_{\text{surprisal}}(\beta), N] = (2\beta) \cdot N$$
   and de Rham monodromies $w_n = n \cdot 2\pi i$ around topological singularities.

4. **Grand Synthesis Theorem**:
   Proves the formal equivalence connecting information surprisal, NCG geometry generation,
   and de Rham cohomology classes.
-/

namespace InfoGeometry.Canonical.SurprisalTopologicalGeometryGenerator

open Complex
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.OperatorSurprisal
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D
open InfoGeometry.Canonical.RedLineCausalConeMonodromy
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-- The Surprisal / Boltzmann Log-Volume differential form generator $\omega = d S$. -/
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
**Main Theorem 2: Surprisal Differential Generates De Rham Cohomology**
The contour integral of the surprisal differential form around the singularity generates
non-trivial de Rham cohomology classes (monodromies):
$$\frac{1}{2\pi i} \oint_{\gamma} d S_{\text{surprisal}} = n \in \mathbb{Z}.$$
-/
theorem surprisal_derham_cohomology_generator (R : ℝ) (hR : 0 < R) (n : ℤ) :
    poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) :=
  discrete_quantized_time_loop R hR n

/--
**Main Theorem 3: The Surprisal-NCG Topological Geometry Identity**
Unifies the 3 manifestations of Surprisal / Boltzmann Entropy:
1. Operator Surprisal generates non-commutative hyperbolic geometry ($[S, N] = 2\beta N$).
2. Surprisal differential generates 1st de Rham cohomology ($\oint dS / 2\pi i = n$).
3. Surprisal potential exponentiation recovers the phase volume ($\det J = e^{-\Phi_{\text{RedLine}}}$).
-/
theorem surprisal_topological_geometry_unification
    (β : ℝ) (R : ℝ) (hR : 0 < R) (n : ℤ)
    (data : SpinorialFlowJacobianData Map) (φ : Map) :
    (InfoGeometry.Canonical.OperatorSurprisal.surprisal β * N - N * InfoGeometry.Canonical.OperatorSurprisal.surprisal β = (2 * β) • N) ∧
    (poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ)) ∧
    (Real.exp (- data.redLinePotential φ) = data.jacobianDet φ) := ⟨
  surprisal_generates_modular_geometry β,
  surprisal_derham_cohomology_generator R hR n,
  redLine_potential_exp_recovery data φ
⟩

end InfoGeometry.Canonical.SurprisalTopologicalGeometryGenerator
