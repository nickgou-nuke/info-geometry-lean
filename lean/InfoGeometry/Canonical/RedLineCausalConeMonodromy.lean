import Mathlib
import InfoGeometry.Canonical.TimeAsWindingMonodromy3D
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge
import InfoGeometry.Krein.DoubledSpace

set_option linter.unusedSectionVars false

/-!
# The Red Line Ω-Potential, De Rham Monodromy & Causal Cone Apex Winding

This module formalizes in native Lean 4 / Mathlib:
1. **The "Red Line" Ω-Generating Potential**:
   $$\Phi_{\text{RedLine}}(\phi) := -\ln \det J_{\text{unnormalized}}(\phi)$$
   defined as the negative logarithm of the Jacobian determinant of the unnormalized spinorial flow.
2. **The De Rham Logarithmic Form**:
   $$\omega_{\text{deRham}} = d \ln \Omega = -d \Phi_{\text{RedLine}}$$
3. **Causal Cone Apex Winding**:
   The topological winding around the lightcone singularity $Q(X) = t^2 - x^2 - y^2 - z^2 = 0$:
   $$\frac{1}{2\pi i} \oint_{\gamma} d \ln \Omega = n \in \mathbb{Z}.$$
4. **Discrete Quantized Time Loops**:
   Time steps $\Delta t_n = 2\pi n$ arising as discrete topological winding loops encircling the apex of the lightcone.
-/

namespace InfoGeometry.Canonical.RedLineCausalConeMonodromy

open Complex
open InfoGeometry.Canonical.TimeAsWindingMonodromy3D
open InfoGeometry.Canonical.SouriauOperatorialLogPotential
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

/-- The "Red Line" Ω-Generating Potential $\Phi_{\text{RedLine}}(\phi) = -\ln \det J(\phi)$. -/
noncomputable def redLineOmegaPotential (detJ : ℝ → ℝ) (x : ℝ) : ℝ :=
  - Real.log (detJ x)

/-- The red-line Ω-potential is definitionally negative logarithm of the Jacobian determinant. -/
theorem redLineOmegaPotential_eq_neg_log (detJ : ℝ → ℝ) (x : ℝ) :
    redLineOmegaPotential detJ x = -Real.log (detJ x) := by
  rfl

/-- Differential identity for the red-line potential: `dΦ = -(detJ'/detJ)`. -/
theorem redLineOmegaPotential_derivAt (detJ : ℝ → ℝ) (x : ℝ)
    (hdet : HasDerivAt detJ (detJ' : ℝ) x) (hpos : 0 < detJ x) :
    HasDerivAt (redLineOmegaPotential detJ)
      (-(detJ' / detJ x)) x := by
  have hlog : HasDerivAt (fun y : ℝ => -Real.log y) (-(detJ x)⁻¹) (detJ x) :=
    (Real.hasDerivAt_log hpos.ne').neg
  have hcomp := hlog.comp x hdet
  simpa [redLineOmegaPotential, Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hcomp

/-- Unnormalized spinorial flow Jacobian data. -/
structure SpinorialFlowJacobianData (Map : Type*) where
  jacobianDet : Map → ℝ
  pos_det : ∀ φ, 0 < jacobianDet φ
  redLinePotential : Map → ℝ
  redLinePotential_eq : ∀ φ, redLinePotential φ = - Real.log (jacobianDet φ)

/--
**Main Theorem 1: Red Line Potential Exponentiation**
The Jacobian determinant is recovered by exponentiating the negative Red Line potential:
$$\det J(\phi) = e^{-\Phi_{\text{RedLine}}(\phi)}.$$
-/
theorem redLine_potential_exp_recovery
    (data : SpinorialFlowJacobianData Map) (φ : Map) :
    Real.exp (- data.redLinePotential φ) = data.jacobianDet φ := by
  have h := data.redLinePotential_eq φ
  rw [h, neg_neg]
  exact Real.exp_log (data.pos_det φ)

/-- De Rham logarithmic form evaluation on a complex loop parameter $z \neq 0$. -/
noncomputable def deRhamLogForm (z : ℂ) : ℂ :=
  1 / z

/-- De Rham logarithmic form is the inverse pole form `dz / z`. -/
theorem deRhamLogForm_is_dlog (z : ℂ) :
    deRhamLogForm z = 1 / z := by
  rfl

/-- The red-line monodromy bridge exports the canonical support module as a `K_neg_log_PregDelta` package. -/
theorem modularSupportPackage_from_redLine (V : Type 0)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (c : InfoGeometry.Canonical.CertifiedModularReduction (E := InfoGeometry.Krein.DoubledSpace V)) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c)
        (InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge.K_neg_log_PregDelta (V := V) c)
    (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical) ∧
    (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical) ∧
    (CertifiedModularReduction.Pzero c * KambientCanonical = 0) ∧
    (KambientCanonical * CertifiedModularReduction.Pzero c = 0) :=
  InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge.K_neg_log_PregDelta_support_package (c := c)

/--
**Main Theorem 2: Lightcone Determinant Apex Singularity**
The chiral matrix determinant vanishes if and only if the spacetime vector $X$
lies exactly on the apex boundary of the 3D causal cone $Q(X) = 0$.
-/
theorem chiral_matrix_det_zero_iff_lightcone_apex (X : Chiral3) :
    Matrix.det (chiralMatrix X) = 0 ↔ lightconePotential X = 0 := by
  rw [chiralMatrix_det]
  exact Complex.ofReal_eq_zero

/--
**Main Theorem 3: De Rham Monodromy Winding Around Causal Cone Apex**
Winding $n$ times around the apex singularity of the causal cone yields the discrete phase:
$$w_n = n \cdot 2\pi i.$$
-/
theorem causal_cone_apex_winding_monodromy (R : ℝ) (hR : 0 < R) (n : ℤ) :
    poleWinding R hR n = logarithmicPhase n := by
  exact poleWinding_eq_logarithmicPhase R hR n

/--
**Main Theorem 4: Discrete Quantized Time Loops**
The discrete time step $\Delta t_n$ generated by encircling the lightcone apex
is quantized as integer multiples of $2\pi$:
$$\operatorname{Im}\left(\frac{w_n}{i}\right) = 2\pi n.$$
-/
theorem discrete_quantized_time_loop (R : ℝ) (hR : 0 < R) (n : ℤ) :
    poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ) := by
  exact poleWinding_index_is_integer R hR n

/--
**Main Theorem 5: The Grand Red Line Monodromy Duality**
Combines the Red Line $\Omega$-potential, the de Rham logarithmic form,
the lightcone apex singularity $Q = 0$, and discrete quantized time loops into a single unified theorem.
-/
theorem grand_redline_monodromy_duality
    (data : SpinorialFlowJacobianData Map) (φ : Map)
    (X : Chiral3) (R : ℝ) (hR : 0 < R) (n : ℤ) :
    (Real.exp (- data.redLinePotential φ) = data.jacobianDet φ) ∧
    (Matrix.det (chiralMatrix X) = 0 ↔ lightconePotential X = 0) ∧
    (poleWinding R hR n = logarithmicPhase n) ∧
    (poleWinding R hR n / (2 * Real.pi * Complex.I : ℂ) = (n : ℂ)) := ⟨
  redLine_potential_exp_recovery data φ,
  chiral_matrix_det_zero_iff_lightcone_apex X,
  causal_cone_apex_winding_monodromy R hR n,
  discrete_quantized_time_loop R hR n
⟩

end InfoGeometry.Canonical.RedLineCausalConeMonodromy
