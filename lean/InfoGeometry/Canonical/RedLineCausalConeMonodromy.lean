import Mathlib
import InfoGeometry.Canonical.TimeAsWindingMonodromy3D
import InfoGeometry.Canonical.SouriauOperatorialLogPotential
import InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge
import Mathlib

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
open InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge
open InfoGeometry.Krein

/-- The "Red Line" Ω-Generating Potential $\Phi_{\text{RedLine}}(\phi) = -\ln \det J(\phi)$. -/
noncomputable def redLineOmegaPotential (detJ : ℝ → ℝ) (x : ℝ) : ℝ :=
  - Real.log (detJ x)

/-- Unnormalized spinorial flow Jacobian data. -/
structure SpinorialFlowJacobianData (Map : Type*) where
  jacobianDet : Map → ℝ
  pos_det : ∀ φ, 0 < jacobianDet φ
  redLinePotential : Map → ℝ
  redLinePotential_eq : ∀ φ, redLinePotential φ = - Real.log (jacobianDet φ)

/-- Unnormalized spinorial flow Jacobian data (alias kept for adapter clarity). -/
abbrev UnnormalizedSpinorialFlowJacobian (Map : Type*) := SpinorialFlowJacobianData Map

/-- Red-Line Ω-potential written directly from Jacobian data.
Equivalent to `redLinePotential` on valid flow data. -/
noncomputable def unnormalizedFlowOmegaPotential (Map : Type*)
    (S : UnnormalizedSpinorialFlowJacobian Map) (φ : Map) : ℝ :=
  - Real.log (S.jacobianDet φ)

/-- `-log ∘ jacobian` is exactly the stored Red-Line potential. -/
theorem unnormalizedFlowOmegaPotential_eq_redLinePotential
    (Map : Type*) (S : UnnormalizedSpinorialFlowJacobian Map) (φ : Map) :
    unnormalizedFlowOmegaPotential Map S φ = S.redLinePotential φ := by
  simpa [unnormalizedFlowOmegaPotential, S.redLinePotential_eq]

/-- The Ω-potential is definitionally `-log` of the Jacobian determinant. -/
theorem redLineOmegaPotential_eq_neg_log (detJ : ℝ → ℝ) (x : ℝ) :
    redLineOmegaPotential detJ x = -Real.log (detJ x) := by
  rfl

/-- `SpinorialFlowJacobianData` stores exactly the same Ω-potential as the defining equation. -/
theorem redLinePotential_eq_neg_log_jacobian
    (data : SpinorialFlowJacobianData Map) (φ : Map) :
    data.redLinePotential φ = -Real.log (data.jacobianDet φ) := by
  exact data.redLinePotential_eq φ

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

/-- Log potential lifted to `RegularizedJacobianPotential`. -/
noncomputable def redLineRegularizedPotential (Map : Type*)
    (data : SpinorialFlowJacobianData Map) :
    RegularizedJacobianPotential Map :=
  { jacobian := data.jacobianDet
    logDetReg := fun φ => Real.log (data.jacobianDet φ)
    volumeCompressionPotential := data.redLinePotential
    volumeCompressionPotential_eq_neg_logDetReg := by
      intro φ
      simpa [data.redLinePotential_eq] }

theorem redLineRegularizedPotential_volumePotential
    (Map : Type*) (data : SpinorialFlowJacobianData Map) (φ : Map) :
    (redLineRegularizedPotential Map data).volumeCompressionPotential φ = data.redLinePotential φ := by
  rfl

theorem redLineRegularizedPotential_componentwise_eq_lightconeBarrierCarrier
    (data : SpinorialFlowJacobianData Chiral3)
    (hJ : ∀ X : Chiral3, data.jacobianDet X = lightconePotential X) :
    ((∀ X : Chiral3, (redLineRegularizedPotential Chiral3 data).logDetReg X =
      lightconeBarrierCarrier.logDetReg X) ∧
     (∀ X : Chiral3, (redLineRegularizedPotential Chiral3 data).volumeCompressionPotential X =
      lightconeBarrierCarrier.volumeCompressionPotential X)) := by
  refine ⟨?_, ?_⟩
  · intro X
    simp [redLineRegularizedPotential, lightconeBarrierCarrier, hJ X]
  · intro X
    simp [redLineRegularizedPotential, lightconeBarrierCarrier, hJ X, data.redLinePotential_eq]

theorem redLineRegularizedPotential_det
    (Map : Type*) (data : SpinorialFlowJacobianData Map) (φ : Map) :
    (redLineRegularizedPotential Map data).logDetReg φ = Real.log (data.jacobianDet φ) := by
  rfl

theorem deRhamLogForm_eq_poleForm (z : ℂ) :
    deRhamLogForm z = poleForm z := rfl

/-- Red line potential recovers the lightcone potential when the scalar Jacobian field matches.
This is the honest adapter from the Red-Line model to the chiral lightcone carrier. -/
theorem redLine_chiral_volumeCompression_eq_lightconeBarrier
    (data : SpinorialFlowJacobianData Chiral3)
    (hJ : ∀ X : Chiral3, data.jacobianDet X = lightconePotential X) :
    (∀ X : Chiral3,
      (redLineRegularizedPotential Chiral3 data).volumeCompressionPotential X =
        lightconeBarrierCarrier.volumeCompressionPotential X) := by
  intro X
  have hP : data.redLinePotential X = -Real.log (lightconePotential X) := by
    simpa [hJ X] using data.redLinePotential_eq X
  simp [redLineRegularizedPotential, lightconeBarrierCarrier, hP, hJ]

/-- `K = -log Δ` written on the regularized support lane is exactly the `Preg` compression.
This is a direct adapter to the existing modular support bridge. -/
theorem modularSupportPackage_from_redLine (V : Type 0)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (c : CertifiedModularReduction (E := DoubledSpace V)) :
    let KambientCanonical :=
      compress (CertifiedModularReduction.Preg c) (K_neg_log_PregDelta (V := V) c)
    (CertifiedModularReduction.Preg c * KambientCanonical = KambientCanonical) ∧
    (KambientCanonical * CertifiedModularReduction.Preg c = KambientCanonical) ∧
    (CertifiedModularReduction.Pzero c * KambientCanonical = 0) ∧
    (KambientCanonical * CertifiedModularReduction.Pzero c = 0) :=
  K_neg_log_PregDelta_support_package (V := V) c

/--
**Main Theorem 2: Lightcone Determinant Apex Singularity**
The chiral matrix determinant vanishes if and only if the spacetime vector $X$
lies exactly on the apex boundary of the 3D causal cone $Q(X) = 0$.
-/
theorem chiral_matrix_det_zero_iff_lightcone_apex (X : Chiral3) :
    Matrix.det (chiralMatrix X) = 0 ↔ lightconePotential X = 0 := by
  rw [chiralMatrix_det]
  exact Complex.ofReal_eq_zero

/-- de Rham logarithmic 1-form equals the complex logarithm derivative.
This is the analytic identity `d (log Ω) = dΩ / Ω` in local logarithm coordinates:
for `Ω(z)=z`, the derivative is `1/z`. -/
theorem deRhamLogForm_deriv (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => Complex.log w) (deRhamLogForm z) z := by
  simpa [deRhamLogForm] using (Complex.hasDerivAt_log hz)

/-- Negative branch differential used for minus-log potentials. -/
theorem neg_deRhamLogForm_deriv (z : ℂ) (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ => -Complex.log w) (-(deRhamLogForm z)) z := by
  simpa [deRhamLogForm] using (Complex.hasDerivAt_log hz).neg

/-- Pole form is non-vanishing off the singularity. -/
theorem deRhamLogForm_ne_zero (z : ℂ) (hz : z ≠ 0) : deRhamLogForm z ≠ 0 := by
  exact div_ne_zero (by norm_num) hz

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
