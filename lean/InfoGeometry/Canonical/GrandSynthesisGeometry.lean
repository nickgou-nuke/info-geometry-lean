import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Canonical.CalabiYauRNMongeAmpere
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.KaehlerGeometry
import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Canonical.SingularTransportSystem
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The Grand Unification of the Physics of Information in Lean 4

Capstone synthesis layer connecting thermodynamic Sinkhorn/KMS closure,
geometric Ricci/Calabi-Yau closure, and algebraic Bott-Dirac closure.
-/

open scoped TensorProduct
open scoped Kronecker

namespace InfoGeometry.Canonical.GrandSynthesis

open InfoGeometry.Krein
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.SpectralInference

section DeterminantChainRule

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Classical log-absolute determinant functional on square real matrices. -/
noncomputable def logAbsDetMatrix (A : Matrix m m ℝ) : ℝ :=
  Real.log (|Matrix.det A|)

/--
Classical determinant chain rule:
`log |det(AB)| = log |det A| + log |det B|`.
-/
lemma logAbsDetMatrix_mul
    (A B : Matrix m m ℝ)
    (hA : Matrix.det A ≠ 0)
    (hB : Matrix.det B ≠ 0) :
    logAbsDetMatrix (A * B) = logAbsDetMatrix A + logAbsDetMatrix B := by
  have hAabs : |Matrix.det A| ≠ 0 := abs_ne_zero.mpr hA
  have hBabs : |Matrix.det B| ≠ 0 := abs_ne_zero.mpr hB
  unfold logAbsDetMatrix
  rw [Matrix.det_mul, abs_mul, Real.log_mul hAabs hBabs]

variable {k : Type*} [Fintype k] [DecidableEq k]

/--
Tensor-product determinant decomposition:
`det(A ⊗ B) = det(A)^dim(B) * det(B)^dim(A)`, after `log|·|` this becomes
an additive entropy-scaling law.
-/
lemma logAbsDetMatrix_kronecker
    (A : Matrix m m ℝ) (B : Matrix k k ℝ)
    (hA : Matrix.det A ≠ 0)
    (hB : Matrix.det B ≠ 0) :
    logAbsDetMatrix (A ⊗ₖ B)
      = (Fintype.card k) * logAbsDetMatrix A
          + (Fintype.card m) * logAbsDetMatrix B := by
  have hAabs : |Matrix.det A| ≠ 0 := abs_ne_zero.mpr hA
  have hBabs : |Matrix.det B| ≠ 0 := abs_ne_zero.mpr hB
  have hAabsPow : |Matrix.det A| ^ Fintype.card k ≠ 0 :=
    pow_ne_zero _ hAabs
  have hBabsPow : |Matrix.det B| ^ Fintype.card m ≠ 0 :=
    pow_ne_zero _ hBabs
  unfold logAbsDetMatrix
  rw [Matrix.det_kronecker, abs_mul, abs_pow, abs_pow, Real.log_mul hAabsPow hBabsPow]
  rw [Real.log_pow, Real.log_pow]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Quantum-side Jacobian determinant functional on continuous endomorphisms. -/
noncomputable def jacDetCLM (L : E →L[ℝ] E) : ℝ :=
  LinearMap.det L.toLinearMap

/-- Jacobian chain rule (quantum/operator side): multiplicativity under composition. -/
lemma jacDetCLM_comp (L₁ L₂ : E →L[ℝ] E) :
    jacDetCLM (L₁.comp L₂) = jacDetCLM L₁ * jacDetCLM L₂ := by
  have _ : FiniteDimensional ℝ E := inferInstance
  simp [jacDetCLM, LinearMap.det_comp]

/-- Log-absolute Jacobian on continuous endomorphisms. -/
noncomputable def logAbsJacDetCLM (L : E →L[ℝ] E) : ℝ :=
  Real.log (|jacDetCLM L|)

/--
Quantum-side log-Jacobian chain rule:
`log |det(L₁ ∘ L₂)| = log |det L₁| + log |det L₂|`.
-/
lemma logAbsJacDetCLM_comp
    (L₁ L₂ : E →L[ℝ] E)
    (h₁ : jacDetCLM L₁ ≠ 0)
    (h₂ : jacDetCLM L₂ ≠ 0) :
    logAbsJacDetCLM (L₁.comp L₂) = logAbsJacDetCLM L₁ + logAbsJacDetCLM L₂ := by
  have h₁abs : |jacDetCLM L₁| ≠ 0 := abs_ne_zero.mpr h₁
  have h₂abs : |jacDetCLM L₂| ≠ 0 := abs_ne_zero.mpr h₂
  unfold logAbsJacDetCLM
  rw [jacDetCLM_comp, abs_mul, Real.log_mul h₁abs h₂abs]

end DeterminantChainRule

section SpectralVolumeForm

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Log-volume identity for Monge-Ampere density:
on the nondegenerate branch, `log ρ = log |det(∇²ψ)|`.
-/
private lemma log_mongeAmpereDensity_eq_logAbsDet_metricOp
    [FiniteDimensional ℝ E]
    (H : InfoGeometry.Convex.HessianGeometry E) (x : E)
    (hdet : LinearMap.det (H.metricOp x).toLinearMap ≠ 0) :
    Real.log (mongeAmpereDensity H x)
      = Real.log (|LinearMap.det (H.metricOp x).toLinearMap|) := by
  have hρ :
      mongeAmpereDensity H x = Real.exp (metricLogDet H x) :=
    mongeAmpereDensity_eq_exp_metricLogDet (H := H) (x := x) hdet
  rw [hρ, Real.log_exp]
  rfl

/-- Spectral specialization of the log-volume identity at the basepoint. -/
lemma log_spectralMongeAmpereDensity_eq_basepointLogVolume
    (IST : InfoSpectralTriple E)
    (h_det : LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap ≠ 0) :
    Real.log (spectralMongeAmpereDensity IST)
      = spectralBasepointLogVolume IST := by
  rw [spectralMongeAmpereDensity_eq_exp_spectralBasepointLogVolume IST h_det]
  rw [Real.log_exp]

variable {m : Type*} [Fintype m] [DecidableEq m]

/--
Determinant-model bridge:
if a matrix determinant models the Monge-Ampere density, then its log-absolute
determinant equals the Hessian metric-op log-absolute determinant.
-/
private lemma logAbsDet_metricModel_eq_logAbsDet_metricOp
    [FiniteDimensional ℝ E]
    (H : InfoGeometry.Convex.HessianGeometry E) (x : E) (A : Matrix m m ℝ)
    (h_det : LinearMap.det (H.metricOp x).toLinearMap ≠ 0)
    (hdet : Matrix.det A = mongeAmpereDensity H x) :
    logAbsDetMatrix A = Real.log (|LinearMap.det (H.metricOp x).toLinearMap|) := by
  unfold logAbsDetMatrix
  rw [hdet]
  rw [abs_of_pos (mongeAmpereDensity_pos (H := H) (x := x) h_det)]
  exact log_mongeAmpereDensity_eq_logAbsDet_metricOp (H := H) (x := x) h_det

/--
Spectral determinant-model bridge:
if a matrix determinant models the spectral Monge-Ampere density, then its
log-absolute determinant equals spectral volume.
-/
private lemma logAbsDet_spectralModel_eq_basepointLogVolume
    (IST : InfoSpectralTriple E) (A : Matrix m m ℝ)
    (h_det_m : LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap ≠ 0)
    (hdet : Matrix.det A = spectralMongeAmpereDensity IST) :
    logAbsDetMatrix A = spectralBasepointLogVolume IST := by
  unfold logAbsDetMatrix
  rw [hdet]
  have hpos : 0 < spectralMongeAmpereDensity IST := by
    rw [spectralMongeAmpereDensity_eq_exp_spectralBasepointLogVolume IST h_det_m]
    exact Real.exp_pos _
  rw [abs_of_pos hpos]
  exact log_spectralMongeAmpereDensity_eq_basepointLogVolume (IST := IST) h_det_m

end SpectralVolumeForm

section EntropicCalabiBridge

variable (n : Nat)
variable {X : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [FiniteDimensional ℝ X]

/--
Entropy-sourced geometric gravity statement:
RN/Kahler-potential sourcing plus unit relative-volume closure and a metric RN
bridge implies the vacuum Einstein equation on the `c = 0` branch (`scalar = 2Λ`).
-/
private theorem vacuumEinsteinEquation_of_rnEntropySource
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  have hUnitState : UnitRelativeVolumeState Kgeo := by
    intro x'
    simpa [RNEntropySourcesMongeAmpere, hUnit] using hSource x'
  exact vacuumEinsteinEquation_of_unitRelativeVolume
    (R := R) (K := Kgeo) (x := x) (Λ := Λ) hUnitState hBridge

/--
Capstone entropy-to-gravity statement:
if RN/Kahler entropy sources Monge-Ampere density and unit relative-volume closure
is equipped with a metric RN bridge, then the induced information geometry is Ricci-flat and satisfies
the vacuum Einstein equation (`c = 0`, `scalar = 2Λ`).
-/
private theorem gravity_generated_by_rnEntropy
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (hUnit : relativeVolumeChangeRN n M = 1)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  have hUnitState : UnitRelativeVolumeState Kgeo := by
    intro x'
    simpa [RNEntropySourcesMongeAmpere, hUnit] using hSource x'
  refine ⟨?_, ?_⟩
  · exact isRicciFlat_of_unitRelativeVolume
      (R := R) (K := Kgeo) (x := x) hUnitState hBridge
  · exact vacuumEinsteinEquation_of_rnEntropySource
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
      (M := M) hSource hUnit hBridge

end EntropicCalabiBridge

end InfoGeometry.Canonical.GrandSynthesis
