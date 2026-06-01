import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Canonical.CalabiYauRNMongeAmpere
import InfoGeometry.Canonical.IncompressibleBitBridge
import InfoGeometry.Canonical.KMSSinkhornSeedState
import InfoGeometry.Canonical.KMSSinkhornScalarPotential
import InfoGeometry.Canonical.KMSSinkhornWeightedTransport
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
open InfoGeometry.Canonical.IncompressibleBitBridge
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

omit [FiniteDimensional ℝ E] in
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

omit [FiniteDimensional ℝ E] in
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

omit [FiniteDimensional ℝ X] in
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
  exact
    InfoGeometry.Canonical.CalabiYauBridge.vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolume
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
      (M := M) hSource hUnit hBridge

/--
Proof-carrying entropy/unit-volume packet for the RN -> gravity lane.

This bundles the concrete Sinkhorn model together with the RN-entropy source and
the constructive `UnitRelativeVolumeBit`, so downstream gravity theorems can
consume one witness packet instead of separately threading `M`, `hSource`, and
`bit`.
-/
structure RNEntropyUnitRelativeVolumeWitness
    (Kgeo : KaehlerInformationGeometry X) where
  /-- Concrete Sinkhorn model feeding the RN/Monge-Ampere lane. -/
  M : SinkhornMatrix n
  /-- RN/Kähler source of the Monge-Ampère density. -/
  hSource : RNEntropySourcesMongeAmpere n Kgeo M
  /-- Proof-carrying unit relative-volume closure for the same model. -/
  bit : UnitRelativeVolumeBit n M

omit [FiniteDimensional ℝ X] in
/--
Recover the geometric unit-volume state from the bundled RN source / unit-bit
witness.
-/
theorem unitRelativeVolumeState_of_rnEntropyWitness
    (Kgeo : KaehlerInformationGeometry X)
    (W : RNEntropyUnitRelativeVolumeWitness (n := n) Kgeo) :
    UnitRelativeVolumeState Kgeo := by
  exact unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolumeBit
    (n := n) (Kgeo := Kgeo) (M := W.M) W.hSource W.bit

omit [FiniteDimensional ℝ X] in
/--
Entropy-sourced geometric gravity statement through the proof-carrying unit
relative-volume bit.

This is the constructive route for callers that own the incompressible RN bit:
the raw equality `relativeVolumeChangeRN n M = 1` is recovered from
`bit.unit_relative_volume`, then the existing Calabi-Yau/RN owner theorem is
reused unchanged.
-/
theorem vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolumeBit
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (bit : UnitRelativeVolumeBit n M)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact vacuumEinsteinEquation_of_rnEntropySource
    (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (M := M) hSource bit.unit_relative_volume hBridge

omit [FiniteDimensional ℝ X] in
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
  exact
    InfoGeometry.Canonical.CalabiYauBridge.isRicciFlat_and_vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolume
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
      (M := M) hSource hUnit hBridge

omit [FiniteDimensional ℝ X] in
/--
Vacuum Einstein equation from the already-constructed unit-volume state.

This façade export removes the RN-entropy source theorem and
`UnitRelativeVolumeBit` packet from the vacuum-equation surface when callers
already own the geometric `UnitRelativeVolumeState Kgeo` consumed by
`MetricRNRicciBridge`.
-/
theorem vacuumEinsteinEquation_of_unitRelativeVolumeState
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (hUnitState : UnitRelativeVolumeState Kgeo)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact vacuumEinsteinEquation_of_unitRelativeVolume
    (R := R) (K := Kgeo) (x := x) (Λ := Λ) hUnitState hBridge

omit [FiniteDimensional ℝ X] in
/--
Gravity capstone from the already-constructed unit-volume state.

This is the smallest non-metric-derived owner route in this module: it no
longer asks callers to re-supply the RN-entropy source theorem or the
`UnitRelativeVolumeBit` packet when they already own the geometric
`UnitRelativeVolumeState Kgeo` consumed by `MetricRNRicciBridge`.
-/
theorem gravity_generated_by_unitRelativeVolumeState
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (hUnitState : UnitRelativeVolumeState Kgeo)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact ⟨
    isRicciFlat_of_unitRelativeVolume
      (R := R) (K := Kgeo) (x := x) hUnitState hBridge,
    vacuumEinsteinEquation_of_unitRelativeVolumeState
      (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ) hUnitState hBridge⟩

omit [FiniteDimensional ℝ X] in
/--
Entropy-to-gravity capstone through the bundled RN source / unit-volume witness.

This removes the explicit triple `(M, hSource, bit)` from the public surface:
callers provide one constructive packet, which is first converted into
`UnitRelativeVolumeState Kgeo` and then routed through the existing smaller
owner theorem `gravity_generated_by_unitRelativeVolumeState`.
-/
theorem gravity_generated_by_rnEntropyWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : RNEntropyUnitRelativeVolumeWitness (n := n) Kgeo)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact gravity_generated_by_unitRelativeVolumeState
    (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (unitRelativeVolumeState_of_rnEntropyWitness (n := n) (Kgeo := Kgeo) W)
    hBridge

omit [FiniteDimensional ℝ X] in
/--
Entropy-to-vacuum route through the bundled RN source / unit-volume witness.

This removes the explicit triple `(M, hSource, bit)` from the non-metric-derived
vacuum-equation surface: callers provide one constructive packet, which is
first converted into `UnitRelativeVolumeState Kgeo` and then routed through the
existing smaller owner theorem.
-/
theorem vacuumEinsteinEquation_of_rnEntropyWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : RNEntropyUnitRelativeVolumeWitness (n := n) Kgeo)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact vacuumEinsteinEquation_of_unitRelativeVolumeState
    (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (unitRelativeVolumeState_of_rnEntropyWitness (n := n) (Kgeo := Kgeo) W)
    hBridge

/--
Proof-carrying RN-entropy / metric-RN-Ricci witness on the non-metric-derived
gravity lane.

This bundles the existing constructive RN-entropy / unit-relative-volume packet
with the `MetricRNRicciBridge` needed by the Ricci-flat / vacuum-Einstein owner
routes, removing the explicit pair `(W, hBridge)` from downstream surfaces.
-/
structure RNEntropyMetricRNRicciWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) where
  rnEntropy : RNEntropyUnitRelativeVolumeWitness (n := n) Kgeo
  hBridge : MetricRNRicciBridge R Kgeo x

namespace RNEntropyMetricRNRicciWitness

omit [FiniteDimensional ℝ X] in
/-- Recover the unit-relative-volume state from the bundled non-metric witness. -/
theorem unitRelativeVolumeState
    {Kgeo : KaehlerInformationGeometry X}
    {R : RicciTensor X}
    {x : X}
    (W : RNEntropyMetricRNRicciWitness (n := n) (Kgeo := Kgeo) R x) :
    UnitRelativeVolumeState Kgeo :=
  unitRelativeVolumeState_of_rnEntropyWitness (n := n) (Kgeo := Kgeo) W.rnEntropy

omit [FiniteDimensional ℝ X] in
/-- Recover the metric RN/Ricci bridge from the bundled non-metric witness. -/
theorem metricRNRicciBridge
    {Kgeo : KaehlerInformationGeometry X}
    {R : RicciTensor X}
    {x : X}
    (W : RNEntropyMetricRNRicciWitness (n := n) (Kgeo := Kgeo) R x) :
    MetricRNRicciBridge R Kgeo x :=
  W.hBridge

end RNEntropyMetricRNRicciWitness

omit [FiniteDimensional ℝ X] in
/--
Entropy-to-gravity capstone from one proof-carrying RN-entropy / metric-RN-Ricci
witness packet.

This removes the explicit pair `(W, hBridge)` from the non-metric-derived
gravity surface: callers provide one constructive packet, which is first
converted into `UnitRelativeVolumeState Kgeo` and then routed through the
existing smaller owner theorem `gravity_generated_by_unitRelativeVolumeState`.
-/
theorem gravity_generated_by_rnEntropyMetricRNRicciWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : RNEntropyMetricRNRicciWitness (n := n) (Kgeo := Kgeo) R x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact gravity_generated_by_unitRelativeVolumeState
    (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (RNEntropyMetricRNRicciWitness.unitRelativeVolumeState (n := n) W)
    (RNEntropyMetricRNRicciWitness.metricRNRicciBridge (n := n) W)

omit [FiniteDimensional ℝ X] in
/--
Entropy-to-vacuum route from one proof-carrying RN-entropy / metric-RN-Ricci
witness packet.

This removes the explicit pair `(W, hBridge)` from the non-metric-derived
vacuum-Einstein surface.
-/
theorem vacuumEinsteinEquation_of_rnEntropyMetricRNRicciWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : RNEntropyMetricRNRicciWitness (n := n) (Kgeo := Kgeo) R x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact
    (gravity_generated_by_rnEntropyMetricRNRicciWitness
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ) W).2

omit [FiniteDimensional ℝ X] in
/--
Entropy-sourced Ricci-flatness from one proof-carrying RN-entropy /
metric-RN-Ricci witness packet.

This removes the explicit pair `(W, hBridge)` from the direct Ricci-flatness
surface on the non-metric-derived RN-entropy lane.
-/
theorem isRicciFlat_of_rnEntropyMetricRNRicciWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X)
    (W : RNEntropyMetricRNRicciWitness (n := n) (Kgeo := Kgeo) R x) :
    IsRicciFlat R := by
  exact
    (gravity_generated_by_rnEntropyMetricRNRicciWitness
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := 0) W).1

omit [FiniteDimensional ℝ X] in
/--
Entropy-sourced Ricci-flat route through the proof-carrying unit relative-volume
bit.

This narrows the Ricci-flat surface from a bare RN equality to the existing
constructive `UnitRelativeVolumeBit` packet.
-/
theorem isRicciFlat_of_rnEntropySource_of_unitRelativeVolumeBit
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (bit : UnitRelativeVolumeBit n M)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R := by
  have hUnitState : UnitRelativeVolumeState Kgeo :=
    unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolumeBit
      (n := n) (Kgeo := Kgeo) (M := M) hSource bit
  exact isRicciFlat_of_unitRelativeVolume
    (R := R) (K := Kgeo) (x := x) hUnitState hBridge

omit [FiniteDimensional ℝ X] in
/--
Capstone entropy-to-gravity statement through the proof-carrying unit
relative-volume bit.

This narrows the public hypothesis surface from a bare RN equality to the
existing constructive `UnitRelativeVolumeBit` packet while preserving the old
raw-equality route above for compatibility.
-/
theorem gravity_generated_by_rnEntropy_of_unitRelativeVolumeBit
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (bit : UnitRelativeVolumeBit n M)
    (hBridge : MetricRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact ⟨
    isRicciFlat_of_rnEntropySource_of_unitRelativeVolumeBit
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (M := M) hSource bit hBridge,
    vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolumeBit
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ) (M := M) hSource bit hBridge
  ⟩

/--
Metric-derived entropy-to-vacuum route through the proof-carrying unit-volume
bit.  This narrowed branch removes the bare `MetricRNRicciBridge` implication
from the capstone surface: callers may instead provide the constructive
metric-derived package identifying `R` with `ricciFromMetricOp`, nondegeneracy,
log-det differentiability, and the unit-volume Ricci-zero readback.
-/
theorem vacuumEinsteinEquation_of_rnEntropySource_of_unitRelativeVolumeBit_metricDerived
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (bit : UnitRelativeVolumeBit n M)
    (hM : MetricDerivedRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  have hUnitState : UnitRelativeVolumeState Kgeo :=
    unitRelativeVolumeState_of_rnEntropySource_of_unitRelativeVolume
      (n := n) (Kgeo := Kgeo) (M := M) hSource bit.unit_relative_volume
  exact vacuumEinsteinEquation_of_unitRelativeVolume_metricDerived
    (R := R) (K := Kgeo) (x := x) (Λ := Λ) hUnitState hM

/--
Metric-derived vacuum equation from the already-constructed unit-volume state.

This narrowed branch removes the RN-entropy source theorem and
`UnitRelativeVolumeBit` packet from the vacuum-equation surface when callers
already own the geometric `UnitRelativeVolumeState Kgeo` consumed by
`MetricDerivedRNRicciBridge`.
-/
theorem vacuumEinsteinEquation_of_unitRelativeVolumeState_metricDerived
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (hUnitState : UnitRelativeVolumeState Kgeo)
    (hM : MetricDerivedRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact vacuumEinsteinEquation_of_unitRelativeVolume_metricDerived
    (R := R) (K := Kgeo) (x := x) (Λ := Λ) hUnitState hM

/--
Metric-derived gravity capstone from the already-constructed unit-volume state.

This is the smallest owner route in this module: it no longer asks callers to
re-supply the RN-entropy source theorem or the `UnitRelativeVolumeBit` packet
when they already own the geometric `UnitRelativeVolumeState Kgeo` consumed by
`MetricDerivedRNRicciBridge`.
-/
theorem gravity_generated_by_unitRelativeVolumeState_metricDerived
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (hUnitState : UnitRelativeVolumeState Kgeo)
    (hM : MetricDerivedRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact ⟨
    isRicciFlat_of_unitRelativeVolume_metricDerived
      (R := R) (K := Kgeo) (x := x) hUnitState hM,
    vacuumEinsteinEquation_of_unitRelativeVolume_metricDerived
      (R := R) (K := Kgeo) (x := x) (Λ := Λ) hUnitState hM⟩

/--
Proof-carrying metric-derived gravity witness on the unit-relative-volume lane.

This is the next constructive narrowing after
`gravity_generated_by_unitRelativeVolumeState_metricDerived`: callers provide one
witness packet carrying both the geometric unit-relative-volume state and the
metric-derived RN/Ricci bridge, instead of threading the pair
`(hUnitState, hM)` separately.
-/
structure MetricDerivedUnitRelativeVolumeStateWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) where
  hUnitState : UnitRelativeVolumeState Kgeo
  hM : MetricDerivedRNRicciBridge R Kgeo x

namespace MetricDerivedUnitRelativeVolumeStateWitness

/-- Recover the unit-relative-volume state from the proof-carrying witness. -/
theorem unitRelativeVolumeState
    {Kgeo : KaehlerInformationGeometry X}
    {R : RicciTensor X}
    {x : X}
    (W : MetricDerivedUnitRelativeVolumeStateWitness (Kgeo := Kgeo) R x) :
    UnitRelativeVolumeState Kgeo :=
  W.hUnitState

/-- Recover the metric-derived RN/Ricci bridge from the proof-carrying witness. -/
theorem metricDerivedBridge
    {Kgeo : KaehlerInformationGeometry X}
    {R : RicciTensor X}
    {x : X}
    (W : MetricDerivedUnitRelativeVolumeStateWitness (Kgeo := Kgeo) R x) :
    MetricDerivedRNRicciBridge R Kgeo x :=
  W.hM

end MetricDerivedUnitRelativeVolumeStateWitness

/--
Proof-carrying metric-derived entropy witness on the RN/unit-volume lane.

This is the next constructive narrowing after
`gravity_generated_by_rnEntropyWitness_metricDerived`: callers provide one
witness packet carrying both the RN/unit-relative-volume source data and the
metric-derived RN/Ricci bridge, instead of threading the pair `(W, hM)`
separately.
-/
structure MetricDerivedRNEntropyUnitRelativeVolumeWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) where
  rnEntropy : RNEntropyUnitRelativeVolumeWitness (n := n) Kgeo
  hM : MetricDerivedRNRicciBridge R Kgeo x

namespace MetricDerivedRNEntropyUnitRelativeVolumeWitness

/--
Construct the bundled metric-derived RN-entropy witness directly from the
concrete RN source, proof-carrying unit-relative-volume bit, and the
metric-derived RN/Ricci bridge.

This is the smallest constructive constructor on the metric-derived bit lane:
callers no longer need to manually assemble the nested RN witness packet before
using the one-packet gravity/vacuum routes.
-/
def ofSourceAndBit
    {Kgeo : KaehlerInformationGeometry X}
    {R : RicciTensor X}
    {x : X}
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (bit : UnitRelativeVolumeBit n M)
    (hM : MetricDerivedRNRicciBridge R Kgeo x) :
    MetricDerivedRNEntropyUnitRelativeVolumeWitness (n := n) (Kgeo := Kgeo) R x where
  rnEntropy :=
    { M := M
      hSource := hSource
      bit := bit }
  hM := hM

/--
Recover the smaller metric-derived unit-relative-volume witness from the bundled
RN-entropy / metric-derived packet.
-/
theorem toMetricDerivedUnitRelativeVolumeStateWitness
    {Kgeo : KaehlerInformationGeometry X}
    {R : RicciTensor X}
    {x : X}
    (W : MetricDerivedRNEntropyUnitRelativeVolumeWitness (n := n) (Kgeo := Kgeo) R x) :
    MetricDerivedUnitRelativeVolumeStateWitness (Kgeo := Kgeo) R x where
  hUnitState := unitRelativeVolumeState_of_rnEntropyWitness
    (n := n) (Kgeo := Kgeo) W.rnEntropy
  hM := W.hM

/--
Recover the unit-relative-volume state directly from the bundled RN-entropy /
metric-derived witness.

This is the smallest one-way owner export on the metric-derived RN-entropy lane:
downstream callers that already own the bundled witness no longer need to reopen
`rnEntropy` manually to obtain `UnitRelativeVolumeState Kgeo`.
-/
theorem unitRelativeVolumeState
    {Kgeo : KaehlerInformationGeometry X}
    {R : RicciTensor X}
    {x : X}
    (W : MetricDerivedRNEntropyUnitRelativeVolumeWitness (n := n) (Kgeo := Kgeo) R x) :
    UnitRelativeVolumeState Kgeo :=
  unitRelativeVolumeState_of_rnEntropyWitness (n := n) (Kgeo := Kgeo) W.rnEntropy

/--
Recover the metric-derived RN/Ricci bridge directly from the bundled RN-entropy /
metric-derived witness.

This removes the need for downstream callers to thread the bridge hypothesis
separately once they already own the larger constructive packet.
-/
theorem metricDerivedBridge
    {Kgeo : KaehlerInformationGeometry X}
    {R : RicciTensor X}
    {x : X}
    (W : MetricDerivedRNEntropyUnitRelativeVolumeWitness (n := n) (Kgeo := Kgeo) R x) :
    MetricDerivedRNRicciBridge R Kgeo x :=
  W.hM

end MetricDerivedRNEntropyUnitRelativeVolumeWitness

/--
Metric-derived gravity capstone from one proof-carrying witness packet.

This removes the explicit pair `(hUnitState, hM)` from the metric-derived owner
surface by routing through `MetricDerivedUnitRelativeVolumeStateWitness`.
-/
theorem gravity_generated_by_metricDerivedUnitRelativeVolumeStateWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : MetricDerivedUnitRelativeVolumeStateWitness (Kgeo := Kgeo) R x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact gravity_generated_by_unitRelativeVolumeState_metricDerived
    (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    W.hUnitState W.hM

/--
Metric-derived vacuum equation from one proof-carrying unit-relative-volume
witness packet.

This removes the explicit pair `(hUnitState, hM)` from the direct
vacuum-equation surface on the smallest metric-derived owner lane.
-/
theorem vacuumEinsteinEquation_of_metricDerivedUnitRelativeVolumeStateWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : MetricDerivedUnitRelativeVolumeStateWitness (Kgeo := Kgeo) R x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact
    (gravity_generated_by_metricDerivedUnitRelativeVolumeStateWitness
      (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ) W).2

/--
Metric-derived Ricci-flatness from one proof-carrying unit-relative-volume
witness packet.

This removes the explicit pair `(hUnitState, hM)` from the direct Ricci-flatness
surface on the smallest metric-derived owner lane.
-/
theorem isRicciFlat_of_metricDerivedUnitRelativeVolumeStateWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X)
    (W : MetricDerivedUnitRelativeVolumeStateWitness (Kgeo := Kgeo) R x) :
    IsRicciFlat R := by
  exact
    (gravity_generated_by_metricDerivedUnitRelativeVolumeStateWitness
      (Kgeo := Kgeo) (R := R) (x := x) (Λ := 0) W).1

/--
Metric-derived entropy-to-gravity capstone from one proof-carrying witness
packet.

This removes the explicit pair `(W, hM)` from the metric-derived RN-entropy
gravity surface: callers provide one constructive packet, which is first
converted into `MetricDerivedUnitRelativeVolumeStateWitness` and then routed
through the existing smaller owner theorem.
-/
theorem gravity_generated_by_metricDerivedRNEntropyUnitRelativeVolumeWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : MetricDerivedRNEntropyUnitRelativeVolumeWitness (n := n) (Kgeo := Kgeo) R x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact gravity_generated_by_metricDerivedUnitRelativeVolumeStateWitness
    (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (MetricDerivedRNEntropyUnitRelativeVolumeWitness.toMetricDerivedUnitRelativeVolumeStateWitness
      (n := n) W)

/--
Metric-derived vacuum equation from one proof-carrying RN-entropy / metric-derived
witness packet.

This removes the remaining explicit metric-derived bridge hypothesis from the
metric-derived vacuum-equation surface: callers provide one
`MetricDerivedRNEntropyUnitRelativeVolumeWitness`, which is routed through the
existing smaller metric-derived gravity theorem and then projected to its vacuum
Einstein component.
-/
theorem vacuumEinsteinEquation_of_metricDerivedRNEntropyUnitRelativeVolumeWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : MetricDerivedRNEntropyUnitRelativeVolumeWitness (n := n) (Kgeo := Kgeo) R x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact
    (gravity_generated_by_metricDerivedRNEntropyUnitRelativeVolumeWitness
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ) W).2

/--
Metric-derived Ricci-flatness from one proof-carrying RN-entropy / metric-derived
witness packet.

This is the direct theorem surface for callers that only need Ricci-flatness:
it removes the remaining explicit metric-derived bridge hypothesis from the
metric-derived RN-entropy lane by consuming
`MetricDerivedRNEntropyUnitRelativeVolumeWitness` directly.
-/
theorem isRicciFlat_of_metricDerivedRNEntropyUnitRelativeVolumeWitness
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X)
    (W : MetricDerivedRNEntropyUnitRelativeVolumeWitness (n := n) (Kgeo := Kgeo) R x) :
    IsRicciFlat R := by
  exact
    (gravity_generated_by_metricDerivedRNEntropyUnitRelativeVolumeWitness
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := 0) W).1

/--
Metric-derived vacuum equation through the bundled RN source / unit-volume
witness.

This removes the explicit triple `(M, hSource, bit)` from the metric-derived
vacuum-equation surface: callers provide one constructive witness packet, which
is first converted into `UnitRelativeVolumeState Kgeo` and then routed through
the existing smaller metric-derived owner theorem.
-/
theorem vacuumEinsteinEquation_of_rnEntropyWitness_metricDerived
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : RNEntropyUnitRelativeVolumeWitness (n := n) Kgeo)
    (hM : MetricDerivedRNRicciBridge R Kgeo x) :
    VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact vacuumEinsteinEquation_of_unitRelativeVolumeState_metricDerived
    (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (unitRelativeVolumeState_of_rnEntropyWitness (n := n) (Kgeo := Kgeo) W)
    hM

/--
Metric-derived Ricci-flatness through the bundled RN source / unit-volume
witness.

This is the direct theorem surface for callers that only need Ricci-flatness:
it removes the explicit triple `(M, hSource, bit)` and routes the derived
`UnitRelativeVolumeState` into the metric-derived owner theorem.
-/
theorem isRicciFlat_of_rnEntropyWitness_metricDerived
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X)
    (W : RNEntropyUnitRelativeVolumeWitness (n := n) Kgeo)
    (hM : MetricDerivedRNRicciBridge R Kgeo x) :
    IsRicciFlat R := by
  exact isRicciFlat_of_unitRelativeVolume_metricDerived
    (R := R) (K := Kgeo) (x := x)
    (unitRelativeVolumeState_of_rnEntropyWitness (n := n) (Kgeo := Kgeo) W)
    hM

/--
Metric-derived entropy-to-gravity capstone through the bundled RN source /
unit-volume witness.

This removes the explicit triple `(M, hSource, bit)` from the metric-derived
gravity surface: callers provide one constructive witness packet, which is
first converted into `UnitRelativeVolumeState Kgeo` and then routed through the
existing smaller metric-derived owner theorem.
-/
theorem gravity_generated_by_rnEntropyWitness_metricDerived
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (W : RNEntropyUnitRelativeVolumeWitness (n := n) Kgeo)
    (hM : MetricDerivedRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact gravity_generated_by_unitRelativeVolumeState_metricDerived
    (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (unitRelativeVolumeState_of_rnEntropyWitness (n := n) (Kgeo := Kgeo) W)
    hM

/--
Metric-derived entropy-to-gravity capstone through the proof-carrying unit-volume
bit.  This keeps the compatibility theorem above for `MetricRNRicciBridge`
callers while routing through the smaller `UnitRelativeVolumeState` owner route.
-/
theorem gravity_generated_by_rnEntropy_of_unitRelativeVolumeBit_metricDerived
    (Kgeo : KaehlerInformationGeometry X)
    (R : RicciTensor X)
    (x : X) (Λ : ℝ)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (bit : UnitRelativeVolumeBit n M)
    (hM : MetricDerivedRNRicciBridge R Kgeo x) :
    IsRicciFlat R ∧ VacuumEinsteinEquationAt R Kgeo x (2 * Λ) Λ := by
  exact gravity_generated_by_metricDerivedRNEntropyUnitRelativeVolumeWitness
    (n := n) (Kgeo := Kgeo) (R := R) (x := x) (Λ := Λ)
    (MetricDerivedRNEntropyUnitRelativeVolumeWitness.ofSourceAndBit
      (n := n) (Kgeo := Kgeo) (R := R) (x := x) M hSource bit hM)

end EntropicCalabiBridge

end InfoGeometry.Canonical.GrandSynthesis
