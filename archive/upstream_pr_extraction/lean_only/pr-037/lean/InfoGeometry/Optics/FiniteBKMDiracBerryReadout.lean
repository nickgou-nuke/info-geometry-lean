import InfoGeometry.Optics.FiniteBKMDiracMetricReadout

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.FiniteBKMDiracBerryReadout

open CanonicalZornCliffordRepresentation
open InfoGeometry.Optics.FiniteBKMDiracMetricReadout
open InfoGeometry.Optics.FiniteBKMDiracTransport
open InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization
open InfoGeometry.Quantum.GeometricQuantumTensor
open InfoGeometry.Unified
open SouriauOnsagerBKM

/-- Normalized trace on the sixteen-component Zorn Dirac carrier. -/
def normalizedDiracTrace (A : Module.End ℂ DiracSpinor16) : ℂ :=
  (16 : ℂ)⁻¹ * LinearMap.trace ℂ DiracSpinor16 A

/-- Normalized Dirac trace recovers a scalar from its central operator
embedding. -/
@[simp] theorem normalizedDiracTrace_centralOperator (z : ℂ) :
    normalizedDiracTrace (centralOperator (W := DiracSpinor16) z) = z := by
  have htrace :
      LinearMap.trace ℂ DiracSpinor16
          (centralOperator (W := DiracSpinor16) z) = 16 * z := by
    simp [centralOperator]
    norm_num [CanonicalZornCompositionTriality.copy_finrank_eight]
    ring
  rw [normalizedDiracTrace, htrace]
  norm_num [div_eq_mul_inv]
  ring

theorem normalizedDiracTrace_add
    (A B : Module.End ℂ DiracSpinor16) :
    normalizedDiracTrace (A + B) =
      normalizedDiracTrace A + normalizedDiracTrace B := by
  simp [normalizedDiracTrace, mul_add]

theorem normalizedDiracTrace_smul
    (z : ℂ) (A : Module.End ℂ DiracSpinor16) :
    normalizedDiracTrace (z • A) = z * normalizedDiracTrace A := by
  simp [normalizedDiracTrace]
  ring

/-- Transporting a central finite operator to the Zorn Dirac carrier leaves
its scalar unchanged. -/
theorem diracTransport_centralOperator (z : ℂ) :
    finiteHilbertSixteenDiracEquiv.conjAlgEquiv ℂ
        (centralOperator (W := FiniteHilbertSpace 16) z) =
      centralOperator (W := DiracSpinor16) z := by
  apply LinearMap.ext
  intro v
  simp [centralOperator, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_apply]

/-- The antisymmetric channel of the transported QGT remains exactly the
central embedding of the genuine Berry two-form value. -/
@[simp] theorem diracBKMAndBerryQGT_antisymmetricBerry_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (observable : Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E)
    (i : Fin 4) :
    (diracBKMAndBerryQGT D observable berryOperator left right).antisymmetricBerry i =
      centralOperator (W := DiracSpinor16)
        ((berryOfOperator (E := E) (berryOperator i)
          (left i) (right i) : ℝ) : ℂ) := by
  exact diracTransport_centralOperator _

/-- The normalized trace of the antisymmetric Dirac-QGT channel recovers the
original operatorial Berry curvature without a dimension factor. -/
theorem normalizedDiracTrace_antisymmetricBerry_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (observable : Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E)
    (i : Fin 4) :
    normalizedDiracTrace
        ((diracBKMAndBerryQGT D observable berryOperator left right).antisymmetricBerry i) =
      ((berryOfOperator (E := E) (berryOperator i)
        (left i) (right i) : ℝ) : ℂ) := by
  rw [diracBKMAndBerryQGT_antisymmetricBerry_apply,
    normalizedDiracTrace_centralOperator]

/-- The two spectral readouts of an operator-valued QGT: a paired symmetric
metric coordinate and a normalized antisymmetric curvature coordinate. -/
def diracQGTSpectralReadout
    (Q : QGTFourVector DiracSpinor16)
    (B : FiniteOperatorAlgebra 16) (i : Fin 4) : ℂ × ℂ :=
  (LinearMap.trace ℂ DiracSpinor16
      (Q.symmetricBKM i * diracTransportOperator B),
    normalizedDiracTrace (Q.antisymmetricBerry i))

/-- Complete QGT readout theorem: the transported operator-valued channels
recover exactly the scalar BKM metric and Berry curvature coordinates. -/
theorem diracQGTSpectralReadout_eq_bkm_berry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (A B : FiniteOperatorAlgebra 16)
    (h_rpow : Continuous D.rpow)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E)
    (i : Fin 4) :
    diracQGTSpectralReadout
        (diracBKMAndBerryQGT D (fun _ => star A)
          berryOperator left right) B i =
      (D.kuboMoriPairing A B,
        ((berryOfOperator (E := E) (berryOperator i)
          (left i) (right i) : ℝ) : ℂ)) := by
  apply Prod.ext
  · exact (kuboMoriPairing_eq_trace_diracQGT_symmetricBKM
      D A B h_rpow berryOperator left right i).symm
  · exact normalizedDiracTrace_antisymmetricBerry_eq
      D (fun _ => star A) berryOperator left right i

/-- The normalized trace of the total complex QGT operator splits into its
symmetric trace coordinate plus `i` times the genuine Berry curvature. -/
theorem normalizedDiracTrace_totalOperator_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (observable : Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E)
    (i : Fin 4) :
    normalizedDiracTrace
        ((diracBKMAndBerryQGT D observable berryOperator left right).totalOperator i) =
      normalizedDiracTrace
          ((diracBKMAndBerryQGT D observable berryOperator left right).symmetricBKM i) +
        Complex.I *
          ((berryOfOperator (E := E) (berryOperator i)
            (left i) (right i) : ℝ) : ℂ) := by
  rw [QGTFourVector.totalOperator_apply, normalizedDiracTrace_add,
    normalizedDiracTrace_smul,
    normalizedDiracTrace_antisymmetricBerry_eq]

end InfoGeometry.Optics.FiniteBKMDiracBerryReadout
