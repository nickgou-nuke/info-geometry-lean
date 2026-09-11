import InfoGeometry.Optics.FiniteBKMDiracTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.FiniteBKMDiracMetricReadout

open CanonicalZornCliffordRepresentation
open InfoGeometry.Thermo.SusceptibilityOnsagerStress
open InfoGeometry.Optics.FiniteBKMDiracTransport
open InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization
open InfoGeometry.Unified
open SouriauOnsagerBKM

/-- Transport a finite sixteen-dimensional observable into the existing
Zorn Dirac endomorphism algebra. -/
def diracTransportOperator (A : FiniteOperatorAlgebra 16) :
    Module.End ℂ DiracSpinor16 :=
  finiteHilbertSixteenDiracEquiv.conjAlgEquiv ℂ A.toLinearMap

/-- Scalar metric readout of the transported BKM operator channel. -/
def diracBKMMetricReadout
    (D : FaithfulDensityOperator 16)
    (A B : FiniteOperatorAlgebra 16) : ℂ :=
  LinearMap.trace ℂ DiracSpinor16
    (diracTransportOperator (D.kuboMoriTransform (star A)) *
      diracTransportOperator B)

/-- Exact operator-lift theorem: the scalar Onsager--BKM pairing is the trace
readout of the corresponding product of transported Dirac operators. -/
theorem kuboMoriPairing_eq_diracBKMMetricReadout
    (D : FaithfulDensityOperator 16)
    (A B : FiniteOperatorAlgebra 16)
    (h_rpow : Continuous D.rpow) :
    D.kuboMoriPairing A B = diracBKMMetricReadout D A B := by
  rw [D.kuboMoriPairing_eq_trace_kuboMoriTransform A B h_rpow,
    finiteOperatorTrace_eq_linearMap_trace]
  unfold diracBKMMetricReadout diracTransportOperator
  rw [← map_mul]
  exact (LinearMap.trace_conj'
    ((D.kuboMoriTransform (star A)).toLinearMap * B.toLinearMap)
    finiteHilbertSixteenDiracEquiv).symm

/-- The transported metric readout inherits Hermitian symmetry from the
genuine BKM pairing. -/
theorem diracBKMMetricReadout_conj_symm
    (D : FaithfulDensityOperator 16)
    (A B : FiniteOperatorAlgebra 16)
    (h_rpow : Continuous D.rpow) :
    star (diracBKMMetricReadout D A B) =
      diracBKMMetricReadout D B A := by
  rw [← kuboMoriPairing_eq_diracBKMMetricReadout D A B h_rpow,
    ← kuboMoriPairing_eq_diracBKMMetricReadout D B A h_rpow]
  exact D.kuboMoriPairing_conj_symm_of_continuous_rpow A B h_rpow

/-- The native real BKM bilinear form is exactly the real part of the Dirac
operator trace readout. -/
theorem bkmRealBilinForm_eq_diracBKMMetricReadout_re
    (D : FaithfulDensityOperator 16)
    (h_rpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra 16) :
    D.bkmRealBilinForm h_rpow A B =
      (diracBKMMetricReadout D A B).re := by
  rw [D.bkmRealBilinForm_apply,
    kuboMoriPairing_eq_diracBKMMetricReadout D A B h_rpow]

/-- The positive Onsager form, under its explicit diagonal-positivity
hypothesis, is realized by the same transported Dirac trace. -/
theorem bkmOnsagerForm_eq_diracBKMMetricReadout_re
    (D : FaithfulDensityOperator 16)
    (h_rpow : Continuous D.rpow)
    (h_nonneg : ∀ A : FiniteOperatorAlgebra 16,
      0 ≤ (D.kuboMoriPairing A A).re)
    (A B : FiniteOperatorAlgebra 16) :
    (D.bkmOnsagerForm h_rpow h_nonneg).form A B =
      (diracBKMMetricReadout D A B).re := by
  rw [D.bkmOnsagerForm_apply,
    kuboMoriPairing_eq_diracBKMMetricReadout D A B h_rpow]

/-- Positivity of the native BKM Onsager form becomes nonnegativity of the
diagonal Dirac operator metric readout. -/
theorem diracBKMMetricReadout_re_nonnegative
    (D : FaithfulDensityOperator 16)
    (h_rpow : Continuous D.rpow)
    (h_nonneg : ∀ A : FiniteOperatorAlgebra 16,
      0 ≤ (D.kuboMoriPairing A A).re)
    (A : FiniteOperatorAlgebra 16) :
    0 ≤ (diracBKMMetricReadout D A A).re := by
  rw [← kuboMoriPairing_eq_diracBKMMetricReadout D A A h_rpow]
  exact h_nonneg A

/-- The symmetric channel of the transported QGT contains precisely the
Dirac transport of the integrated Kubo--Mori transform. -/
@[simp] theorem diracBKMAndBerryQGT_symmetricBKM_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (observable : Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E)
    (i : Fin 4) :
    (diracBKMAndBerryQGT D observable berryOperator left right).symmetricBKM i =
      diracTransportOperator (D.kuboMoriTransform (observable i)) :=
  rfl

/-- Reading the symmetric QGT channel against a transported observable
recovers the genuine scalar BKM metric.  The Berry channel is present in the
same QGT but does not contaminate this symmetric readout. -/
theorem kuboMoriPairing_eq_trace_diracQGT_symmetricBKM
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (A B : FiniteOperatorAlgebra 16)
    (h_rpow : Continuous D.rpow)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E)
    (i : Fin 4) :
    D.kuboMoriPairing A B =
      LinearMap.trace ℂ DiracSpinor16
        ((diracBKMAndBerryQGT D (fun _ => star A)
          berryOperator left right).symmetricBKM i *
          diracTransportOperator B) := by
  rw [diracBKMAndBerryQGT_symmetricBKM_apply]
  exact kuboMoriPairing_eq_diracBKMMetricReadout D A B h_rpow

end InfoGeometry.Optics.FiniteBKMDiracMetricReadout
