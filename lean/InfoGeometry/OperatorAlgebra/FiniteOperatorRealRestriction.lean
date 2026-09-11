import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability
import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelDerivative

/-!
# The real restriction of the finite complex operator algebra

The Duhamel parameter is real, whereas finite Hilbert-space operators are
complex-linear.  This owner records the canonical Mathlib carrier change
explicitly instead of installing an incoherent real scalar instance on the
complex operator type.
-/

namespace InfoGeometry.OperatorAlgebra

noncomputable section

open SouriauOnsagerBKM
open MeasureTheory
open scoped Interval

abbrev RealFiniteOperatorAlgebra (n : ℕ) :=
  RestrictScalars ℝ ℂ (FiniteOperatorAlgebra n)

abbrev RealFiniteOperator (n : ℕ) := RealFiniteOperatorAlgebra n

noncomputable instance realFiniteOperator_completeSpace (n : ℕ) :
    CompleteSpace (RealFiniteOperator n) := by
  let e : RealFiniteOperator n ≃ FiniteOperatorAlgebra n := Equiv.refl _
  apply (completeSpace_congr (e := e) (by
    exact Equiv.isUniformEmbedding e uniformContinuous_id uniformContinuous_id)).2
  infer_instance

def realFiniteOperatorTrace (n : ℕ) :
    RealFiniteOperator n →L[ℝ] ℂ :=
  (finiteOperatorTraceCLM n).restrictScalars ℝ

@[simp] theorem realFiniteOperatorTrace_apply
    {n : ℕ} (T : RealFiniteOperator n) :
    realFiniteOperatorTrace n T = finiteOperatorTrace T := rfl

theorem realFiniteOperatorTrace_mul_comm
    {n : ℕ} (A B : RealFiniteOperator n) :
    realFiniteOperatorTrace n (A * B) =
      realFiniteOperatorTrace n (B * A) := by
  exact finiteOperatorTrace_mul_comm A B

theorem realFiniteOperator_bkm_pairing_self_re_nonneg
    {n : ℕ} (D : FaithfulDensityOperator n)
    (A : RealFiniteOperator n) (h_rpow : Continuous D.rpow) :
    0 ≤ (D.kuboMoriPairing A A).re := by
  exact D.kuboMoriPairing_self_re_nonneg A h_rpow

theorem realFiniteOperator_bkm_pairing_self_re_pos
    {n : ℕ} (D : FaithfulDensityOperator n)
    (A : RealFiniteOperator n) (h_rpow : Continuous D.rpow)
    (hA : A ≠ 0) :
    0 < (D.kuboMoriPairing A A).re := by
  exact D.kuboMoriPairing_self_re_pos A h_rpow hA

theorem realFiniteOperator_integrand_intervalIntegrable
    {n : ℕ} (H T : RealFiniteOperator n) :
    IntervalIntegrable
      (fun t : ℝ =>
        NormedSpace.exp ((1 - t) • H) * T * NormedSpace.exp (t • H))
      volume 0 1 := by
  letI : NormedAlgebra ℚ (RealFiniteOperator n) :=
    NormedAlgebra.restrictScalars ℚ ℝ (RealFiniteOperator n)
  apply Continuous.intervalIntegrable
  fun_prop

theorem realFiniteOperatorTrace_duhamel
    {n : ℕ} (H T : RealFiniteOperator n) :
    realFiniteOperatorTrace n (duhamelDerivative H T) =
      ∫ t in (0 : ℝ)..1,
        realFiniteOperatorTrace n
          (NormedSpace.exp ((1 - t) • H) * T * NormedSpace.exp (t • H)) := by
  letI : NormedAlgebra ℚ (RealFiniteOperator n) :=
    NormedAlgebra.restrictScalars ℚ ℝ (RealFiniteOperator n)
  rw [duhamelDerivative_apply_integral]
  change realFiniteOperatorTrace n
      (∫ t in (0 : ℝ)..1,
        NormedSpace.exp ((1 - t) • H) * T * NormedSpace.exp (t • H)) = _
  exact (realFiniteOperatorTrace n).intervalIntegral_comp_comm
    (realFiniteOperator_integrand_intervalIntegrable H T) |>.symm

end

end InfoGeometry.OperatorAlgebra
