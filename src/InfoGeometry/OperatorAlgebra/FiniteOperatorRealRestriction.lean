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

set_option synthInstance.maxHeartbeats 200000

def RealFiniteOperatorAlgebra (n : ℕ) :=
  FiniteOperatorAlgebra n

abbrev RealFiniteOperator (n : ℕ) := RealFiniteOperatorAlgebra n

namespace RealFiniteOperator

instance (n : ℕ) : NormedRing (RealFiniteOperator n) :=
  inferInstanceAs (NormedRing (FiniteOperatorAlgebra n))

instance (n : ℕ) : CompleteSpace (RealFiniteOperator n) :=
  inferInstanceAs (CompleteSpace (FiniteOperatorAlgebra n))

instance (n : ℕ) : NormedSpace ℝ (RealFiniteOperator n) :=
  NormedSpace.restrictScalars ℝ ℂ (FiniteOperatorAlgebra n)

instance (n : ℕ) : NormedAlgebra ℝ (RealFiniteOperator n) :=
  NormedAlgebra.restrictScalars ℝ ℂ (FiniteOperatorAlgebra n)

end RealFiniteOperator

def realFiniteOperatorTrace (n : ℕ) :
    RealFiniteOperator n →L[ℝ] ℂ :=
  (finiteOperatorTraceCLM n).restrictScalars ℝ

@[simp] theorem realFiniteOperatorTrace_apply
    {n : ℕ} (T : RealFiniteOperator n) :
    realFiniteOperatorTrace n T = finiteOperatorTrace (T : FiniteOperatorAlgebra n) := rfl

theorem realFiniteOperatorTrace_mul_comm
    {n : ℕ} (A B : RealFiniteOperator n) :
    realFiniteOperatorTrace n (A * B) =
      realFiniteOperatorTrace n (B * A) := by
  exact finiteOperatorTrace_mul_comm (A : FiniteOperatorAlgebra n) (B : FiniteOperatorAlgebra n)

theorem realFiniteOperator_bkm_pairing_self_re_nonneg
    {n : ℕ} (D : FaithfulDensityOperator n)
    (A : RealFiniteOperator n) (h_rpow : Continuous D.rpow) :
    0 ≤ (D.kuboMoriPairing (A : FiniteOperatorAlgebra n) (A : FiniteOperatorAlgebra n)).re := by
  exact D.kuboMoriPairing_self_re_nonneg (A : FiniteOperatorAlgebra n) h_rpow

theorem realFiniteOperator_bkm_pairing_self_re_pos
    {n : ℕ} (D : FaithfulDensityOperator n)
    (A : RealFiniteOperator n) (h_rpow : Continuous D.rpow)
    (hA : A ≠ 0) :
    0 < (D.kuboMoriPairing (A : FiniteOperatorAlgebra n) (A : FiniteOperatorAlgebra n)).re := by
  exact D.kuboMoriPairing_self_re_pos (A : FiniteOperatorAlgebra n) h_rpow hA

theorem realFiniteOperator_integrand_intervalIntegrable
    {n : ℕ} (H T : RealFiniteOperator n) :
    IntervalIntegrable
      (fun t : ℝ =>
        NormedSpace.exp ((1 - t) • H) * T * NormedSpace.exp (t • H))
      volume 0 1 := by
  have hc : Continuous (fun t : ℝ => (duhamelIntegrand H t) T) :=
    (ContinuousLinearMap.apply ℝ (RealFiniteOperator n) T).continuous.comp
      (continuous_duhamelIntegrand H)
  exact hc.intervalIntegrable 0 1

theorem realFiniteOperatorTrace_duhamel
    {n : ℕ} (H T : RealFiniteOperator n) :
    realFiniteOperatorTrace n (duhamelDerivative H T) =
      ∫ t in (0 : ℝ)..1,
        realFiniteOperatorTrace n
          (NormedSpace.exp ((1 - t) • H) * T * NormedSpace.exp (t • H)) := by
  rw [duhamelDerivative_apply_integral H T]
  exact (realFiniteOperatorTrace n).intervalIntegral_comp_comm
    (realFiniteOperator_integrand_intervalIntegrable H T) |>.symm

end

end InfoGeometry.OperatorAlgebra
