import Mathlib.Analysis.Matrix.Order
import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability

noncomputable section

namespace SouriauOnsagerBKM

open Matrix
open scoped MatrixOrder
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

/-- Splitting a real CFC power into two equal powers. -/
theorem FaithfulDensityOperator.rpow_half_mul_self
    (D : FaithfulDensityOperator n) (s : ℝ) :
    D.rpow (s / 2) * D.rpow (s / 2) = D.rpow s := by
  rw [← D.rpow_add]
  congr 1
  ring

/-- Splitting the complementary real CFC power into two equal powers. -/
theorem FaithfulDensityOperator.rpow_one_sub_half_mul_self
    (D : FaithfulDensityOperator n) (s : ℝ) :
    D.rpow ((1 - s) / 2) * D.rpow ((1 - s) / 2) = D.rpow (1 - s) := by
  rw [← D.rpow_add]
  congr 1
  ring

/-- The finite trace of `X†X` has nonnegative real part.  The proof is native:
transport to the canonical matrix representation, use positivity of
`Mᴴ M`, and then positivity of the matrix trace. -/
theorem finiteOperatorTrace_star_mul_self_re_nonneg
    (X : FiniteOperatorAlgebra n) :
    0 ≤ (finiteOperatorTrace (star X * X)).re := by
  unfold finiteOperatorTrace
  rw [matrixOfOp_comp, matrixOfOp_adjoint]
  have hpos : ((matrixOfOp X)ᴴ * matrixOfOp X).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self (matrixOfOp X)
  exact (RCLike.nonneg_iff.mp hpos.trace_nonneg).1

/-- Pointwise Hilbert--Schmidt factorization of the diagonal BKM integrand.

This is deliberately a trace-level identity, not an operator identity.  The
cyclicity of the finite trace moves the final `ρ^(s/2)` to the front, where the
two half-powers combine to `ρ^s`. -/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_eq_trace_star_mul_self
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ) :
    D.kuboMoriIntegrand A A s =
      finiteOperatorTrace
        (star
            (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2)) *
          (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
  unfold FaithfulDensityOperator.kuboMoriIntegrand
  rw [← D.rpow_half_mul_self s,
    ← D.rpow_one_sub_half_mul_self s]
  simp only [StarMul.star_mul, D.star_rpow, star_star]
  calc
    finiteOperatorTrace
        ((D.rpow (s / 2) * D.rpow (s / 2)) * star A *
          (D.rpow ((1 - s) / 2) * D.rpow ((1 - s) / 2)) * A) =
      finiteOperatorTrace
        ((D.rpow (s / 2) * star A * D.rpow ((1 - s) / 2) *
            D.rpow ((1 - s) / 2) * A) * D.rpow (s / 2)) := by
          simp only [mul_assoc]
          rw [finiteOperatorTrace_mul_comm]
    _ =
      finiteOperatorTrace
        ((D.rpow (s / 2) * (star A * D.rpow ((1 - s) / 2))) *
          (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
          congr 1
          simp only [mul_assoc]

/-- The diagonal BKM integrand is pointwise nonnegative in real part. -/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_re_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ) :
    0 ≤ (D.kuboMoriIntegrand A A s).re := by
  rw [D.kuboMoriIntegrand_self_eq_trace_star_mul_self A s]
  exact finiteOperatorTrace_star_mul_self_re_nonneg _

/-- The genuine finite-dimensional noncommutative BKM pairing has
nonnegative diagonal. -/
theorem FaithfulDensityOperator.kuboMoriPairing_self_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h : Continuous D.rpow) :
    0 ≤ (D.kuboMoriPairing A A).re := by
  have hIntegrable :
      IntervalIntegrable (D.kuboMoriIntegrand A A)
        MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h).intervalIntegrable 0 1
  have hre :
      (D.kuboMoriPairing A A).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A A s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    simpa using
      (ContinuousLinearMap.intervalIntegral_comp_comm
        (RCLike.reCLM : ℂ →L[ℝ] ℝ) hIntegrable)
  rw [hre]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num) fun s =>
    D.kuboMoriIntegrand_self_re_nonneg A s

end SouriauOnsagerBKM
