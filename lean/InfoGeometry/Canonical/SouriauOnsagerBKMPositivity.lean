import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.BilinearForm.Properties
import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm

noncomputable section

namespace SouriauOnsagerBKM

open Matrix
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

/-- The finite operator trace is nonnegative on a canonical square `X†X`.

This is the basis-independent operator statement proved through the existing
matrix/operator equivalence and Mathlib's positive-semidefinite trace theorem.
-/
theorem finiteOperatorTrace_star_mul_self_re_nonneg
    (X : FiniteOperatorAlgebra n) :
    0 ≤ (finiteOperatorTrace (star X * X)).re := by
  unfold finiteOperatorTrace
  change
    0 ≤
      (Matrix.trace
        (matrixOfOp ((ContinuousLinearMap.adjoint X).comp X))).re
  rw [matrixOfOp_comp, matrixOfOp_adjoint]
  have hpsd :
      ((matrixOfOp X)ᴴ * matrixOfOp X).PosSemidef :=
    posSemidef_conjTranspose_mul_self (matrixOfOp X)
  exact (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1

/-- The self Kubo--Mori integrand is the trace of an explicit operator square.

For
`X_s = ρ^((1-s)/2) A ρ^(s/2)`, cyclicity of the finite trace gives

`Tr(ρ^s A† ρ^(1-s) A) = Tr(X_s† X_s)`.

No simultaneous diagonalization or commutativity of `A` with `ρ` is used.
-/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_eq_trace_star_mul_self
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (s : ℝ) :
    D.kuboMoriIntegrand A A s =
      finiteOperatorTrace
        (star
            (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2)) *
          (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
  have hleft :
      D.rpow ((1 - s) / 2) * D.rpow ((1 - s) / 2) =
        D.rpow (1 - s) := by
    rw [← D.rpow_add]
    congr 1
    ring
  have hright :
      D.rpow (s / 2) * D.rpow (s / 2) = D.rpow s := by
    rw [← D.rpow_add]
    congr 1
    ring
  calc
    D.kuboMoriIntegrand A A s =
        finiteOperatorTrace
          (D.rpow s * star A * D.rpow (1 - s) * A) := by
            rfl
    _ = finiteOperatorTrace
          ((D.rpow (s / 2) * D.rpow (s / 2)) *
            star A * D.rpow (1 - s) * A) := by
          rw [hright]
    _ = finiteOperatorTrace
          (D.rpow (s / 2) *
            (D.rpow (s / 2) * star A * D.rpow (1 - s) * A)) := by
          congr 1
          noncomm_ring
    _ = finiteOperatorTrace
          ((D.rpow (s / 2) * star A * D.rpow (1 - s) * A) *
            D.rpow (s / 2)) :=
          finiteOperatorTrace_mul_comm _ _
    _ = finiteOperatorTrace
          ((D.rpow (s / 2) * star A *
              (D.rpow ((1 - s) / 2) * D.rpow ((1 - s) / 2)) * A) *
            D.rpow (s / 2)) := by
          rw [hleft]
    _ = finiteOperatorTrace
          ((D.rpow (s / 2) * star A * D.rpow ((1 - s) / 2)) *
            (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
          congr 1
          noncomm_ring
    _ = finiteOperatorTrace
          (star
              (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2)) *
            (D.rpow ((1 - s) / 2) * A * D.rpow (s / 2))) := by
          congr 1
          simp [mul_assoc]

/-- Pointwise positivity of the full noncommutative Kubo--Mori self-integrand.
-/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_re_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (s : ℝ) :
    0 ≤ (D.kuboMoriIntegrand A A s).re := by
  rw [D.kuboMoriIntegrand_self_eq_trace_star_mul_self A s]
  exact finiteOperatorTrace_star_mul_self_re_nonneg _

/-- The real part of the integrated full noncommutative Kubo--Mori self-pairing
is nonnegative.

The only analytic input is the continuity hypothesis on the existing CFC
real-power path, already used by the BKM integrability owner.
-/
theorem FaithfulDensityOperator.kuboMoriPairing_self_re_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (h_rpow : Continuous D.rpow) :
    0 ≤ (D.kuboMoriPairing A A).re := by
  have h_integrable :
      IntervalIntegrable
        (D.kuboMoriIntegrand A A) MeasureTheory.volume 0 1 :=
    (D.continuous_kuboMoriIntegrand_of_continuous_rpow A A h_rpow).intervalIntegrable 0 1
  have hre :
      (D.kuboMoriPairing A A).re =
        ∫ s in (0 : ℝ)..1, (D.kuboMoriIntegrand A A s).re := by
    unfold FaithfulDensityOperator.kuboMoriPairing
    symm
    exact
      ContinuousLinearMap.intervalIntegral_comp_comm
        (RCLike.reCLM : ℂ →L[ℝ] ℝ) h_integrable
  rw [hre]
  exact intervalIntegral.integral_nonneg_of_forall (by norm_num) fun s =>
    D.kuboMoriIntegrand_self_re_nonneg A s

/-- The existing real BKM response form is a genuine positive-semidefinite
symmetric bilinear form on the full finite noncommutative operator algebra.
-/
theorem FaithfulDensityOperator.bkmRealBilinForm_isPosSemidef
    (D : FaithfulDensityOperator n)
    (h_rpow : Continuous D.rpow) :
    (D.bkmRealBilinForm h_rpow).IsPosSemidef where
  isSymm := D.bkmRealBilinForm_symm h_rpow
  isNonneg := ⟨fun A => by
    simpa only [D.bkmRealBilinForm_apply h_rpow A A] using
      D.kuboMoriPairing_self_re_nonneg A h_rpow⟩

end SouriauOnsagerBKM
