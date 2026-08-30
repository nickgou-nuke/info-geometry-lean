import Mathlib.Analysis.Matrix.Order
import InfoGeometry.Canonical.SouriauOnsagerBKMIntegrability

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

This is the algebraic positivity statement needed before integrating over the
modular parameter and deriving the BKM Cauchy--Schwarz/Cramér--Rao lane.
-/
theorem FaithfulDensityOperator.kuboMoriIntegrand_self_re_nonneg
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n)
    (s : ℝ) :
    0 ≤ (D.kuboMoriIntegrand A A s).re := by
  rw [D.kuboMoriIntegrand_self_eq_trace_star_mul_self A s]
  exact finiteOperatorTrace_star_mul_self_re_nonneg _

end SouriauOnsagerBKM
