import Mathlib
import InfoGeometry.Analysis.RankOneTrace

/-!
# Phase 2: Hilbert-Schmidt fragments and rank-one trace

This duplicate file now keeps only the finite-dimensional facts that are
actually proved from mathlib and the repository's rank-one trace lemma.
The unfinished Hilbert-Schmidt isometry and partial-trace constructions are
owned elsewhere.
-/

noncomputable section

open FiniteDimensional
open TensorProduct

namespace HilbertTensorProduct
namespace Phase2

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

section HS2Ell2

variable [FiniteDimensional ℝ H₁] [FiniteDimensional ℝ H₂]

/-- Hilbert-Schmidt inner product on bounded operators. -/
noncomputable def hsInner (A B : H₁ →L[ℝ] H₂) : ℝ :=
  let e := stdOrthonormalBasis ℝ H₁
  ∑ i, inner (𝕜 := ℝ) (A (e i)) (B (e i))

lemma hsInner_nonneg (A : H₁ →L[ℝ] H₂) : 0 ≤ hsInner A A := by
  dsimp [hsInner]
  exact Finset.sum_nonneg fun i _ =>
    by simpa using (inner_self_nonneg : 0 ≤ inner (𝕜 := ℝ) (A (stdOrthonormalBasis ℝ H₁ i)) (A (stdOrthonormalBasis ℝ H₁ i)))

/-- Hilbert-Schmidt norm. -/
noncomputable def hsNorm (A : H₁ →L[ℝ] H₂) : ℝ := Real.sqrt (hsInner A A)

lemma hsNorm_sq (A : H₁ →L[ℝ] H₂) : (hsNorm A)^2 = hsInner A A := by
  dsimp [hsNorm]
  simpa using (Real.sq_sqrt (hsInner_nonneg A))

lemma hsNorm_nonneg (A : H₁ →L[ℝ] H₂) : 0 ≤ hsNorm A := by
  dsimp [hsNorm]
  exact Real.sqrt_nonneg _

end HS2Ell2

section OperatorTrace

variable [FiniteDimensional ℝ H₁]

/-- Trace of a linear operator via a standard orthonormal basis. -/
noncomputable def operatorTrace (A : H₁ →L[ℝ] H₁) : ℝ :=
  let e := stdOrthonormalBasis ℝ H₁
  ∑ i, inner (𝕜 := ℝ) (e i) (A (e i))

/-- The trace of a rank-one operator is the corresponding inner product. -/
lemma operatorTrace_rankOne (x y : H₁) :
    operatorTrace (InnerProductSpace.rankOne ℝ x y) = inner (𝕜 := ℝ) y x := by
  calc
    operatorTrace (InnerProductSpace.rankOne ℝ x y)
        = (LinearMap.trace ℝ H₁) (InnerProductSpace.rankOne ℝ x y) := by
            simpa [operatorTrace] using
              (LinearMap.trace_eq_sum_inner (T := (InnerProductSpace.rankOne ℝ x y).toLinearMap)
                (b := stdOrthonormalBasis ℝ H₁)).symm
    _ = inner (𝕜 := ℝ) y x := by
          simpa using (InfoGeometry.Analysis.trace_rankOne_eq_inner (H := H₁) x y)

end OperatorTrace

/-- The norm of a rank-one operator is the product of the norms. -/
theorem norm_rankOne_eq
    (x : H₁) (y : H₂) :
    ‖InnerProductSpace.rankOne ℝ x y‖ = ‖x‖ * ‖y‖ := by
  simpa using
    (InfoGeometry.Analysis.norm_rankOne_eq (H := H₁) (H₂ := H₂) x y)

end Phase2
end HilbertTensorProduct
