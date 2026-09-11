import InfoGeometry.KK.KasparovCycle
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# InfoGeometry.KK.CompactOperatorBridge

Concrete compact-operator lemmas for the bounded Kasparov layer.
-/

namespace InfoGeometry.KK

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma isCompactEnd_zero :
    IsCompactEnd H (0 : EndH H) := by
  simpa [IsCompactEnd] using (isCompactOperator_zero : IsCompactOperator (0 : H → H))

lemma isCompactEnd_add {A B : EndH H}
    (hA : IsCompactEnd H A) (hB : IsCompactEnd H B) :
    IsCompactEnd H (A + B) := by
  simpa [IsCompactEnd] using (IsCompactOperator.add hA hB)

lemma isCompactEnd_smul (r : ℝ) {A : EndH H}
    (hA : IsCompactEnd H A) :
    IsCompactEnd H (r • A) := by
  simpa [IsCompactEnd] using (IsCompactOperator.smul hA r)

/--
On finite-dimensional real Hilbert carriers, every bounded endomorphism is compact.
-/
lemma isCompactEnd_of_finiteDimensional
    [CompleteSpace H] [FiniteDimensional ℝ H]
    (A : EndH H) :
    IsCompactEnd H A := by
  change IsCompactOperator (A : H →ₗ[ℝ] H)
  refine (isCompactOperator_iff_image_closedBall_subset_compact
      (f := (A : H →ₗ[ℝ] H)) (hr := zero_lt_one)).2 ?_
  refine ⟨Metric.closedBall (0 : H) ‖A‖, isCompact_closedBall _ _, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hx' : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hAx : ‖A x‖ ≤ ‖A‖ := by
    calc
      ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left hx' (norm_nonneg _)
      _ = ‖A‖ := by ring
  simpa using hAx

end InfoGeometry.KK
