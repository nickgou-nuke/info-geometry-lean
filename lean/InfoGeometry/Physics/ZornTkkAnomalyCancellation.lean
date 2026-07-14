import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# InfoGeometry.Physics.ZornTkkAnomalyCancellation

Concrete owner-safe e⁺/e⁻ commutator readback on the split-octonion Zorn basis.

This file formalizes only the finite checked content already supported by the
concrete owner multiplication table:
- the commutator `[ePlus, eMinus]` is exactly zero;
- hence its off-diagonal slots vanish (pure-bosonic readback);
- its trace and determinant read back as zero.

No abstract 5-graded Lie closure, Jacobi theorem, or global TKK package is
asserted here.
-/

namespace ZornTkkAnomalyCancellation

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

/-- Concrete commutator on split-octonion Zorn cells. -/
def lieBracket (X Y : SplitOct) : SplitOct :=
  subZ (mulZ X Y) (mulZ Y X)

/-- The concrete `e⁺/e⁻` commutator cancels exactly. -/
@[simp] theorem lieBracket_ePlus_eMinus :
    lieBracket ePlus eMinus = zeroZ := by
  unfold lieBracket
  rw [ePlus_mul_eMinus, eMinus_mul_ePlus]
  rfl

/-- The cancelled `e⁺/e⁻` commutator is purely bosonic. -/
theorem tkk_e_plus_minus_anomaly_cancellation :
    IsPureBosonic (lieBracket ePlus eMinus) := by
  rw [lieBracket_ePlus_eMinus]
  unfold IsPureBosonic zeroZ
  simp

/-- The concrete `e⁺/e⁻` commutator has zero trace. -/
theorem tkk_commutator_trace_evaluation :
    trZ (lieBracket ePlus eMinus) = 0 := by
  rw [lieBracket_ePlus_eMinus]
  rfl

/-- The concrete `e⁺/e⁻` commutator has zero determinant. -/
theorem tkk_commutator_det_evaluation :
    detZ (lieBracket ePlus eMinus) = 0 := by
  rw [lieBracket_ePlus_eMinus]
  rfl

/-- Base readback of the cancelled `e⁺/e⁻` commutator. -/
theorem tkk_commutator_base_readout :
    (projectToBase (lieBracket ePlus eMinus)).trace = 0 ∧
      (projectToBase (lieBracket ePlus eMinus)).det = 0 := by
  constructor
  · exact tkk_commutator_trace_evaluation
  · exact tkk_commutator_det_evaluation

end ZornTkkAnomalyCancellation
