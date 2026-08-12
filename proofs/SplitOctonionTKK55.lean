import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import proofs.SO55NullSU5KleinSpectral

/-!
# Constrained split orthogonal carrier for the TKK(5,5) target

This module separates the genuine orthogonal carrier from the unconstrained
`1 ⊕ 8 ⊕ 1` matrix envelope.  The carrier is the real matrix condition
`Aᵀ η + η A = 0` for the diagonal form of signature `(5,5)`.
-/

noncomputable section
namespace SplitOctonionTKK55

abbrev M10 := Matrix (Fin 10) (Fin 10) ℝ

/-- Diagonal metric with five positive and five negative directions. -/
def eta55 : M10 :=
  fun i j => if i = j then if i.val < 5 then 1 else -1 else 0

@[simp] theorem eta55_apply_eq (i : Fin 10) :
    eta55 i i = if i.val < 5 then 1 else -1 := by
  simp [eta55]

@[simp] theorem eta55_apply_ne {i j : Fin 10} (h : i ≠ j) :
    eta55 i j = 0 := by
  simp [eta55, h]

/-- The defining linear condition for the real split orthogonal algebra. -/
def orthogonal55Condition (A : M10) : Prop :=
  A.transpose * eta55 + eta55 * A = 0

/-- The constrained carrier, unlike the previous unconstrained `gl₁₀` carrier. -/
def Orthogonal55 := {A : M10 // orthogonal55Condition A}

instance : Zero Orthogonal55 := ⟨⟨0, by simp [orthogonal55Condition]⟩⟩

instance : Add Orthogonal55 := ⟨fun A B =>
  ⟨A.1 + B.1, by
    simp only [orthogonal55Condition, Matrix.transpose_add, add_mul, mul_add]
    calc
      A.1.transpose * eta55 + B.1.transpose * eta55 +
          (eta55 * A.1 + eta55 * B.1) =
        (A.1.transpose * eta55 + eta55 * A.1) +
          (B.1.transpose * eta55 + eta55 * B.1) := by abel
      _ = 0 := by rw [A.2, B.2]; simp⟩⟩

instance : Neg Orthogonal55 := ⟨fun A =>
  ⟨-A.1, by
    simp only [orthogonal55Condition, Matrix.transpose_neg, neg_mul, mul_neg]
    rw [← neg_add, A.2]
    simp⟩⟩

/-- The orthogonal commutator. -/
def orthogonalBracket (A B : Orthogonal55) : Orthogonal55 :=
  ⟨A.1 * B.1 - B.1 * A.1, by
    unfold orthogonal55Condition
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
    have hA : A.1.transpose * eta55 = -(eta55 * A.1) :=
      eq_neg_of_add_eq_zero_left A.2
    have hB : B.1.transpose * eta55 = -(eta55 * B.1) :=
      eq_neg_of_add_eq_zero_left B.2
    simp only [mul_sub, sub_mul]
    rw [mul_assoc B.1.transpose A.1.transpose eta55,
      mul_assoc A.1.transpose B.1.transpose eta55,
      hA, hB]
    simp only [mul_neg]
    rw [← mul_assoc B.1.transpose eta55 A.1,
      ← mul_assoc A.1.transpose eta55 B.1,
      hB, hA]
    noncomm_ring⟩

/-- The bracket is antisymmetric. -/
theorem orthogonalBracket_skew (A B : Orthogonal55) :
    orthogonalBracket A B = -orthogonalBracket B A := by
  apply Subtype.ext
  change A.1 * B.1 - B.1 * A.1 = -(B.1 * A.1 - A.1 * B.1)
  noncomm_ring

theorem orthogonalBracket_jacobi (A B C : Orthogonal55) :
    orthogonalBracket A (orthogonalBracket B C) +
        orthogonalBracket B (orthogonalBracket C A) +
        orthogonalBracket C (orthogonalBracket A B) = 0 := by
  apply Subtype.ext
  change
    (A.1 * (B.1 * C.1 - C.1 * B.1) -
        (B.1 * C.1 - C.1 * B.1) * A.1) +
      (B.1 * (C.1 * A.1 - A.1 * C.1) -
        (C.1 * A.1 - A.1 * C.1) * B.1) +
      (C.1 * (A.1 * B.1 - B.1 * A.1) -
        (A.1 * B.1 - B.1 * A.1) * C.1) = 0
  noncomm_ring

/-- The constrained carrier is closed under the ordinary matrix commutator. -/
theorem orthogonalBracket_closed (A B : Orthogonal55) :
    orthogonal55Condition (orthogonalBracket A B).1 :=
  (orthogonalBracket A B).2

/-- Block count for the split orthogonal algebra: `25 + 10 + 10 = 45`. -/
def orthogonal55BlockDimension : ℕ := 5 * 5 + 5 * 4 / 2 + 5 * 4 / 2

theorem orthogonal55BlockDimension_eq_45 :
    orthogonal55BlockDimension = 45 := by
  norm_num [orthogonal55BlockDimension]

/-- The same count as the standard `so(5,5)` skew-pair count. -/
theorem orthogonal55BlockDimension_eq_so55 :
    orthogonal55BlockDimension =
      SO55NullSU5KleinSpectral.soDim SO55NullSU5KleinSpectral.nullVectorDim := by
  norm_num [orthogonal55BlockDimension,
    SO55NullSU5KleinSpectral.soDim,
    SO55NullSU5KleinSpectral.nullVectorDim,
    SO55NullSU5KleinSpectral.n5]

/-- The constrained carrier has the correct numerical target for the split TKK
algebra, while the algebraic equivalence remains an explicit next theorem. -/
theorem split_tkk55_dimension_target :
    orthogonal55BlockDimension = 45 ∧
      SO55NullSU5KleinSpectral.soDim SO55NullSU5KleinSpectral.nullVectorDim = 45 := by
  exact ⟨orthogonal55BlockDimension_eq_45,
    SO55NullSU5KleinSpectral.so55_dimension_45⟩

end SplitOctonionTKK55

end noncomputable section
