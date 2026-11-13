/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces

/-!
# Odd anticommutators and products through the zero corner

For either odd grade of a tripotent adjoint, the span of anticommutators is
exactly the span of the products that pass through the zero Peirce corner.
The inclusion in the extreme grade is unconditional. Equality with the full
extreme grade is equivalent to that corner-spanning condition; no fullness or
categorical Morita equivalence is assumed or inferred.
-/

noncomputable section

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The real span of the unnormalized anticommutators of elements of `U`. -/
def anticommutatorSpan (U : Submodule ℝ A) : Submodule ℝ A :=
  Submodule.span ℝ {Z : A | ∃ X ∈ U, ∃ Y ∈ U, Z = X * Y + Y * X}

/-- The real span of all products passing through the specified middle corner. -/
def middleCornerSpan (p q r : A) : Submodule ℝ A :=
  Submodule.span ℝ {Z : A | ∃ X Y : A, Z = p * X * q * Y * r}

private theorem mul_eq_middle_of_two_corner
    {p q r X Y : A} (hqq : q * q = q) (hqp : q * p = 0)
    (hrp : r * p = 0) (hrq : r * q = 0)
    (hX : X = p * X * q + q * X * r)
    (hY : Y = p * Y * q + q * Y * r) :
    X * Y = p * X * q * Y * r := by
  calc
    X * Y = (p * X * q + q * X * r) * (p * Y * q + q * Y * r) :=
      congrArg₂ (fun a b : A => a * b) hX hY
    _ = p * X * (q * p) * Y * q + p * X * (q * q) * Y * r +
        q * X * (r * p) * Y * q + q * X * (r * q) * Y * r := by
      noncomm_ring
    _ = p * X * q * Y * r := by simp only [hqq, hqp, hrp, hrq,
      mul_zero, zero_mul, add_zero, zero_add]

private theorem adjacent_corner_anticommutator
    {p q r : A} (hqq : q * q = q) (hrp : r * p = 0) (X Y : A) :
    (p * X * q) * (q * Y * r) + (q * Y * r) * (p * X * q) =
      p * X * q * Y * r := by
  calc
    (p * X * q) * (q * Y * r) + (q * Y * r) * (p * X * q) =
        p * X * (q * q) * Y * r + q * Y * (r * p) * X * q := by
      noncomm_ring
    _ = p * X * q * Y * r := by
      simp only [hqq, hrp, mul_zero, zero_mul, add_zero]

private theorem anticommutatorSpan_eq_middleCornerSpan_of_two_corner
    (U : Submodule ℝ A) {p q r : A}
    (hqq : q * q = q) (hqp : q * p = 0)
    (hrp : r * p = 0) (hrq : r * q = 0)
    (hdecomp : ∀ X ∈ U, X = p * X * q + q * X * r)
    (hleft : ∀ X : A, p * X * q ∈ U)
    (hright : ∀ Y : A, q * Y * r ∈ U) :
    anticommutatorSpan U = middleCornerSpan p q r := by
  unfold anticommutatorSpan middleCornerSpan
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro Z ⟨X, hX, Y, hY, rfl⟩
    rw [mul_eq_middle_of_two_corner hqq hqp hrp hrq (hdecomp X hX) (hdecomp Y hY),
      mul_eq_middle_of_two_corner hqq hqp hrp hrq (hdecomp Y hY) (hdecomp X hX)]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨X, Y, rfl⟩)
      (Submodule.subset_span ⟨Y, X, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro Z ⟨X, Y, rfl⟩
    apply Submodule.subset_span
    exact ⟨p * X * q, hleft X, q * Y * r, hright Y,
      (adjacent_corner_anticommutator hqq hrp X Y).symm⟩

/-- An element of grade `+1` is the sum of its two adjacent Peirce corners. -/
theorem adGrade_posOne_decompose {S X : A} (hS : S * S * S = S)
    (hX : X ∈ adGrade S 1) :
    X = projPos S * X * projZero S + projZero S * X * projNeg S := by
  have hX' : X ∈ fiveGradeRange S .posOne := by
    rw [fiveGradeRange_eq_eigenspace hS, ← adGrade_eq_eigenspace]
    exact hX
  have hfixed := (mem_fiveGradeRange_iff_projector_fixed hS .posOne).mp hX'
  simpa only [fiveGradeProjector_posOne, gradePosOneProjector,
    LinearMap.add_apply, jointPeirceProjector_apply, peirceProjector_pos,
    peirceProjector_zero, peirceProjector_neg, mul_assoc] using hfixed.symm

/-- An element of grade `-1` is the sum of its two adjacent Peirce corners. -/
theorem adGrade_negOne_decompose {S X : A} (hS : S * S * S = S)
    (hX : X ∈ adGrade S (-1)) :
    X = projNeg S * X * projZero S + projZero S * X * projPos S := by
  have hX' : X ∈ fiveGradeRange S .negOne := by
    rw [fiveGradeRange_eq_eigenspace hS, ← adGrade_eq_eigenspace]
    exact hX
  have hfixed := (mem_fiveGradeRange_iff_projector_fixed hS .negOne).mp hX'
  simpa only [fiveGradeProjector_negOne, gradeNegOneProjector,
    LinearMap.add_apply, jointPeirceProjector_apply, peirceProjector_pos,
    peirceProjector_zero, peirceProjector_neg, mul_assoc, add_comm] using hfixed.symm

theorem pos_zero_corner_mem_adGrade_one {S : A} (hS : S * S * S = S) (X : A) :
    projPos S * X * projZero S ∈ adGrade S 1 := by
  apply mem_adGrade_iff.mpr
  simpa [adOp, peirceScalar, mul_assoc] using
    jointPeirceProjector_adjoint_weight hS .pos .zero X

theorem zero_neg_corner_mem_adGrade_one {S : A} (hS : S * S * S = S) (X : A) :
    projZero S * X * projNeg S ∈ adGrade S 1 := by
  apply mem_adGrade_iff.mpr
  simpa [adOp, peirceScalar, mul_assoc] using
    jointPeirceProjector_adjoint_weight hS .zero .neg X

theorem neg_zero_corner_mem_adGrade_neg_one {S : A} (hS : S * S * S = S)
    (X : A) : projNeg S * X * projZero S ∈ adGrade S (-1) := by
  apply mem_adGrade_iff.mpr
  simpa [adOp, peirceScalar, mul_assoc] using
    jointPeirceProjector_adjoint_weight hS .neg .zero X

theorem zero_pos_corner_mem_adGrade_neg_one {S : A} (hS : S * S * S = S)
    (X : A) : projZero S * X * projPos S ∈ adGrade S (-1) := by
  apply mem_adGrade_iff.mpr
  simpa [adOp, peirceScalar, mul_assoc] using
    jointPeirceProjector_adjoint_weight hS .zero .pos X

/-- The two orders of multiplication in grade `+1` factor through `P₀`. -/
theorem anticommutator_posOne_factorization {S X Y : A}
    (hS : S * S * S = S) (hX : X ∈ adGrade S 1) (hY : Y ∈ adGrade S 1) :
    X * Y + Y * X =
      projPos S * X * projZero S * Y * projNeg S +
        projPos S * Y * projZero S * X * projNeg S := by
  rw [mul_eq_middle_of_two_corner (projZero_idempotent hS)
    (projZero_mul_projPos_eq_zero hS) (projNeg_mul_projPos_eq_zero hS)
    (projNeg_mul_projZero_eq_zero hS) (adGrade_posOne_decompose hS hX)
    (adGrade_posOne_decompose hS hY),
    mul_eq_middle_of_two_corner (projZero_idempotent hS)
    (projZero_mul_projPos_eq_zero hS) (projNeg_mul_projPos_eq_zero hS)
    (projNeg_mul_projZero_eq_zero hS) (adGrade_posOne_decompose hS hY)
    (adGrade_posOne_decompose hS hX)]

/-- The two orders of multiplication in grade `-1` factor through `P₀`. -/
theorem anticommutator_negOne_factorization {S X Y : A}
    (hS : S * S * S = S) (hX : X ∈ adGrade S (-1)) (hY : Y ∈ adGrade S (-1)) :
    X * Y + Y * X =
      projNeg S * X * projZero S * Y * projPos S +
        projNeg S * Y * projZero S * X * projPos S := by
  rw [mul_eq_middle_of_two_corner (projZero_idempotent hS)
    (projZero_mul_projNeg_eq_zero hS) (projPos_mul_projNeg_eq_zero hS)
    (projPos_mul_projZero_eq_zero hS) (adGrade_negOne_decompose hS hX)
    (adGrade_negOne_decompose hS hY),
    mul_eq_middle_of_two_corner (projZero_idempotent hS)
    (projZero_mul_projNeg_eq_zero hS) (projPos_mul_projNeg_eq_zero hS)
    (projPos_mul_projZero_eq_zero hS) (adGrade_negOne_decompose hS hY)
    (adGrade_negOne_decompose hS hX)]

/-- Every product through the zero corner is generated by positive odd
anticommutators, and every such anticommutator is a sum of two such products. -/
theorem anticommutatorSpan_posOne_eq_middleCornerSpan {S : A}
    (hS : S * S * S = S) :
    anticommutatorSpan (adGrade S 1) =
      middleCornerSpan (projPos S) (projZero S) (projNeg S) :=
  anticommutatorSpan_eq_middleCornerSpan_of_two_corner (adGrade S 1)
    (projZero_idempotent hS) (projZero_mul_projPos_eq_zero hS)
    (projNeg_mul_projPos_eq_zero hS) (projNeg_mul_projZero_eq_zero hS)
    (fun _ hX => adGrade_posOne_decompose hS hX)
    (pos_zero_corner_mem_adGrade_one hS) (zero_neg_corner_mem_adGrade_one hS)

/-- The same exact spanning identity holds for the negative odd grade. -/
theorem anticommutatorSpan_negOne_eq_middleCornerSpan {S : A}
    (hS : S * S * S = S) :
    anticommutatorSpan (adGrade S (-1)) =
      middleCornerSpan (projNeg S) (projZero S) (projPos S) :=
  anticommutatorSpan_eq_middleCornerSpan_of_two_corner (adGrade S (-1))
    (projZero_idempotent hS) (projZero_mul_projNeg_eq_zero hS)
    (projPos_mul_projNeg_eq_zero hS) (projPos_mul_projZero_eq_zero hS)
    (fun _ hX => adGrade_negOne_decompose hS hX)
    (neg_zero_corner_mem_adGrade_neg_one hS) (zero_pos_corner_mem_adGrade_neg_one hS)

/-- Grade addition bounds the anticommutator span, without a tripotency hypothesis. -/
theorem anticommutatorSpan_adGrade_le (S : A) (k : ℤ) :
    anticommutatorSpan (adGrade S k) ≤ adGrade S (k + k) := by
  apply Submodule.span_le.mpr
  rintro Z ⟨X, hX, Y, hY, rfl⟩
  exact (adGrade S (k + k)).add_mem (mul_mem_adGrade_add hX hY)
    (mul_mem_adGrade_add hY hX)

/-- Positive odd anticommutators span the whole extreme grade exactly when
every extreme element is in the span of products through the zero corner. -/
theorem anticommutatorSpan_posOne_eq_posTwo_iff {S : A}
    (hS : S * S * S = S) :
    anticommutatorSpan (adGrade S 1) = adGrade S 2 ↔
      ∀ Z ∈ adGrade S 2, Z ∈ middleCornerSpan (projPos S) (projZero S) (projNeg S) := by
  rw [anticommutatorSpan_posOne_eq_middleCornerSpan hS]
  constructor
  · intro h Z hZ
    exact h.symm ▸ hZ
  · intro h
    apply le_antisymm _ h
    rw [← anticommutatorSpan_posOne_eq_middleCornerSpan hS]
    simpa using anticommutatorSpan_adGrade_le S 1

/-- Negative odd anticommutators span the whole opposite extreme grade exactly
under the corresponding zero-corner spanning condition. -/
theorem anticommutatorSpan_negOne_eq_negTwo_iff {S : A}
    (hS : S * S * S = S) :
    anticommutatorSpan (adGrade S (-1)) = adGrade S (-2) ↔
      ∀ Z ∈ adGrade S (-2), Z ∈ middleCornerSpan (projNeg S) (projZero S) (projPos S) := by
  rw [anticommutatorSpan_negOne_eq_middleCornerSpan hS]
  constructor
  · intro h Z hZ
    exact h.symm ▸ hZ
  · intro h
    apply le_antisymm _ h
    rw [← anticommutatorSpan_negOne_eq_middleCornerSpan hS]
    simpa using anticommutatorSpan_adGrade_le S (-1)

end InfoGeometry.Core.TripotentAdjoint
