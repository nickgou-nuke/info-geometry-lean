import InfoGeometry.Algebra.ZornLeftMultiplicationDefect
import InfoGeometry.OperatorAlgebra.OperatorDefectCompletion

/-!
# Native Zorn defects belong to the generated operator Lie algebra

This adapter uses the repository's actual real Zorn carrier and its proved
commutator-defect identity. It does not assert that an arbitrary noncommutative-
coefficient Zorn product is alternative.

Status: complete proof-script draft, not locally elaborated in this environment.
-/

set_option autoImplicit false

namespace InfoGeometry.Algebra.ZornLeftCAR

open ZornPinorReconstruction
open InfoGeometry.OperatorAlgebra.DefectCompletion

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

/-- Recover the associator operator from native left actions and their bracket. -/
theorem multiplicationDefect_eq_half_commutator_correction (X Y : Z) :
    multiplicationDefect X Y =
      (1 / 2 : ℝ) •
        (leftMultiplication (ZornVectorMatrix.commutator X Y) -
          ⁅leftMultiplication X, leftMultiplication Y⁆) := by
  have h := leftMultiplication_commutator_defect X Y
  rw [two_nsmul] at h
  have hsum :
      multiplicationDefect X Y + multiplicationDefect X Y =
        leftMultiplication (ZornVectorMatrix.commutator X Y) -
          ⁅leftMultiplication X, leftMultiplication Y⁆ := by
    rw [LieRing.of_associative_ring_bracket, h]
    abel
  calc
    multiplicationDefect X Y =
        (1 / 2 : ℝ) • ((2 : ℝ) • multiplicationDefect X Y) := by
      norm_num [smul_smul]
    _ = (1 / 2 : ℝ) •
        (multiplicationDefect X Y + multiplicationDefect X Y) := by
      rw [two_smul]
    _ = _ := by rw [hsum]

/-- Every operator Lie subalgebra containing all left actions contains their
associator defects. No defect is postulated as an independent generator. -/
theorem multiplicationDefect_mem_of_left_actions
    (K : LieSubalgebra ℝ (Module.End ℝ Z))
    (hL : ∀ W : Z, leftMultiplication W ∈ K) (X Y : Z) :
    multiplicationDefect X Y ∈ K := by
  rw [multiplicationDefect_eq_half_commutator_correction]
  exact K.smul_mem (1 / 2 : ℝ)
    (K.sub_mem (hL (ZornVectorMatrix.commutator X Y))
      (K.lie_mem (hL X) (hL Y)))

/-- In particular, the native Lie closure of the left actions contains the
operator-valued associator. -/
theorem multiplicationDefect_mem_native_lieSpan (X Y : Z) :
    multiplicationDefect X Y ∈
      LieSubalgebra.lieSpan ℝ (Module.End ℝ Z)
        (Set.range leftMultiplication) := by
  apply multiplicationDefect_mem_of_left_actions
  intro W
  exact LieSubalgebra.subset_lieSpan ⟨W, rfl⟩

/-- Every associator defect annihilates the native unit. -/
@[simp] theorem multiplicationDefect_one (X Y : Z) :
    multiplicationDefect X Y ZornVectorMatrix.one = 0 := by
  change ZornVectorMatrix.mul (ZornVectorMatrix.mul X Y) ZornVectorMatrix.one -
      ZornVectorMatrix.mul X (ZornVectorMatrix.mul Y ZornVectorMatrix.one) = 0
  rw [ZornVectorMatrix.mul_one, ZornVectorMatrix.mul_one, sub_self]

/-- A nonzero associator operator is not itself a left multiplication.
Its action on the unit is the separating observable. -/
theorem nonzero_multiplicationDefect_not_mem_left_range
    (X Y : Z) (hD : multiplicationDefect X Y ≠ 0) :
    multiplicationDefect X Y ∉ LinearMap.range leftMultiplication := by
  rintro ⟨W, hW⟩
  have he := LinearMap.congr_fun hW ZornVectorMatrix.one
  have hW0 : W = 0 := by
    simpa only [leftMultiplication_apply, ZornVectorMatrix.mul_one,
      multiplicationDefect_one] using he
  apply hD
  calc
    multiplicationDefect X Y = leftMultiplication W := hW.symm
    _ = 0 := by rw [hW0, map_zero]

/-- Preserve the repository's explicit nonmultiplicativity witness. -/
theorem multiplicationDefect_U01_ne_zero :
    multiplicationDefect (ZornVectorMatrix.U 0) (ZornVectorMatrix.U 1) ≠ 0 := by
  intro h
  apply leftMultiplication_not_multiplicative
  unfold multiplicationDefect at h
  exact (sub_eq_zero.mp h).symm

/-- The native Zorn counterexample forces a strict extension of the space
of left actions inside its actual generated operator Lie algebra. -/
theorem left_action_range_lt_native_lieSpan :
    LinearMap.range leftMultiplication <
      (LieSubalgebra.lieSpan ℝ (Module.End ℝ Z)
        (Set.range leftMultiplication)).toSubmodule := by
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · intro T hT
    exact LieSubalgebra.subset_lieSpan hT
  · intro hback
    exact nonzero_multiplicationDefect_not_mem_left_range
      (ZornVectorMatrix.U 0) (ZornVectorMatrix.U 1)
      multiplicationDefect_U01_ne_zero
      (hback (multiplicationDefect_mem_native_lieSpan
        (ZornVectorMatrix.U 0) (ZornVectorMatrix.U 1)))

/-- If the operator idempotent is retained as well, the odd Peirce component
of the associator is generated inside the same operator Lie algebra. -/
theorem odd_multiplicationDefect_mem_of_left_actions
    (K : LieSubalgebra ℝ (Module.End ℝ Z))
    (hL : ∀ W : Z, leftMultiplication W ∈ K)
    (p : Module.End ℝ Z) (hp : p * p = p) (hpK : p ∈ K)
    (X Y : Z) :
    oddPart p (multiplicationDefect X Y) ∈ K := by
  exact oddPart_mem_of_mem K p (multiplicationDefect X Y) hp hpK
    (multiplicationDefect_mem_of_left_actions K hL X Y)

end
end InfoGeometry.Algebra.ZornLeftCAR
