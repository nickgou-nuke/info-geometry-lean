/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCl44TrialityDerivation
import InfoGeometry.Canonical.ZornCl44TrialityOrthogonal
import InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge

/-!
# A real mixed-plane triality derivation

The sign-corrected mixed bivector

`Tᵥ(e₁,f₂) - Tᵥ(f₁,e₂)`

is the existing canonical Peirce-stabilizing derivation associated with
the trace-zero matrix `!![0,-1,0; -1,0,0; 0,0,0]`.  Its Leibniz law is
inherited from that construction.  Both spinor bivector differences equal
the same operator.

The boost and rotation have squares `P` and `-P`, where `P` projects onto
their active four-dimensional spatial subspace.  Neither square is a
signed identity on the whole octonion carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44TrialityBoost

open ZornMatrix ZornClifford ZornSignedConvention ZornCl44Triality
open ZornCl44TrialityDerivation
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornPeirceSL3Bridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

local instance : LieRing (Module.End ℝ (ZornMatrix ℝ)) := LieRing.ofAssociativeRing

/-- Coordinate action of the existing trace-zero-matrix derivation on the
whole canonical Zorn carrier, including its two fixed scalar coordinates. -/
theorem sl3StabilizerCandidate_coordinates (M : SL3) (z : ZornMatrix ℝ) :
    (sl3StabilizerCandidate M).1 z =
      ⟨0, 0, M.1.mulVec z.x, (-Matrix.transpose M.1).mulVec z.y⟩ := by
  apply canonicalVectorEquiv.injective
  have hAction :
      canonicalToVectorDerivation (sl3StabilizerCandidate M)
          (canonicalVectorEquiv z) =
        ⟨0, M.1.mulVec z.x, (-Matrix.transpose M.1).mulVec z.y, 0⟩ := by
    change parameterAction (sl3Parameters M) (canonicalVectorEquiv z) = _
    exact sl3Parameters_parameterAction M (canonicalVectorEquiv z)
  have hNative := canonicalToVectorDerivation_apply
    (sl3StabilizerCandidate M) (canonicalVectorEquiv z)
  rw [Equiv.symm_apply_apply] at hNative
  exact hNative.symm.trans hAction

/-- The symmetric trace-zero spatial matrix for the mixed-plane boost. -/
def boost12Matrix : Matrix3 :=
  ![![0, -1, 0], ![-1, 0, 0], ![0, 0, 0]]

theorem boost12Matrix_trace_zero : Matrix.trace boost12Matrix = 0 := by
  norm_num [boost12Matrix, Matrix.trace, Matrix.diag, Fin.sum_univ_three,
    Matrix.vecHead, Matrix.vecTail]

/-- The boost parameter in the existing trace-zero matrix carrier. -/
def boost12MatrixSL3 : SL3 := ⟨boost12Matrix, boost12Matrix_trace_zero⟩

/-- The native derivation is obtained from the existing Peirce/`sl₃` bridge. -/
def boost12Derivation : canonicalZornDerivations :=
  sl3StabilizerCandidate boost12MatrixSL3

/-- The corresponding endomorphism of the existing real canonical carrier. -/
def boost12 : Module.End ℝ (ZornMatrix ℝ) := boost12Derivation.1

theorem boost12_mem_derivations : boost12 ∈ canonicalZornDerivations :=
  boost12Derivation.2

/-- Leibniz is inherited from the canonical trace-zero-matrix construction. -/
theorem boost12_leibniz (x y : ZornMatrix ℝ) :
    boost12 (x * y) = boost12 x * y + x * boost12 y :=
  boost12Derivation.2 x y

/-- The upper and lower spatial slots carry the standard and contragredient actions. -/
theorem boost12_coordinates (z : ZornMatrix ℝ) :
    boost12 z =
      ⟨0, 0, ![-z.x 1, -z.x 0, 0], ![z.y 1, z.y 0, 0]⟩ := by
  change (sl3StabilizerCandidate boost12MatrixSL3).1 z = _
  rw [sl3StabilizerCandidate_coordinates]
  apply ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;>
      norm_num [boost12MatrixSL3, boost12Matrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Matrix.vecHead, Matrix.vecTail]
  · funext i
    fin_cases i <;>
      simp [boost12MatrixSL3, boost12Matrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Matrix.transpose]

/-- Identification with the sign-corrected vector-bivector difference. -/
theorem boost12_eq_vectorBivector_difference :
    boost12 = vectorBivector (quaternionAxis 0) (splitAxis 1) -
      vectorBivector (splitAxis 0) (quaternionAxis 1) := by
  apply LinearMap.ext
  intro z
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [vectorBivector_apply, zornBilin_apply, quaternionAxis,
          splitAxis, chiralUpperBasis, chiralLowerBasis, dot,
          Matrix.vecHead, Matrix.vecTail] <;> ring)
    | (norm_num [vectorBivector_apply, zornBilin_apply, quaternionAxis,
        splitAxis, chiralUpperBasis, chiralLowerBasis, dot,
        Matrix.vecHead, Matrix.vecTail])

/-- The positive-chirality mixed bivector has the same diagonal derivation action. -/
theorem spinBivPlus_mixed_difference_eq_boost12 :
    spinBivPlus (quaternionAxis 0) (splitAxis 1) -
      spinBivPlus (splitAxis 0) (quaternionAxis 1) = boost12 := by
  apply LinearMap.ext
  intro z
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [spinBivPlus, Module.End.mul_apply, quaternionAxis, splitAxis,
          chiralUpperBasis, chiralLowerBasis, zornConj, ZornMatrix.mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail] <;> ring)
    | (norm_num [spinBivPlus, Module.End.mul_apply, quaternionAxis, splitAxis,
        chiralUpperBasis, chiralLowerBasis, zornConj, ZornMatrix.mul, dot, cross,
        Matrix.vecHead, Matrix.vecTail])

/-- The negative-chirality mixed bivector agrees with the same derivation. -/
theorem spinBivMinus_mixed_difference_eq_boost12 :
    spinBivMinus (quaternionAxis 0) (splitAxis 1) -
      spinBivMinus (splitAxis 0) (quaternionAxis 1) = boost12 := by
  apply LinearMap.ext
  intro z
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [spinBivMinus, Module.End.mul_apply, quaternionAxis, splitAxis,
          chiralUpperBasis, chiralLowerBasis, zornConj, ZornMatrix.mul, dot, cross,
          Matrix.vecHead, Matrix.vecTail] <;> ring)
    | (norm_num [spinBivMinus, Module.End.mul_apply, quaternionAxis, splitAxis,
        chiralUpperBasis, chiralLowerBasis, zornConj, ZornMatrix.mul, dot, cross,
        Matrix.vecHead, Matrix.vecTail])

theorem boost12_mem_skewAdjointLieSubalgebra :
    boost12 ∈ skewAdjointLieSubalgebra zornBilin := by
  rw [boost12_eq_vectorBivector_difference]
  exact (skewAdjointLieSubalgebra zornBilin).sub_mem
    (vectorBivector_mem_skewAdjointLieSubalgebra _ _)
    (vectorBivector_mem_skewAdjointLieSubalgebra _ _)

theorem boost12_one : boost12 (1 : ZornMatrix ℝ) = 0 := by
  rw [boost12_coordinates]
  apply ZornMatrix.ext <;> simp

theorem boost12_splitUnit : boost12 splitUnit = 0 := by
  rw [boost12_coordinates]
  apply ZornMatrix.ext <;> simp [splitUnit, zornPlus, zornMinus]

theorem boost12_quaternionAxis_zero :
    boost12 (quaternionAxis 0) = -splitAxis 1 := by
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [quaternionAxis, splitAxis, chiralUpperBasis, chiralLowerBasis,
          Matrix.vecHead, Matrix.vecTail])
    | norm_num [quaternionAxis, splitAxis, chiralUpperBasis, chiralLowerBasis,
        Matrix.vecHead, Matrix.vecTail]

theorem boost12_quaternionAxis_one :
    boost12 (quaternionAxis 1) = -splitAxis 0 := by
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [quaternionAxis, splitAxis, chiralUpperBasis, chiralLowerBasis,
          Matrix.vecHead, Matrix.vecTail])
    | norm_num [quaternionAxis, splitAxis, chiralUpperBasis, chiralLowerBasis,
        Matrix.vecHead, Matrix.vecTail]

theorem boost12_splitAxis_zero :
    boost12 (splitAxis 0) = -quaternionAxis 1 := by
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [quaternionAxis, splitAxis, chiralUpperBasis, chiralLowerBasis,
          Matrix.vecHead, Matrix.vecTail])
    | norm_num [quaternionAxis, splitAxis, chiralUpperBasis, chiralLowerBasis,
        Matrix.vecHead, Matrix.vecTail]

theorem boost12_splitAxis_one :
    boost12 (splitAxis 1) = -quaternionAxis 0 := by
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [quaternionAxis, splitAxis, chiralUpperBasis, chiralLowerBasis,
          Matrix.vecHead, Matrix.vecTail])
    | norm_num [quaternionAxis, splitAxis, chiralUpperBasis, chiralLowerBasis,
        Matrix.vecHead, Matrix.vecTail]

theorem boost12_quaternionAxis_two : boost12 (quaternionAxis 2) = 0 := by
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [quaternionAxis, chiralUpperBasis, chiralLowerBasis,
          Matrix.vecHead, Matrix.vecTail])
    | norm_num [quaternionAxis, chiralUpperBasis, chiralLowerBasis,
        Matrix.vecHead, Matrix.vecTail]

theorem boost12_splitAxis_two : boost12 (splitAxis 2) = 0 := by
  rw [boost12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        norm_num [splitAxis, chiralUpperBasis, chiralLowerBasis,
          Matrix.vecHead, Matrix.vecTail])
    | norm_num [splitAxis, chiralUpperBasis, chiralLowerBasis,
        Matrix.vecHead, Matrix.vecTail]

theorem boost12_ne_zero : boost12 ≠ 0 := by
  intro h
  have hx := congrArg (fun F : Module.End ℝ (ZornMatrix ℝ) =>
    (F (quaternionAxis 0)).x 1) h
  rw [boost12_quaternionAxis_zero] at hx
  norm_num [splitAxis, chiralUpperBasis, chiralLowerBasis,
    Matrix.vecHead, Matrix.vecTail] at hx

/-- Projection onto the two active spatial axes in both Zorn vector slots. -/
def active12Projector : Module.End ℝ (ZornMatrix ℝ) where
  toFun z := ⟨0, 0, ![z.x 0, z.x 1, 0], ![z.y 0, z.y 1, 0]⟩
  map_add' z w := by
    apply ZornMatrix.ext
    · simp
    · simp
    · funext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
    · funext i; fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail]
  map_smul' r z := by
    apply ZornMatrix.ext
    · simp
    · simp
    · funext i; fin_cases i <;> simp
    · funext i; fin_cases i <;> simp

@[simp] theorem active12Projector_apply (z : ZornMatrix ℝ) :
    active12Projector z =
      ⟨0, 0, ![z.x 0, z.x 1, 0], ![z.y 0, z.y 1, 0]⟩ := rfl

theorem active12Projector_idempotent : active12Projector * active12Projector = active12Projector := by
  apply LinearMap.ext
  intro z
  simp [Module.End.mul_apply, active12Projector_apply]

/-- The hyperbolic square is the active-space projection, not the full identity. -/
theorem boost12_square : boost12 * boost12 = active12Projector := by
  apply LinearMap.ext
  intro z
  simp only [Module.End.mul_apply, boost12_coordinates, active12Projector_apply]
  apply ZornMatrix.ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp

/-- The compact square is minus that same projection. -/
theorem rotation12_square : rotation12 * rotation12 = -active12Projector := by
  apply LinearMap.ext
  intro z
  simp only [Module.End.mul_apply, rotation12_coordinates,
    LinearMap.neg_apply, active12Projector_apply]
  apply ZornMatrix.ext
  · simp
  · simp
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp

theorem active12Projector_ne_one : active12Projector ≠ 1 := by
  intro h
  have ha := congrArg (fun F : Module.End ℝ (ZornMatrix ℝ) =>
    (F 1).a) h
  norm_num [active12Projector_apply] at ha

theorem boost12_square_ne_one : boost12 * boost12 ≠ 1 := by
  rw [boost12_square]
  exact active12Projector_ne_one

theorem rotation12_square_ne_neg_one : rotation12 * rotation12 ≠ -1 := by
  rw [rotation12_square]
  intro h
  exact active12Projector_ne_one (neg_injective h)

/-- Both real chiral halves carry this same derivation without being exchanged. -/
theorem spinBivector_mixed_difference_apply (s : DiracSpinor16 (R := ℝ)) :
    (spinBivector (quaternionAxis 0) (splitAxis 1) -
      spinBivector (splitAxis 0) (quaternionAxis 1)) s =
      (boost12 s.1, boost12 s.2) := by
  have hp := congrArg (fun F : Module.End ℝ (ZornMatrix ℝ) => F s.1)
    spinBivPlus_mixed_difference_eq_boost12
  have hm := congrArg (fun F : Module.End ℝ (ZornMatrix ℝ) => F s.2)
    spinBivMinus_mixed_difference_eq_boost12
  exact Prod.ext hp hm

end InfoGeometry.Canonical.ZornCl44TrialityBoost
