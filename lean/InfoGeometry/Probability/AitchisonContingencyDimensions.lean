/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.AitchisonContingency
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimensions of the rectangular CLR decomposition

These are dimensions of the native submodules in `AitchisonContingency`, not
parameter counts imposed as assumptions. The interaction range is the range of
an idempotent linear map, whose trace is computed in the standard matrix basis.
Rank-nullity then identifies the additive kernel. A second rank-nullity argument
uses total sum restricted to that additive kernel; an explicit linear equivalence
identifies the new kernel with the centered additive subspace.

Both index types are finite and nonempty. In particular a singleton row or column
type is allowed, and the interaction dimension is then zero.
-/

noncomputable section

namespace InfoGeometry.Probability.AitchisonContingency

open scoped BigOperators
open Module BipartiteLogCoupling

variable {I J : Type*} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]

omit [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] in
private lemma matrix_stdBasis_repr (X : Matrix I J ℝ) (i : I) (j : J) :
    (Matrix.stdBasis ℝ I J).repr X (i, j) = X i j := by
  simp [Matrix.stdBasis]

omit [Nonempty I] [Nonempty J] in
private lemma interaction_single_diagonal (i : I) (j : J) :
    interaction (Matrix.single i j (1 : ℝ)) i j =
      (1 - (Fintype.card I : ℝ)⁻¹) * (1 - (Fintype.card J : ℝ)⁻¹) := by
  simp [interaction, Matrix.mul_apply, Matrix.single, ite_and, center, average]

/-- The trace of the actual double-centering endomorphism. -/
theorem trace_interactionLinear :
    LinearMap.trace ℝ (Matrix I J ℝ) (interactionLinear (I := I) (J := J)) =
      ((Fintype.card I : ℝ) - 1) * ((Fintype.card J : ℝ) - 1) := by
  have hI : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hJ : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [LinearMap.trace_eq_matrix_trace ℝ (Matrix.stdBasis ℝ I J)]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
    LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, matrix_stdBasis_repr,
    interactionLinear_apply, interaction_single_diagonal]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hI, hJ]

/-- The interaction space has the product of the two centered dimensions. -/
theorem finrank_interactionSubspace :
    finrank ℝ (interactionSubspace (I := I) (J := J)) =
      (Fintype.card I - 1) * (Fintype.card J - 1) := by
  have hp : IsIdempotentElem (interactionLinear (I := I) (J := J)) := by
    apply LinearMap.ext
    intro X
    change interaction (interaction X) = interaction X
    exact interaction_idempotent X
  have ht := LinearMap.IsProj.trace
    (LinearMap.IsIdempotentElem.isProj_range (interactionLinear (I := I) (J := J)) hp)
  rw [trace_interactionLinear] at ht
  have hI : 1 ≤ Fintype.card I := Nat.succ_le_iff.mpr Fintype.card_pos
  have hJ : 1 ≤ Fintype.card J := Nat.succ_le_iff.mpr Fintype.card_pos
  have hcast :
      (finrank ℝ (interactionSubspace (I := I) (J := J)) : ℝ) =
        (((Fintype.card I - 1) * (Fintype.card J - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hI, Nat.cast_sub hJ, Nat.cast_one]
    exact ht.symm
  exact_mod_cast hcast

private lemma rectangle_dimension_identity (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (m - 1) * (n - 1) + (m + n - 1) = m * n := by
  have hs : m + n - 1 = (m - 1) + (n - 1) + 1 := by omega
  calc
    _ = ((m - 1) + 1) * ((n - 1) + 1) := by rw [hs]; ring
    _ = m * n := by rw [Nat.sub_add_cancel hm, Nat.sub_add_cancel hn]

/-- The full additive kernel includes the one-dimensional grand constant. -/
theorem finrank_additiveSubspace :
    finrank ℝ (additiveSubspace (I := I) (J := J)) =
      Fintype.card I + Fintype.card J - 1 := by
  have hr := (interactionLinear (I := I) (J := J)).finrank_range_add_finrank_ker
  change finrank ℝ (interactionSubspace (I := I) (J := J)) +
    finrank ℝ (additiveSubspace (I := I) (J := J)) =
      finrank ℝ (Matrix I J ℝ) at hr
  rw [finrank_interactionSubspace, Module.finrank_matrix] at hr
  simp only [Module.finrank_self, mul_one] at hr
  have hc := rectangle_dimension_identity (Fintype.card I) (Fintype.card J)
    (Nat.succ_le_iff.mpr Fintype.card_pos) (Nat.succ_le_iff.mpr Fintype.card_pos)
  omega

omit [Nonempty I] in
/-- Constant matrices are genuinely in the kernel of the interaction map. -/
theorem constant_mem_additiveSubspace (c : ℝ) :
    (fun (_ : I) (_ : J) => c) ∈ additiveSubspace (I := I) (J := J) := by
  change interaction (fun (_ : I) (_ : J) => c) = 0
  change center I * (rowShift (fun _ : I => c) : Matrix I J ℝ) * center J = 0
  rw [Matrix.mul_assoc, rowShift_center, Matrix.mul_zero]

omit [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] in
theorem totalSum_constant (c : ℝ) :
    totalSumLinear (fun (_ : I) (_ : J) => c) =
      (Fintype.card I : ℝ) * (Fintype.card J : ℝ) * c := by
  change (∑ _ : I, ∑ _ : J, c) = _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Total sum restricted to the actual additive submodule. -/
def totalSumOnAdditive : additiveSubspace (I := I) (J := J) →ₗ[ℝ] ℝ :=
  totalSumLinear.comp (additiveSubspace (I := I) (J := J)).subtype

/-- A constant matrix realizes every prescribed total sum. -/
theorem totalSumOnAdditive_surjective :
    Function.Surjective (totalSumOnAdditive (I := I) (J := J)) := by
  intro c
  have hI : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hJ : (Fintype.card J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨⟨fun _ _ => c / ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)),
    constant_mem_additiveSubspace _⟩, ?_⟩
  change totalSumLinear (fun (_ : I) (_ : J) =>
    c / ((Fintype.card I : ℝ) * (Fintype.card J : ℝ))) = c
  rw [totalSum_constant]
  field_simp [hI, hJ]

/-- The centered additive space is the kernel of total sum on the additive space. -/
def centeredAdditiveEquivKernel :
    centeredAdditiveSubspace (I := I) (J := J) ≃ₗ[ℝ]
      LinearMap.ker (totalSumOnAdditive (I := I) (J := J)) where
  toFun X := ⟨⟨X.1, X.2.1⟩, X.2.2⟩
  invFun X := ⟨X.1.1, ⟨X.1.2, X.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The centered additive/independence subspace excludes the grand constant. -/
theorem finrank_centeredAdditiveSubspace :
    finrank ℝ (centeredAdditiveSubspace (I := I) (J := J)) =
      Fintype.card I + Fintype.card J - 2 := by
  have hr := (totalSumOnAdditive (I := I) (J := J)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (totalSumOnAdditive_surjective (I := I) (J := J)),
    finrank_top, Module.finrank_self,
    ← (centeredAdditiveEquivKernel (I := I) (J := J)).finrank_eq,
    finrank_additiveSubspace] at hr
  have hI : 0 < Fintype.card I := Fintype.card_pos
  have hJ : 0 < Fintype.card J := Fintype.card_pos
  omega

/-- Total sum is onto on the ambient matrix space. -/
theorem totalSumLinear_surjective :
    Function.Surjective (totalSumLinear (I := I) (J := J)) := by
  intro c
  obtain ⟨X, hX⟩ := totalSumOnAdditive_surjective (I := I) (J := J) c
  exact ⟨X.1, hX⟩

/-- The complete CLR space is the codimension-one total-sum kernel. -/
theorem finrank_centeredSubspace :
    finrank ℝ (centeredSubspace (I := I) (J := J)) =
      Fintype.card I * Fintype.card J - 1 := by
  have hr := (totalSumLinear (I := I) (J := J)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (totalSumLinear_surjective (I := I) (J := J)),
    finrank_top, Module.finrank_self, Module.finrank_matrix] at hr
  simp only [Module.finrank_self, mul_one] at hr
  change 1 + finrank ℝ (centeredSubspace (I := I) (J := J)) =
    Fintype.card I * Fintype.card J at hr
  omega

end InfoGeometry.Probability.AitchisonContingency
