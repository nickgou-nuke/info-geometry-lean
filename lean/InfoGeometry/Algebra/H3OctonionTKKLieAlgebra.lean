/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.JordanTKKLieAlgebra
import InfoGeometry.Algebra.H3OctonionLieAlgebra
import Mathlib.Algebra.Lie.Killing
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# 133-Dimensional Compact-Jordan Exceptional Lie Algebra `𝔈₇(-25)` on `H3Octonion ℝ`

This module instantiates the generic 3-graded Jordan-TKK construction on the compact
27-dimensional Euclidean Albert Jordan algebra `H3Octonion ℝ` with its 79-dimensional
structure Lie subalgebra `h3OctonionStructureLieSubalgebra` and trace adjoint
`h3OctonionTraceAdjoint`:

1. `h3OctonionTKKDatum : JordanTKKDatum ℝ (H3Octonion ℝ)` and 133-dimensional real Lie algebra
   `H3OctonionTKKLie := JordanTKK (H3Octonion ℝ) h3OctonionTKKDatum.str` (`27 + 79 + 27 = 133`).
2. Grade constructors/projections, 9 homogeneous `@[simp]` bracket rules, `zeroLieHom`,
   `h3OctonionCubicStabilizerToTKK` (`E₆(-26)` embedding), grading element `h3OctonionTKKGradeOp`,
   non-triviality witnesses, and `center_H3OctonionTKKLie_eq_bot`.
3. Cartan involution `θ(x, T, y) = (-y, -T†, -x)`, compact `+1` eigenspace `k` (`finrank = 79`),
   non-compact `-1` eigenspace `p` (`finrank = 54`), Cartan signature `54 - 79 = -25`,
   `ad`-invariant bilinear form `tkkInvariantBilin` & positive-definite Cartan inner product
   `tkkCartanInner`, Killing form definiteness (`≤ 0` on `k`, `≥ 0` on `p`, `k ⊥ p`),
   `LieAlgebra.IsKilling ℝ H3OctonionTKKLie`, and concrete Killing/eigenvalue witnesses.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Octonion

attribute [local instance 100] LieRing.ofAssociativeRing

instance instModuleFiniteH3Octonion : Module.Finite ℝ (H3Octonion ℝ) :=
  Module.Finite.of_basis h3OctonionBasis

section TraceAdjointLaws

/-- `h3OctonionTraceAdjoint` packaged as an `ℝ`-linear endomorphism of
`Module.End ℝ (H3Octonion ℝ)`. -/
def h3OctonionTraceAdjointLM :
    Module.End ℝ (H3Octonion ℝ) →ₗ[ℝ] Module.End ℝ (H3Octonion ℝ) where
  toFun := h3OctonionTraceAdjoint
  map_add' A B := by
    apply LinearMap.ext
    intro x
    apply H3Octonion.eq_of_traceBilin_left_eq
    intro y
    rw [LinearMap.add_apply, traceBilin_add_left, h3OctonionTraceAdjoint_pair,
      h3OctonionTraceAdjoint_pair, h3OctonionTraceAdjoint_pair, LinearMap.add_apply,
      traceBilin_add_right]
  map_smul' r A := by
    apply LinearMap.ext
    intro x
    apply H3Octonion.eq_of_traceBilin_left_eq
    intro y
    rw [LinearMap.smul_apply, traceBilin_smul_left, h3OctonionTraceAdjoint_pair,
      h3OctonionTraceAdjoint_pair, LinearMap.smul_apply, traceBilin_smul_right, RingHom.id_apply]

@[simp] theorem h3OctonionTraceAdjointLM_apply (A : Module.End ℝ (H3Octonion ℝ)) :
    h3OctonionTraceAdjointLM A = h3OctonionTraceAdjoint A := rfl

theorem h3OctonionTraceAdjoint_comp (A B : Module.End ℝ (H3Octonion ℝ)) :
    h3OctonionTraceAdjoint (A ∘ₗ B) = h3OctonionTraceAdjoint B ∘ₗ h3OctonionTraceAdjoint A := by
  apply LinearMap.ext
  intro x
  apply H3Octonion.eq_of_traceBilin_left_eq
  intro y
  rw [LinearMap.comp_apply, h3OctonionTraceAdjoint_pair, h3OctonionTraceAdjoint_pair,
    h3OctonionTraceAdjoint_pair, LinearMap.comp_apply]

theorem h3OctonionTraceAdjoint_jordanLmul (a : H3Octonion ℝ) :
    h3OctonionTraceAdjoint (jordanLmul (R := ℝ) a) = jordanLmul (R := ℝ) a := by
  apply LinearMap.ext
  intro x
  apply H3Octonion.eq_of_traceBilin_left_eq
  intro y
  rw [h3OctonionTraceAdjoint_pair, jordanLmul_apply, jordanLmul_apply,
    ← h3Octonion_traceBilin_jordanLmul_assoc a x y, _root_.mul_comm a x]

theorem h3OctonionTraceAdjoint_derivation
    (D : NonAssocDerivation.derivations ℝ (H3Octonion ℝ)) :
    h3OctonionTraceAdjoint (D : Module.End ℝ (H3Octonion ℝ)) =
      -(D : Module.End ℝ (H3Octonion ℝ)) := by
  apply LinearMap.ext
  intro x
  apply H3Octonion.eq_of_traceBilin_left_eq
  intro y
  rw [h3OctonionTraceAdjoint_pair, LinearMap.neg_apply,
    show -((D : Module.End ℝ (H3Octonion ℝ)) x) =
      (-1 : ℝ) • ((D : Module.End ℝ (H3Octonion ℝ)) x) by module,
    traceBilin_smul_left, neg_one_mul]
  have hskew := h3Octonion_derivation_traceBilin_skew ⟨(D : Module.End ℝ (H3Octonion ℝ)), D.2⟩ x y
  exact eq_neg_of_add_eq_zero_right hskew

theorem h3OctonionTraceAdjoint_id :
    h3OctonionTraceAdjoint (LinearMap.id : Module.End ℝ (H3Octonion ℝ)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply H3Octonion.eq_of_traceBilin_left_eq
  intro y
  rw [h3OctonionTraceAdjoint_pair, LinearMap.id_apply, LinearMap.id_apply]

theorem h3OctonionTraceAdjoint_involutive (A : Module.End ℝ (H3Octonion ℝ)) :
    h3OctonionTraceAdjoint (h3OctonionTraceAdjoint A) = A := by
  apply LinearMap.ext
  intro x
  apply H3Octonion.eq_of_traceBilin_left_eq
  intro y
  rw [h3OctonionTraceAdjoint_pair, traceBilin_symm, h3OctonionTraceAdjoint_pair, traceBilin_symm]

end TraceAdjointLaws

/-- The verified TKK datum on the compact Albert algebra `H3Octonion ℝ`. -/
def h3OctonionTKKDatum : JordanTKKDatum ℝ (H3Octonion ℝ) where
  str := h3OctonionStructureLieSubalgebra.toSubmodule
  adj := h3OctonionTraceAdjointLM
  adj_comp := h3OctonionTraceAdjoint_comp
  adj_jordanLmul := h3OctonionTraceAdjoint_jordanLmul
  adj_derivation := h3OctonionTraceAdjoint_derivation
  str_decomp := by
    rintro T ⟨D, a, rfl⟩
    exact ⟨⟨(D : Module.End ℝ (H3Octonion ℝ)), D.2⟩, a, rfl⟩
  jordanLmul_mem_str a := ⟨0, a, by
    change jordanLmul (R := ℝ) a = (0 : Module.End ℝ (H3Octonion ℝ)) + jordanLmul (R := ℝ) a
    rw [zero_add]⟩
  innerDeriv_mem_str x y := by
    refine ⟨h3OctonionJordanInnerDerivation x y, 0, ?_⟩
    apply LinearMap.ext
    intro z
    change (jordanInnerDerivationBundled (R := ℝ) x y : Module.End ℝ (H3Octonion ℝ)) z =
      (h3OctonionJordanInnerDerivation x y : Module.End ℝ (H3Octonion ℝ)) z +
        (0 : H3Octonion ℝ) * z
    rw [zero_mul, add_zero]
    rfl
  str_lie_mem {T U} hT hU := h3OctonionStructureLieSubalgebra.lie_mem hT hU

/-- The 133-dimensional compact-Jordan real exceptional Lie algebra `𝔈₇(-25)`
on `H3Octonion ℝ`. -/
abbrev H3OctonionTKKLie := JordanTKK (H3Octonion ℝ) h3OctonionTKKDatum.str

instance instLieRingH3OctonionTKKLie : LieRing H3OctonionTKKLie :=
  JordanTKK.lieRing h3OctonionTKKDatum

instance instLieAlgebraH3OctonionTKKLie : LieAlgebra ℝ H3OctonionTKKLie :=
  JordanTKK.lieAlgebra h3OctonionTKKDatum

/-- **Exact 133-dimensionality of `𝔈₇(-25)`**: `27 + 79 + 27 = 133`. -/
theorem finrank_H3OctonionTKKLie : Module.finrank ℝ H3OctonionTKKLie = 133 := by
  rw [JordanTKK.finrank_jordanTKK (F := ℝ)]
  have h_str : Module.finrank ℝ h3OctonionTKKDatum.str = 79 := by
    change Module.finrank ℝ h3OctonionStructureLieSubalgebra = 79
    exact finrank_h3OctonionStructureLieSubalgebra
  rw [finrank_h3Octonion, h_str]

namespace H3OctonionTKKLie

/-- Grade `-1` injection `H3Octonion ℝ →ₗ[ℝ] H3OctonionTKKLie`. -/
def negInj : H3Octonion ℝ →ₗ[ℝ] H3OctonionTKKLie :=
  JordanTKK.negLM (R := ℝ) (J := H3Octonion ℝ) (S := h3OctonionTKKDatum.str)

/-- Grade `0` injection `h3OctonionTKKDatum.str →ₗ[ℝ] H3OctonionTKKLie`. -/
def zeroInj : h3OctonionTKKDatum.str →ₗ[ℝ] H3OctonionTKKLie :=
  JordanTKK.zeroLM (R := ℝ) (J := H3Octonion ℝ) (S := h3OctonionTKKDatum.str)

/-- Grade `+1` injection `H3Octonion ℝ →ₗ[ℝ] H3OctonionTKKLie`. -/
def posInj : H3Octonion ℝ →ₗ[ℝ] H3OctonionTKKLie :=
  JordanTKK.posLM (R := ℝ) (J := H3Octonion ℝ) (S := h3OctonionTKKDatum.str)

/-- Projection onto grade `-1`. -/
def projNeg : H3OctonionTKKLie →ₗ[ℝ] H3Octonion ℝ :=
  JordanTKK.projNeg (R := ℝ) (J := H3Octonion ℝ) (S := h3OctonionTKKDatum.str)

/-- Projection onto grade `0`. -/
def projZero : H3OctonionTKKLie →ₗ[ℝ] h3OctonionTKKDatum.str :=
  JordanTKK.projZero (R := ℝ) (J := H3Octonion ℝ) (S := h3OctonionTKKDatum.str)

/-- Projection onto grade `+1`. -/
def projPos : H3OctonionTKKLie →ₗ[ℝ] H3Octonion ℝ :=
  JordanTKK.projPos (R := ℝ) (J := H3Octonion ℝ) (S := h3OctonionTKKDatum.str)

theorem negInj_injective : Function.Injective negInj := JordanTKK.negLM_injective
theorem zeroInj_injective : Function.Injective zeroInj := JordanTKK.zeroLM_injective
theorem posInj_injective : Function.Injective posInj := JordanTKK.posLM_injective

theorem eq_neg_add_zero_add_pos (X : H3OctonionTKKLie) :
    X = negInj X.neg + zeroInj X.zero + posInj X.pos :=
  JordanTKK.eq_neg_add_zero_add_pos (R := ℝ) X

@[simp] theorem negInj_bracket_negInj (x₁ x₂ : H3Octonion ℝ) :
    ⁅negInj x₁, negInj x₂⁆ = 0 :=
  JordanTKK.neg_bracket_neg h3OctonionTKKDatum x₁ x₂

@[simp] theorem posInj_bracket_posInj (y₁ y₂ : H3Octonion ℝ) :
    ⁅posInj y₁, posInj y₂⁆ = 0 :=
  JordanTKK.pos_bracket_pos h3OctonionTKKDatum y₁ y₂

@[simp] theorem zeroInj_bracket_zeroInj (T₁ T₂ : h3OctonionTKKDatum.str) :
    ⁅zeroInj T₁, zeroInj T₂⁆ =
      zeroInj ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3OctonionTKKDatum.str_lie_mem T₁.2 T₂.2⟩ :=
  JordanTKK.zero_bracket_zero h3OctonionTKKDatum T₁ T₂

@[simp] theorem zeroInj_bracket_negInj (T : h3OctonionTKKDatum.str) (x : H3Octonion ℝ) :
    ⁅zeroInj T, negInj x⁆ = negInj (T.1 x) :=
  JordanTKK.zero_bracket_neg h3OctonionTKKDatum T x

@[simp] theorem negInj_bracket_zeroInj (x : H3Octonion ℝ) (T : h3OctonionTKKDatum.str) :
    ⁅negInj x, zeroInj T⁆ = negInj (-(T.1 x)) :=
  JordanTKK.neg_bracket_zero h3OctonionTKKDatum x T

@[simp] theorem zeroInj_bracket_posInj (T : h3OctonionTKKDatum.str) (y : H3Octonion ℝ) :
    ⁅zeroInj T, posInj y⁆ = posInj (-h3OctonionTraceAdjoint T.1 y) :=
  JordanTKK.zero_bracket_pos h3OctonionTKKDatum T y

@[simp] theorem posInj_bracket_zeroInj (y : H3Octonion ℝ) (T : h3OctonionTKKDatum.str) :
    ⁅posInj y, zeroInj T⁆ = posInj (h3OctonionTraceAdjoint T.1 y) :=
  JordanTKK.pos_bracket_zero h3OctonionTKKDatum y T

@[simp] theorem negInj_bracket_posInj (x y : H3Octonion ℝ) :
    ⁅negInj x, posInj y⁆ =
      zeroInj ⟨JordanTKK.tripleD ℝ x y, h3OctonionTKKDatum.tripleD_mem_str x y⟩ :=
  JordanTKK.neg_bracket_pos h3OctonionTKKDatum x y

@[simp] theorem posInj_bracket_negInj (y x : H3Octonion ℝ) :
    ⁅posInj y, negInj x⁆ =
      zeroInj ⟨-JordanTKK.tripleD ℝ x y,
        h3OctonionTKKDatum.str.neg_mem (h3OctonionTKKDatum.tripleD_mem_str x y)⟩ :=
  JordanTKK.pos_bracket_neg h3OctonionTKKDatum y x

/-- Canonical Lie-algebra inclusion of the 79D structure algebra into `H3OctonionTKKLie`. -/
def zeroLieHom : h3OctonionStructureLieSubalgebra →ₗ⁅ℝ⁆ H3OctonionTKKLie where
  toFun T := zeroInj ⟨T.1, T.2⟩
  map_add' T₁ T₂ := by
    change zeroInj (⟨T₁.1, T₁.2⟩ + ⟨T₂.1, T₂.2⟩) = _
    rw [map_add]
  map_smul' r T := by
    change zeroInj (r • ⟨T.1, T.2⟩) = _
    rw [map_smul]
    rfl
  map_lie' {T₁ T₂} := by
    change zeroInj ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3OctonionTKKDatum.str_lie_mem T₁.2 T₂.2⟩ =
      ⁅zeroInj ⟨T₁.1, T₁.2⟩, zeroInj ⟨T₂.1, T₂.2⟩⁆
    exact (zeroInj_bracket_zeroInj ⟨T₁.1, T₁.2⟩ ⟨T₂.1, T₂.2⟩).symm

theorem zeroLieHom_injective : Function.Injective zeroLieHom := by
  intro T₁ T₂ h
  apply Subtype.ext
  exact congrArg (fun X => X.zero.1) h

end H3OctonionTKKLie

section InclusionsAndGradeOp

open H3OctonionTKKLie

theorem h3OctonionCubicStabilizer_le_structureLieSubalgebra :
    h3OctonionCubicStabilizer ≤ h3OctonionStructureLieSubalgebra := by
  intro T hT
  obtain ⟨⟨D, a⟩, hEq⟩ := h3OctonionCubicStabilizerDirectSumEquiv.surjective ⟨T, hT⟩
  exact ⟨D, a.1, (congrArg Subtype.val hEq).symm⟩

/-- Canonical Lie-algebra embedding of the 78D reduced structure algebra `str₀ = E₆(-26)`
into `H3OctonionTKKLie`. -/
def h3OctonionCubicStabilizerToTKK : h3OctonionCubicStabilizer →ₗ⁅ℝ⁆ H3OctonionTKKLie :=
  zeroLieHom.comp (LieSubalgebra.inclusion h3OctonionCubicStabilizer_le_structureLieSubalgebra)

theorem h3OctonionCubicStabilizerToTKK_injective :
    Function.Injective h3OctonionCubicStabilizerToTKK := by
  intro T₁ T₂ h
  apply Subtype.ext
  exact congrArg (fun X => X.zero.1) h

/-- The identity operator `L₁ = id` in `h3OctonionTKKDatum.str`. -/
def h3OctonionStrOne : h3OctonionTKKDatum.str :=
  ⟨h3OctonionStructureOperator 0 (1 : H3Octonion ℝ), 0, 1, rfl⟩

theorem h3OctonionStrOne_coe_eq_id :
    (h3OctonionStrOne : Module.End ℝ (H3Octonion ℝ)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (0 : H3OctonionF4Derivations).1 x + (1 : H3Octonion ℝ) * x = x
  rw [ZeroMemClass.coe_zero, LinearMap.zero_apply, zero_add, one_mul_h3Octonion]

@[simp] theorem h3OctonionStrOne_apply (x : H3Octonion ℝ) :
    (h3OctonionStrOne : Module.End ℝ (H3Octonion ℝ)) x = x := by
  rw [h3OctonionStrOne_coe_eq_id, LinearMap.id_apply]

theorem h3OctonionStrOne_not_mem_cubicStabilizer :
    (h3OctonionStrOne : Module.End ℝ (H3Octonion ℝ)) ∉ h3OctonionCubicStabilizer := by
  intro hmem
  have h1 : jordanLmul (R := ℝ) (1 : H3Octonion ℝ) ∈ h3OctonionCubicStabilizer := by
    have heq : (h3OctonionStrOne : Module.End ℝ (H3Octonion ℝ)) =
        jordanLmul (R := ℝ) (1 : H3Octonion ℝ) := by
      apply LinearMap.ext
      intro x
      rw [h3OctonionStrOne_apply, jordanLmul_apply, one_mul_h3Octonion]
    rwa [← heq]
  rw [jordanLmul_mem_h3OctonionCubicStabilizer_iff, linearTrace_one] at h1
  norm_num at h1

/-- The canonical 3-grading element `H₀ = L₁ = id` inside `H3OctonionTKKLie`, with eigenvalues
`+1`, `0`, `-1` on `negInj`, `zeroInj`, `posInj` respectively. -/
def h3OctonionTKKGradeOp : H3OctonionTKKLie :=
  zeroInj h3OctonionStrOne

@[simp] theorem h3OctonionTKKGradeOp_bracket_neg (x : H3Octonion ℝ) :
    ⁅h3OctonionTKKGradeOp, negInj x⁆ = negInj x := by
  simp [h3OctonionTKKGradeOp]

@[simp] theorem h3OctonionTKKGradeOp_bracket_pos (y : H3Octonion ℝ) :
    ⁅h3OctonionTKKGradeOp, posInj y⁆ = -posInj y := by
  rw [h3OctonionTKKGradeOp, zeroInj_bracket_posInj, h3OctonionStrOne_coe_eq_id,
    h3OctonionTraceAdjoint_id, LinearMap.id_apply, map_neg]

@[simp] theorem h3OctonionTKKGradeOp_bracket_zero (T : h3OctonionTKKDatum.str) :
    ⁅h3OctonionTKKGradeOp, zeroInj T⁆ = 0 := by
  rw [h3OctonionTKKGradeOp, zeroInj_bracket_zeroInj]
  have h0 : (⟨h3OctonionStrOne.1 ∘ₗ T.1 - T.1 ∘ₗ h3OctonionStrOne.1,
      h3OctonionTKKDatum.str_lie_mem h3OctonionStrOne.2 T.2⟩ : h3OctonionTKKDatum.str) = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp
  rw [h0, map_zero]

private theorem h3Octonion_one_ne_zero : (1 : H3Octonion ℝ) ≠ 0 := by
  intro h
  have h1 := congrArg H3Octonion.α₁ h
  change (1 : ℝ) = 0 at h1
  exact one_ne_zero h1

theorem h3OctonionTKKGradeOp_bracket_neg_one_ne_zero :
    ⁅h3OctonionTKKGradeOp, negInj (1 : H3Octonion ℝ)⁆ ≠ 0 := by
  rw [h3OctonionTKKGradeOp_bracket_neg]
  intro h
  exact h3Octonion_one_ne_zero (negInj_injective (h.trans (map_zero negInj).symm))

theorem negInj_one_bracket_posInj_one_eq_gradeOp :
    ⁅negInj (1 : H3Octonion ℝ), posInj (1 : H3Octonion ℝ)⁆ = h3OctonionTKKGradeOp := by
  rw [negInj_bracket_posInj, h3OctonionTKKGradeOp]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rw [JordanTKK.tripleD_apply, JordanTKK.triple, h3OctonionStrOne_apply]
  simp only [h3Octonion_mul_one, one_mul_h3Octonion]
  abel

theorem negInj_one_bracket_posInj_one_ne_zero :
    ⁅negInj (1 : H3Octonion ℝ), posInj (1 : H3Octonion ℝ)⁆ ≠ 0 := by
  rw [negInj_one_bracket_posInj_one_eq_gradeOp]
  intro h
  have h1 := congrArg (fun X : H3OctonionTKKLie => X.zero.1 1) h
  change h3OctonionStrOne.1 1 = (0 : Module.End ℝ (H3Octonion ℝ)) 1 at h1
  rw [h3OctonionStrOne_apply, LinearMap.zero_apply] at h1
  exact h3Octonion_one_ne_zero h1

theorem center_H3OctonionTKKLie_eq_bot :
    LieAlgebra.center ℝ H3OctonionTKKLie = ⊥ := by
  rw [eq_bot_iff]
  intro X hX
  rw [LieSubmodule.mem_bot]
  have hcomm : ∀ Y : H3OctonionTKKLie, ⁅Y, X⁆ = 0 :=
    (LieModule.mem_maxTrivSubmodule ℝ H3OctonionTKKLie H3OctonionTKKLie X).mp hX
  have hgr : ⁅h3OctonionTKKGradeOp, X⁆ = 0 := hcomm h3OctonionTKKGradeOp
  have hdecomp : ⁅h3OctonionTKKGradeOp, X⁆ = negInj X.neg - posInj X.pos := by
    conv_lhs => rw [eq_neg_add_zero_add_pos X]
    simp only [lie_add, h3OctonionTKKGradeOp_bracket_neg, h3OctonionTKKGradeOp_bracket_zero,
      h3OctonionTKKGradeOp_bracket_pos, add_zero, sub_eq_add_neg]
  rw [hgr] at hdecomp
  have hneg : X.neg = 0 := by
    have h := congrArg JordanTKK.neg hdecomp
    simp only [negInj, posInj, JordanTKK.zero_neg, JordanTKK.sub_neg_comp,
      JordanTKK.negLM_neg, JordanTKK.posLM_neg, sub_zero] at h
    exact h.symm
  have hpos : X.pos = 0 := by
    have h := congrArg JordanTKK.pos hdecomp
    simp only [negInj, posInj, JordanTKK.zero_pos, JordanTKK.sub_pos_comp,
      JordanTKK.negLM_pos, JordanTKK.posLM_pos, zero_sub] at h
    exact neg_eq_zero.mp h.symm
  have hzero : X.zero = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    have hx := hcomm (negInj x)
    have hX0 : X = zeroInj X.zero := by
      conv_lhs => rw [eq_neg_add_zero_add_pos X]
      rw [hneg, hpos, map_zero, map_zero, zero_add, add_zero]
    rw [hX0, negInj_bracket_zeroInj] at hx
    have hnx := negInj_injective (hx.trans (map_zero negInj).symm)
    simpa using hnx
  ext <;> simp [hneg, hzero, hpos]

end InclusionsAndGradeOp

section CartanInvolutionAndEigenspaces

open H3OctonionTKKLie

private theorem adj_neg_adj (A : Module.End ℝ (H3Octonion ℝ)) :
    h3OctonionTraceAdjoint (-h3OctonionTraceAdjoint A) = -A := by
  rw [← h3OctonionTraceAdjointLM_apply, map_neg, h3OctonionTraceAdjointLM_apply,
    h3OctonionTraceAdjoint_involutive]

private theorem adj_tripleD_local (x y : H3Octonion ℝ) :
    h3OctonionTraceAdjoint (JordanTKK.tripleD ℝ x y) = JordanTKK.tripleD ℝ y x :=
  h3OctonionTKKDatum.adj_tripleD x y

private theorem neg_adj_mem_str (T : h3OctonionTKKDatum.str) :
    -h3OctonionTraceAdjoint T.1 ∈ h3OctonionTKKDatum.str :=
  h3OctonionTKKDatum.str.neg_mem (h3OctonionTKKDatum.adj_mem_str T.2)

private def cartanInvolutionFun (X : H3OctonionTKKLie) : H3OctonionTKKLie where
  neg := -X.pos
  zero := ⟨-h3OctonionTraceAdjoint X.zero.1, neg_adj_mem_str X.zero⟩
  pos := -X.neg

/-- The canonical Cartan involution `θ(x, T, y) = (-y, -T†, -x)` of `𝔈₇(-25)`. -/
def h3OctonionCartanInvolution : H3OctonionTKKLie ≃ₗ⁅ℝ⁆ H3OctonionTKKLie where
  toFun := cartanInvolutionFun
  invFun := cartanInvolutionFun
  left_inv X := by
    apply JordanTKK.ext
    · simp [cartanInvolutionFun]
    · apply Subtype.ext
      change -h3OctonionTraceAdjoint (-h3OctonionTraceAdjoint X.zero.1) = X.zero.1
      rw [adj_neg_adj, neg_neg]
    · simp [cartanInvolutionFun]
  right_inv X := by
    apply JordanTKK.ext
    · simp [cartanInvolutionFun]
    · apply Subtype.ext
      change -h3OctonionTraceAdjoint (-h3OctonionTraceAdjoint X.zero.1) = X.zero.1
      rw [adj_neg_adj, neg_neg]
    · simp [cartanInvolutionFun]
  map_add' X Y := by
    apply JordanTKK.ext
    · simp [cartanInvolutionFun]; abel
    · apply Subtype.ext
      change -h3OctonionTraceAdjoint (X.zero.1 + Y.zero.1) =
        -h3OctonionTraceAdjoint X.zero.1 + -h3OctonionTraceAdjoint Y.zero.1
      rw [← h3OctonionTraceAdjointLM_apply, map_add, h3OctonionTraceAdjointLM_apply,
        h3OctonionTraceAdjointLM_apply, neg_add]
    · simp [cartanInvolutionFun]; abel
  map_smul' r X := by
    apply JordanTKK.ext
    · simp [cartanInvolutionFun]
    · apply Subtype.ext
      change -h3OctonionTraceAdjoint (r • X.zero.1) = r • (-h3OctonionTraceAdjoint X.zero.1)
      rw [← h3OctonionTraceAdjointLM_apply, map_smul, h3OctonionTraceAdjointLM_apply, smul_neg]
    · simp [cartanInvolutionFun]
  map_lie' {X Y} := by
    apply JordanTKK.ext
    · change -(-h3OctonionTraceAdjoint X.zero.1 Y.pos + h3OctonionTraceAdjoint Y.zero.1 X.pos) =
        (-h3OctonionTraceAdjoint X.zero.1) (-Y.pos) - (-h3OctonionTraceAdjoint Y.zero.1) (-X.pos)
      simp only [LinearMap.neg_apply, map_neg]
      abel
    · apply Subtype.ext
      change -h3OctonionTraceAdjoint ((X.zero.1 ∘ₗ Y.zero.1 - Y.zero.1 ∘ₗ X.zero.1) +
          (JordanTKK.tripleD ℝ X.neg Y.pos - JordanTKK.tripleD ℝ Y.neg X.pos)) =
        ((-h3OctonionTraceAdjoint X.zero.1) ∘ₗ (-h3OctonionTraceAdjoint Y.zero.1) -
          (-h3OctonionTraceAdjoint Y.zero.1) ∘ₗ (-h3OctonionTraceAdjoint X.zero.1)) +
        (JordanTKK.tripleD ℝ (-X.pos) (-Y.neg) - JordanTKK.tripleD ℝ (-Y.pos) (-X.neg))
      rw [← h3OctonionTraceAdjointLM_apply, map_add, map_sub, map_sub]
      simp only [h3OctonionTraceAdjointLM_apply, h3OctonionTraceAdjoint_comp, adj_tripleD_local]
      have htri : ∀ u v : H3Octonion ℝ,
          JordanTKK.tripleD ℝ (-u) (-v) = JordanTKK.tripleD ℝ u v := by
        intro u v
        rw [show -u = (-1 : ℝ) • u by module, show -v = (-1 : ℝ) • v by module,
          JordanTKK.tripleD_smul_left, JordanTKK.tripleD_smul_right, smul_smul]
        norm_num
      rw [htri X.pos Y.neg, htri Y.pos X.neg]
      simp only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]
      abel
    · change -(X.zero.1 Y.neg - Y.zero.1 X.neg) =
        -h3OctonionTraceAdjoint (-h3OctonionTraceAdjoint X.zero.1) (-Y.neg) +
          h3OctonionTraceAdjoint (-h3OctonionTraceAdjoint Y.zero.1) (-X.neg)
      rw [adj_neg_adj, adj_neg_adj]
      simp only [LinearMap.neg_apply, map_neg, neg_neg]
      abel

@[simp] theorem h3OctonionCartanInvolution_neg (X : H3OctonionTKKLie) :
    (h3OctonionCartanInvolution X).neg = -X.pos := rfl

@[simp] theorem h3OctonionCartanInvolution_zero (X : H3OctonionTKKLie) :
    (h3OctonionCartanInvolution X).zero =
      ⟨-h3OctonionTraceAdjoint X.zero.1, neg_adj_mem_str X.zero⟩ := rfl

@[simp] theorem h3OctonionCartanInvolution_zero_coe (X : H3OctonionTKKLie) :
    (h3OctonionCartanInvolution X).zero.1 = -h3OctonionTraceAdjoint X.zero.1 := rfl

@[simp] theorem h3OctonionCartanInvolution_pos (X : H3OctonionTKKLie) :
    (h3OctonionCartanInvolution X).pos = -X.neg := rfl

theorem h3OctonionCartanInvolution_involutive (X : H3OctonionTKKLie) :
    h3OctonionCartanInvolution (h3OctonionCartanInvolution X) = X :=
  h3OctonionCartanInvolution.left_inv X

/-- The compact `+1` eigenspace `k` (`79`-dimensional) of `h3OctonionCartanInvolution`. -/
def h3OctonionCartanCompactSubalgebra : LieSubalgebra ℝ H3OctonionTKKLie where
  carrier := {X | h3OctonionCartanInvolution X = X}
  zero_mem' := map_zero h3OctonionCartanInvolution
  add_mem' {X Y} hX hY := by
    change h3OctonionCartanInvolution (X + Y) = X + Y
    rw [map_add, hX, hY]
  smul_mem' r X hX := by
    change h3OctonionCartanInvolution (r • X) = r • X
    rw [map_smul, hX]
  lie_mem' {X Y} hX hY := by
    change h3OctonionCartanInvolution ⁅X, Y⁆ = ⁅X, Y⁆
    rw [LieEquiv.map_lie, hX, hY]

/-- The non-compact `-1` eigenspace `p` (`54`-dimensional) of `h3OctonionCartanInvolution`. -/
def h3OctonionCartanNoncompactSubmodule : Submodule ℝ H3OctonionTKKLie where
  carrier := {X | h3OctonionCartanInvolution X = -X}
  zero_mem' := by
    change h3OctonionCartanInvolution 0 = -(0 : H3OctonionTKKLie)
    rw [map_zero, neg_zero]
  add_mem' {X Y} hX hY := by
    change h3OctonionCartanInvolution (X + Y) = -(X + Y)
    rw [map_add, hX, hY, neg_add]
  smul_mem' r X hX := by
    change h3OctonionCartanInvolution (r • X) = -(r • X)
    rw [map_smul, hX, smul_neg]

@[simp] theorem mem_h3OctonionCartanCompactSubalgebra (X : H3OctonionTKKLie) :
    X ∈ h3OctonionCartanCompactSubalgebra ↔ h3OctonionCartanInvolution X = X := Iff.rfl

@[simp] theorem mem_h3OctonionCartanNoncompactSubmodule (X : H3OctonionTKKLie) :
    X ∈ h3OctonionCartanNoncompactSubmodule ↔ h3OctonionCartanInvolution X = -X := Iff.rfl

theorem h3OctonionCartanCompact_bracket_noncompact {X Y : H3OctonionTKKLie}
    (hX : X ∈ h3OctonionCartanCompactSubalgebra)
    (hY : Y ∈ h3OctonionCartanNoncompactSubmodule) :
    ⁅X, Y⁆ ∈ h3OctonionCartanNoncompactSubmodule := by
  change h3OctonionCartanInvolution ⁅X, Y⁆ = -⁅X, Y⁆
  rw [LieEquiv.map_lie, hX, hY, lie_neg]

theorem h3OctonionCartanNoncompact_bracket_noncompact {X Y : H3OctonionTKKLie}
    (hX : X ∈ h3OctonionCartanNoncompactSubmodule)
    (hY : Y ∈ h3OctonionCartanNoncompactSubmodule) :
    ⁅X, Y⁆ ∈ h3OctonionCartanCompactSubalgebra := by
  change h3OctonionCartanInvolution ⁅X, Y⁆ = ⁅X, Y⁆
  rw [LieEquiv.map_lie, hX, hY, neg_lie, lie_neg, neg_neg]

theorem h3OctonionCartan_decomposition_isCompl :
    IsCompl h3OctonionCartanCompactSubalgebra.toSubmodule h3OctonionCartanNoncompactSubmodule := by
  rw [isCompl_iff]
  constructor
  · rw [Submodule.disjoint_def]
    intro X hXk hXp
    have h2 : (2 : ℝ) • X = 0 := by
      have h1 : h3OctonionCartanInvolution X = X := hXk
      have h2' : h3OctonionCartanInvolution X = -X := hXp
      have hX0 : X = -X := h1.symm.trans h2'
      calc (2 : ℝ) • X = X + X := two_smul ℝ X
        _ = X + (-X) := by conv_rhs => rw [← hX0]
        _ = 0 := add_neg_cancel X
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    let Xk : H3OctonionTKKLie := (1 / 2 : ℝ) • (X + h3OctonionCartanInvolution X)
    let Xp : H3OctonionTKKLie := (1 / 2 : ℝ) • (X - h3OctonionCartanInvolution X)
    have hXk : Xk ∈ h3OctonionCartanCompactSubalgebra.toSubmodule := by
      change h3OctonionCartanInvolution Xk = Xk
      dsimp [Xk]
      rw [map_smul, map_add, h3OctonionCartanInvolution_involutive, add_comm]
    have hXp : Xp ∈ h3OctonionCartanNoncompactSubmodule := by
      change h3OctonionCartanInvolution Xp = -Xp
      dsimp [Xp]
      rw [map_smul, map_sub, h3OctonionCartanInvolution_involutive, ← smul_neg, neg_sub]
    have hsum : X = Xk + Xp := by
      dsimp [Xk, Xp]
      module
    rw [hsum]
    exact Submodule.add_mem_sup hXk hXp

private theorem h3Octonion_str_deriv_add_lmul_unique
    {D : H3OctonionF4Derivations} {a : H3Octonion ℝ}
    (h : D.1 + jordanLmul (R := ℝ) a = 0) : D = 0 ∧ a = 0 := by
  have h1 := LinearMap.ext_iff.mp h (1 : H3Octonion ℝ)
  have ha : a = 0 := by
    change D.1 1 + a * (1 : H3Octonion ℝ) = 0 at h1
    rw [h3Octonion_derivation_apply_one_eq_zero D, zero_add, h3Octonion_mul_one] at h1
    exact h1
  have hD : D = 0 := by
    apply Subtype.ext
    rw [ha] at h
    have hl0 : jordanLmul (R := ℝ) (0 : H3Octonion ℝ) = 0 := by
      apply LinearMap.ext; intro x; simp [jordanLmul_apply]
    rw [hl0, add_zero] at h
    exact h
  exact ⟨hD, ha⟩

private theorem deriv_mem_str (D : H3OctonionF4Derivations) :
    D.1 ∈ h3OctonionTKKDatum.str :=
  ⟨D, 0, by
    apply LinearMap.ext; intro x
    simp [h3OctonionStructureOperator, jordanLmul_apply]⟩

private def cartanCompactLinear :
    (H3Octonion ℝ × H3OctonionF4Derivations) →ₗ[ℝ] h3OctonionCartanCompactSubalgebra where
  toFun p :=
    ⟨⟨p.1, ⟨p.2.1, deriv_mem_str p.2⟩, -p.1⟩, by
      apply JordanTKK.ext
      · simp
      · apply Subtype.ext
        change -h3OctonionTraceAdjoint (p.2.1) = p.2.1
        have hd := h3OctonionTraceAdjoint_derivation ⟨p.2.1, p.2.2⟩
        change h3OctonionTraceAdjoint p.2.1 = -p.2.1 at hd
        rw [hd, neg_neg]
      · simp⟩
  map_add' p q := by
    apply Subtype.ext
    apply JordanTKK.ext
    · rfl
    · apply Subtype.ext; rfl
    · simp; abel
  map_smul' r p := by
    apply Subtype.ext
    apply JordanTKK.ext
    · rfl
    · apply Subtype.ext; rfl
    · simp

/-- Explicit linear equivalence `(H3Octonion ℝ × H3OctonionF4Derivations) ≃ₗ[ℝ] k`
identifying the 79-dimensional compact `+1` Cartan eigenspace `k`. -/
def h3OctonionCartanCompactEquiv :
    (H3Octonion ℝ × H3OctonionF4Derivations) ≃ₗ[ℝ] h3OctonionCartanCompactSubalgebra :=
  LinearEquiv.ofBijective cartanCompactLinear
    ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨x, D⟩ h
      have h0 : (cartanCompactLinear (x, D) : H3OctonionTKKLie) = 0 := congrArg Subtype.val h
      have hx : x = 0 := congrArg JordanTKK.neg h0
      have hD : D = 0 := Subtype.ext (congrArg (fun X => X.zero.1) h0)
      exact Prod.ext hx hD,
    by
      rintro ⟨X, hX⟩
      have hneg : X.pos = -X.neg := by
        have h := congrArg JordanTKK.neg hX
        exact neg_eq_iff_eq_neg.mp h
      have hadj : -h3OctonionTraceAdjoint X.zero.1 = X.zero.1 :=
        congrArg (fun Z : H3OctonionTKKLie => Z.zero.1) hX
      obtain ⟨⟨D, a⟩, hDa⟩ := h3OctonionStructureDirectSumEquiv.surjective ⟨X.zero.1, X.zero.2⟩
      have hT : X.zero.1 = D.1 + jordanLmul (R := ℝ) a := (congrArg Subtype.val hDa).symm
      have hadjT : h3OctonionTraceAdjoint X.zero.1 = -D.1 + jordanLmul (R := ℝ) a := by
        rw [hT, ← h3OctonionTraceAdjointLM_apply, map_add, h3OctonionTraceAdjointLM_apply,
          h3OctonionTraceAdjointLM_apply, h3OctonionTraceAdjoint_derivation ⟨D.1, D.2⟩,
          h3OctonionTraceAdjoint_jordanLmul]
      rw [hadjT, neg_add, neg_neg, hT] at hadj
      have ha2 : jordanLmul (R := ℝ) ((2 : ℝ) • a) = 0 := by
        apply LinearMap.ext; intro z
        have hz := LinearMap.ext_iff.mp hadj z
        change D.1 z - jordanLmul (R := ℝ) a z = D.1 z + jordanLmul (R := ℝ) a z at hz
        have h2a : jordanLmul (R := ℝ) a z + jordanLmul (R := ℝ) a z = 0 := by
          have hz' := congrArg (fun w => w - D.1 z) hz
          simp only [sub_sub_cancel_left, add_sub_cancel_left] at hz'
          calc jordanLmul (R := ℝ) a z + jordanLmul (R := ℝ) a z
              = -(jordanLmul (R := ℝ) a z) + jordanLmul (R := ℝ) a z := by
                  nth_rw 1 [← hz']
            _ = 0 := neg_add_cancel _
        change ((2 : ℝ) • a) * z = 0
        rw [smul_mul_assoc, two_smul]
        exact h2a
      have ha0 : a = 0 := by
        have h1 := LinearMap.ext_iff.mp ha2 (1 : H3Octonion ℝ)
        change ((2 : ℝ) • a) * 1 = 0 at h1
        rw [h3Octonion_mul_one] at h1
        exact (smul_eq_zero.mp h1).resolve_left (by norm_num)
      have hXD : X.zero.1 = D.1 := by
        rw [hT, ha0]
        apply LinearMap.ext; intro z; simp [jordanLmul_apply]
      refine ⟨(X.neg, D), ?_⟩
      apply Subtype.ext
      apply JordanTKK.ext
      · rfl
      · apply Subtype.ext; exact hXD.symm
      · exact hneg.symm⟩

theorem finrank_h3OctonionCartanCompactSubalgebra :
    Module.finrank ℝ h3OctonionCartanCompactSubalgebra = 79 := by
  rw [← LinearEquiv.finrank_eq h3OctonionCartanCompactEquiv, Module.finrank_prod,
    finrank_h3Octonion, finrank_H3OctonionF4Derivations]

private def cartanNoncompactLinear :
    (H3Octonion ℝ × H3Octonion ℝ) →ₗ[ℝ] h3OctonionCartanNoncompactSubmodule where
  toFun p :=
    ⟨⟨p.1, ⟨jordanLmul (R := ℝ) p.2, 0, p.2, by simp [h3OctonionStructureOperator]⟩, p.1⟩, by
      apply JordanTKK.ext
      · simp
      · apply Subtype.ext
        change -h3OctonionTraceAdjoint (jordanLmul (R := ℝ) p.2) = -jordanLmul (R := ℝ) p.2
        rw [h3OctonionTraceAdjoint_jordanLmul]
      · simp⟩
  map_add' p q := by
    apply Subtype.ext
    apply JordanTKK.ext
    · rfl
    · apply Subtype.ext; apply LinearMap.ext; intro z
      change (p.2 + q.2) * z = p.2 * z + q.2 * z
      exact add_mul p.2 q.2 z
    · rfl
  map_smul' r p := by
    apply Subtype.ext
    apply JordanTKK.ext
    · rfl
    · apply Subtype.ext; apply LinearMap.ext; intro z
      change (r • p.2) * z = r • (p.2 * z)
      exact smul_mul_assoc r p.2 z
    · rfl

/-- Explicit linear equivalence `(H3Octonion ℝ × H3Octonion ℝ) ≃ₗ[ℝ] p`
identifying the 54-dimensional non-compact `-1` Cartan eigenspace `p`. -/
def h3OctonionCartanNoncompactEquiv :
    (H3Octonion ℝ × H3Octonion ℝ) ≃ₗ[ℝ] h3OctonionCartanNoncompactSubmodule :=
  LinearEquiv.ofBijective cartanNoncompactLinear
    ⟨by
      rw [injective_iff_map_eq_zero]
      rintro ⟨x, a⟩ h
      have h0 : (cartanNoncompactLinear (x, a) : H3OctonionTKKLie) = 0 := congrArg Subtype.val h
      have hx : x = 0 := congrArg JordanTKK.neg h0
      have ha : a = 0 := by
        have hL := congrArg (fun X : H3OctonionTKKLie => X.zero.1 1) h0
        change a * (1 : H3Octonion ℝ) = 0 at hL
        rwa [h3Octonion_mul_one] at hL
      exact Prod.ext hx ha,
    by
      rintro ⟨X, hX⟩
      have hpos : X.pos = X.neg := by
        have h := congrArg JordanTKK.neg hX
        exact neg_inj.mp h
      have hadj : -h3OctonionTraceAdjoint X.zero.1 = -X.zero.1 :=
        congrArg (fun Z : H3OctonionTKKLie => Z.zero.1) hX
      have hadj' : h3OctonionTraceAdjoint X.zero.1 = X.zero.1 := neg_inj.mp hadj
      obtain ⟨⟨D, a⟩, hDa⟩ := h3OctonionStructureDirectSumEquiv.surjective ⟨X.zero.1, X.zero.2⟩
      have hT : X.zero.1 = D.1 + jordanLmul (R := ℝ) a := (congrArg Subtype.val hDa).symm
      have hadjT : h3OctonionTraceAdjoint X.zero.1 = -D.1 + jordanLmul (R := ℝ) a := by
        rw [hT, ← h3OctonionTraceAdjointLM_apply, map_add, h3OctonionTraceAdjointLM_apply,
          h3OctonionTraceAdjointLM_apply, h3OctonionTraceAdjoint_derivation ⟨D.1, D.2⟩,
          h3OctonionTraceAdjoint_jordanLmul]
      rw [hadjT, hT] at hadj'
      have h2D : (2 : ℝ) • D.1 = 0 := by
        apply LinearMap.ext; intro z
        have hz := LinearMap.ext_iff.mp hadj' z
        change -D.1 z + jordanLmul (R := ℝ) a z = D.1 z + jordanLmul (R := ℝ) a z at hz
        have hz' : -D.1 z = D.1 z := add_right_cancel hz
        rw [LinearMap.smul_apply, two_smul]
        nth_rw 1 [← hz']
        exact neg_add_cancel _
      have hD0 : D.1 = 0 := (smul_eq_zero.mp h2D).resolve_left (by norm_num)
      have hXL : X.zero.1 = jordanLmul (R := ℝ) a := by rw [hT, hD0, zero_add]
      refine ⟨(X.neg, a), ?_⟩
      apply Subtype.ext
      apply JordanTKK.ext
      · rfl
      · apply Subtype.ext; exact hXL.symm
      · exact hpos.symm⟩

theorem finrank_h3OctonionCartanNoncompactSubmodule :
    Module.finrank ℝ h3OctonionCartanNoncompactSubmodule = 54 := by
  rw [← LinearEquiv.finrank_eq h3OctonionCartanNoncompactEquiv, Module.finrank_prod,
    finrank_h3Octonion]

/-- **Cartan Signature of `𝔈₇(-25)`**: `dim p - dim k = 54 - 79 = -25`. -/
theorem h3OctonionCartan_signature_eq_neg_25 :
    (Module.finrank ℝ h3OctonionCartanNoncompactSubmodule : ℤ) -
      Module.finrank ℝ h3OctonionCartanCompactSubalgebra = -25 := by
  rw [finrank_h3OctonionCartanNoncompactSubmodule, finrank_h3OctonionCartanCompactSubalgebra]
  norm_num

end CartanInvolutionAndEigenspaces

section KillingFormAndInvariantBilin

open H3OctonionTKKLie

private theorem sum_fin27_split (f : Fin 27 → ℝ) :
    ∑ k : Fin 27, f k = f 0 + f 1 + f 2 +
      (∑ i : Fin 8, f ⟨3 + i.val, by omega⟩) +
      (∑ i : Fin 8, f ⟨11 + i.val, by omega⟩) +
      (∑ i : Fin 8, f ⟨19 + i.val, by omega⟩) := by
  let g : ℕ → ℝ := fun i => if h : i < 27 then f ⟨i, h⟩ else 0
  have hg_main : ∑ k : Fin 27, f k = ∑ i ∈ Finset.range 27, g i := by
    rw [Finset.sum_fin_eq_sum_range]
  have h27 : (∑ i ∈ Finset.range 27, g i) =
      (∑ i ∈ Finset.range 3, g i) +
      (∑ i ∈ Finset.range 8, g (3 + i)) +
      (∑ i ∈ Finset.range 8, g (3 + (8 + i))) +
      (∑ i ∈ Finset.range 8, g (3 + (8 + (8 + i)))) := by
    rw [show (27 : ℕ) = 3 + (8 + (8 + 8)) from rfl,
      Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add]
    ring
  have h3 : ∑ i ∈ Finset.range 3, g i = f 0 + f 1 + f 2 := by
    simp [g, Finset.sum_range_succ, add_assoc]
  have h12 : ∑ i ∈ Finset.range 8, g (3 + i) = ∑ i : Fin 8, f ⟨3 + i.val, by omega⟩ := by
    rw [Finset.sum_fin_eq_sum_range (fun i : Fin 8 => f ⟨3 + i.val, by omega⟩)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx8 : x < 8 := Finset.mem_range.mp hx
    simp [g, hx8, show 3 + x < 27 by omega]
  have h23 : ∑ i ∈ Finset.range 8, g (3 + (8 + i)) =
      ∑ i : Fin 8, f ⟨11 + i.val, by omega⟩ := by
    rw [Finset.sum_fin_eq_sum_range (fun i : Fin 8 => f ⟨11 + i.val, by omega⟩)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx8 : x < 8 := Finset.mem_range.mp hx
    have heq : (⟨3 + (8 + x), by omega⟩ : Fin 27) = ⟨11 + x, by omega⟩ := by
      ext; dsimp; omega
    simp [g, hx8, show 3 + (8 + x) < 27 by omega, heq]
  have h31 : ∑ i ∈ Finset.range 8, g (3 + (8 + (8 + i))) =
      ∑ i : Fin 8, f ⟨19 + i.val, by omega⟩ := by
    rw [Finset.sum_fin_eq_sum_range (fun i : Fin 8 => f ⟨19 + i.val, by omega⟩)]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx8 : x < 8 := Finset.mem_range.mp hx
    have heq : (⟨3 + (8 + (8 + x)), by omega⟩ : Fin 27) = ⟨19 + x, by omega⟩ := by
      ext; dsimp; omega
    simp [g, hx8, show 3 + (8 + (8 + x)) < 27 by omega, heq]
  rw [hg_main, h27, h3, h12, h23, h31]

private theorem compactOctonion_basisVec_norm_one (i : Fin 8) :
    CompactOctonion.norm (CompactOctonion.basisVec i) = 1 := by
  fin_cases i <;> simp [CompactOctonion.norm, CompactOctonion.basisVec]

private theorem compactOctonion_sum_trace_mul_conj_sq (u : CompactOctonion ℝ) :
    ∑ i : Fin 8,
      (CompactOctonion.trace (CompactOctonion.mul u
        (CompactOctonion.conj (CompactOctonion.basisVec i)))) ^ 2 =
      4 * CompactOctonion.norm u := by
  rw [Fin.sum_univ_eight]
  simp [CompactOctonion.trace, CompactOctonion.mul, CompactOctonion.conj,
    CompactOctonion.basisVec, CompactOctonion.norm]
  ring

private theorem basisVec_diag_0 : H3Octonion.basisVec 0 = diagCartan 1 0 0 := by
  simp [H3Octonion.basisVec]
private theorem basisVec_diag_1 : H3Octonion.basisVec 1 = diagCartan 0 1 0 := by
  simp [H3Octonion.basisVec]
private theorem basisVec_diag_2 : H3Octonion.basisVec 2 = diagCartan 0 0 1 := by
  simp [H3Octonion.basisVec]

private theorem basisVec_off12 (i : Fin 8) :
    H3Octonion.basisVec ⟨3 + i.val, by omega⟩ = embedJ12 (CompactOctonion.basisVec i) := by
  have hi : 3 + i.val ≠ 1 ∧ 3 + i.val ≠ 2 ∧ 3 + i.val < 11 := by omega
  simp [H3Octonion.basisVec, hi.1, hi.2.1, hi.2.2]

private theorem basisVec_off23 (i : Fin 8) :
    H3Octonion.basisVec ⟨11 + i.val, by omega⟩ =
      H3Octonion.embedJ23 (CompactOctonion.basisVec i) := by
  have hi : 11 + i.val ≠ 1 ∧ 11 + i.val ≠ 2 ∧
      ¬(11 + i.val < 11) ∧ 11 + i.val < 19 := by omega
  simp [H3Octonion.basisVec, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]

private theorem basisVec_off31 (i : Fin 8) :
    H3Octonion.basisVec ⟨19 + i.val, by omega⟩ =
      H3Octonion.embedJ31 (CompactOctonion.basisVec i) := by
  have hi : 19 + i.val ≠ 1 ∧ 19 + i.val ≠ 2 ∧
      ¬(19 + i.val < 11) ∧ ¬(19 + i.val < 19) := by omega
  simp [H3Octonion.basisVec, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]

private theorem mul_diag1_eval (a : H3Octonion ℝ) :
    a * diagCartan 1 0 0 = ⟨a.α₁, 0, 0, (1 / 2 : ℝ) • a.a, 0, (1 / 2 : ℝ) • a.c⟩ := by
  rw [mul_comm, mul_trace_formula]
  have hlt : linearTrace (diagCartan (1 : ℝ) 0 0) = 1 := by simp [linearTrace, diagCartan]
  have hcr : H3Octonion.crossProduct (diagCartan (1 : ℝ) 0 0) a =
      ⟨0, a.α₃, a.α₂, 0, -a.b, 0⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, diagCartan]
  rw [hlt, hcr]
  apply ext_h3 <;> (simp [diagCartan, linearTrace]; try ring)

private theorem mul_diag2_eval (a : H3Octonion ℝ) :
    a * diagCartan 0 1 0 = ⟨0, a.α₂, 0, (1 / 2 : ℝ) • a.a, (1 / 2 : ℝ) • a.b, 0⟩ := by
  rw [mul_comm, mul_trace_formula]
  have hlt : linearTrace (diagCartan (0 : ℝ) 1 0) = 1 := by simp [linearTrace, diagCartan]
  have hcr : H3Octonion.crossProduct (diagCartan (0 : ℝ) 1 0) a =
      ⟨a.α₃, 0, a.α₁, 0, 0, -a.c⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, diagCartan]
  rw [hlt, hcr]
  apply ext_h3 <;> (simp [diagCartan, linearTrace]; try ring)

private theorem mul_diag3_eval (a : H3Octonion ℝ) :
    a * diagCartan 0 0 1 = ⟨0, 0, a.α₃, 0, (1 / 2 : ℝ) • a.b, (1 / 2 : ℝ) • a.c⟩ := by
  rw [mul_comm, mul_trace_formula]
  have hlt : linearTrace (diagCartan (0 : ℝ) 0 1) = 1 := by simp [linearTrace, diagCartan]
  have hcr : H3Octonion.crossProduct (diagCartan (0 : ℝ) 0 1) a =
      ⟨a.α₂, a.α₁, 0, -a.a, 0, 0⟩ := by
    apply ext_h3 <;> (try apply CompactOctonion.ext) <;>
      simp [H3Octonion.crossProduct, diagCartan]
  rw [hlt, hcr]
  apply ext_h3 <;> (simp [diagCartan, linearTrace]; try ring)

private theorem mul_embedJ12_eval (a : H3Octonion ℝ) (u : CompactOctonion ℝ) :
    a * embedJ12 u =
      ⟨(1 / 2 : ℝ) * CompactOctonion.trace (CompactOctonion.mul a.a (CompactOctonion.conj u)),
       (1 / 2 : ℝ) * CompactOctonion.trace (CompactOctonion.mul a.a (CompactOctonion.conj u)),
       0,
       ((1 / 2 : ℝ) * (a.α₁ + a.α₂)) • u,
       (1 / 2 : ℝ) • CompactOctonion.mul (CompactOctonion.conj u) (CompactOctonion.conj a.c),
       (1 / 2 : ℝ) • CompactOctonion.mul (CompactOctonion.conj a.b) (CompactOctonion.conj u)⟩ := by
  rw [mul_trace_formula]
  have hlt : linearTrace (embedJ12 u) = 0 := by simp [linearTrace, embedJ12]
  have hcr : H3Octonion.crossProduct a (embedJ12 u) =
      ⟨0, 0, -CompactOctonion.trace (CompactOctonion.mul a.a (CompactOctonion.conj u)),
       -(a.α₃ • u),
       CompactOctonion.mul (CompactOctonion.conj u) (CompactOctonion.conj a.c),
       CompactOctonion.mul (CompactOctonion.conj a.b) (CompactOctonion.conj u)⟩ := by
    apply ext_h3 <;> simp [H3Octonion.crossProduct, embedJ12]
  have hltcr : linearTrace (H3Octonion.crossProduct a (embedJ12 u)) =
      -CompactOctonion.trace (CompactOctonion.mul a.a (CompactOctonion.conj u)) := by
    rw [hcr]; simp [linearTrace]
  rw [hlt, hltcr, hcr]
  apply ext_h3
  · simp [embedJ12]
  · simp [embedJ12]
  · simp [embedJ12]
  · simp [embedJ12]; dsimp [H3Octonion.linearTrace]; module
  · simp [embedJ12]
  · simp [embedJ12]

private theorem mul_embedJ23_eval (a : H3Octonion ℝ) (u : CompactOctonion ℝ) :
    a * H3Octonion.embedJ23 u =
      ⟨0,
       (1 / 2 : ℝ) * CompactOctonion.trace (CompactOctonion.mul a.b (CompactOctonion.conj u)),
       (1 / 2 : ℝ) * CompactOctonion.trace (CompactOctonion.mul a.b (CompactOctonion.conj u)),
       (1 / 2 : ℝ) • CompactOctonion.mul (CompactOctonion.conj a.c) (CompactOctonion.conj u),
       ((1 / 2 : ℝ) * (a.α₂ + a.α₃)) • u,
       (1 / 2 : ℝ) • CompactOctonion.mul (CompactOctonion.conj u) (CompactOctonion.conj a.a)⟩ := by
  rw [mul_trace_formula]
  have hlt : linearTrace (H3Octonion.embedJ23 u) = 0 := by simp [linearTrace, H3Octonion.embedJ23]
  have hcr : H3Octonion.crossProduct a (H3Octonion.embedJ23 u) =
      ⟨-CompactOctonion.trace (CompactOctonion.mul a.b (CompactOctonion.conj u)), 0, 0,
       CompactOctonion.mul (CompactOctonion.conj a.c) (CompactOctonion.conj u),
       -(a.α₁ • u),
       CompactOctonion.mul (CompactOctonion.conj u) (CompactOctonion.conj a.a)⟩ := by
    apply ext_h3 <;> simp [H3Octonion.crossProduct, H3Octonion.embedJ23]
  have hltcr : linearTrace (H3Octonion.crossProduct a (H3Octonion.embedJ23 u)) =
      -CompactOctonion.trace (CompactOctonion.mul a.b (CompactOctonion.conj u)) := by
    rw [hcr]; simp [linearTrace]
  rw [hlt, hltcr, hcr]
  apply ext_h3
  · simp [H3Octonion.embedJ23]
  · simp [H3Octonion.embedJ23]
  · simp [H3Octonion.embedJ23]
  · simp [H3Octonion.embedJ23]
  · simp [H3Octonion.embedJ23]; dsimp [H3Octonion.linearTrace]; module
  · simp [H3Octonion.embedJ23]

private theorem mul_embedJ31_eval (a : H3Octonion ℝ) (u : CompactOctonion ℝ) :
    a * H3Octonion.embedJ31 u =
      ⟨(1 / 2 : ℝ) * CompactOctonion.trace (CompactOctonion.mul a.c (CompactOctonion.conj u)),
       0,
       (1 / 2 : ℝ) * CompactOctonion.trace (CompactOctonion.mul a.c (CompactOctonion.conj u)),
       (1 / 2 : ℝ) • CompactOctonion.mul (CompactOctonion.conj u) (CompactOctonion.conj a.b),
       (1 / 2 : ℝ) • CompactOctonion.mul (CompactOctonion.conj a.a) (CompactOctonion.conj u),
       ((1 / 2 : ℝ) * (a.α₃ + a.α₁)) • u⟩ := by
  rw [mul_trace_formula]
  have hlt : linearTrace (H3Octonion.embedJ31 u) = 0 := by simp [linearTrace, H3Octonion.embedJ31]
  have hcr : H3Octonion.crossProduct a (H3Octonion.embedJ31 u) =
      ⟨0, -CompactOctonion.trace (CompactOctonion.mul a.c (CompactOctonion.conj u)), 0,
       CompactOctonion.mul (CompactOctonion.conj u) (CompactOctonion.conj a.b),
       CompactOctonion.mul (CompactOctonion.conj a.a) (CompactOctonion.conj u),
       -(a.α₂ • u)⟩ := by
    apply ext_h3 <;> simp [H3Octonion.crossProduct, H3Octonion.embedJ31]
  have hltcr : linearTrace (H3Octonion.crossProduct a (H3Octonion.embedJ31 u)) =
      -CompactOctonion.trace (CompactOctonion.mul a.c (CompactOctonion.conj u)) := by
    rw [hcr]; simp [linearTrace]
  rw [hlt, hltcr, hcr]
  apply ext_h3
  · simp [H3Octonion.embedJ31]
  · simp [H3Octonion.embedJ31]
  · simp [H3Octonion.embedJ31]
  · simp [H3Octonion.embedJ31]
  · simp [H3Octonion.embedJ31]
  · simp [H3Octonion.embedJ31]; dsimp [H3Octonion.linearTrace]; module

private def octDualWeightLocal (k : Fin 27) : ℝ :=
  if k.val < 3 then 1 else 1 / 2

private def octDualVecLocal (k : Fin 27) : H3Octonion ℝ :=
  if k.val < 3 then H3Octonion.basisVec k else (1 / 2 : ℝ) • H3Octonion.basisVec k

private theorem h3OctonionBasis_repr_eq_coord (y : H3Octonion ℝ) (k : Fin 27) :
    h3OctonionBasis.repr y k = H3Octonion.coordFun y k := rfl

private theorem compactOctonion_trace_basisVec_mul (i : Fin 8) (u : CompactOctonion ℝ) :
    CompactOctonion.trace
        (CompactOctonion.mul (CompactOctonion.basisVec i) (CompactOctonion.conj u)) =
      2 * CompactOctonion.coordFun u i := by
  fin_cases i <;>
    simp [CompactOctonion.trace, CompactOctonion.mul, CompactOctonion.conj,
      CompactOctonion.basisVec, CompactOctonion.coordFun] <;> ring

private theorem traceBilin_embedJ12 (u : CompactOctonion ℝ) (y : H3Octonion ℝ) :
    traceBilin (embedJ12 u) y =
      CompactOctonion.trace (CompactOctonion.mul u (CompactOctonion.conj y.a)) := by
  simp [traceBilin, embedJ12]

private theorem traceBilin_embedJ23 (u : CompactOctonion ℝ) (y : H3Octonion ℝ) :
    traceBilin (H3Octonion.embedJ23 u) y =
      CompactOctonion.trace (CompactOctonion.mul u (CompactOctonion.conj y.b)) := by
  simp [traceBilin, H3Octonion.embedJ23]

private theorem traceBilin_embedJ31 (u : CompactOctonion ℝ) (y : H3Octonion ℝ) :
    traceBilin (H3Octonion.embedJ31 u) y =
      CompactOctonion.trace (CompactOctonion.mul u (CompactOctonion.conj y.c)) := by
  simp [traceBilin, H3Octonion.embedJ31]

private theorem trace_eq_sum_coord_jordanLmul_sq (a : H3Octonion ℝ) :
    LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) =
      ∑ k : Fin 27, octDualWeightLocal k *
        traceBilin (a * H3Octonion.basisVec k) (a * H3Octonion.basisVec k) := by
  have hcoord : ∀ y : H3Octonion ℝ, ∀ k : Fin 27,
      h3OctonionBasis.repr y k = traceBilin (octDualVecLocal k) y := by
    intro y k
    rw [h3OctonionBasis_repr_eq_coord]
    dsimp [octDualVecLocal, H3Octonion.coordFun]
    by_cases hk0 : k.val = 0
    · have hk : k = 0 := Fin.ext hk0
      subst hk; simp [basisVec_diag_0, traceBilin, diagCartan]
    · by_cases hk1 : k.val = 1
      · have hk : k = 1 := Fin.ext hk1
        subst hk; simp [basisVec_diag_1, traceBilin, diagCartan]
      · by_cases hk2 : k.val = 2
        · have hk : k = 2 := Fin.ext hk2
          subst hk; simp [basisVec_diag_2, traceBilin, diagCartan]
        · have hk3 : ¬k.val < 3 := by omega
          by_cases hk11 : k.val < 11
          · have hbv : H3Octonion.basisVec k =
                embedJ12 (CompactOctonion.basisVec ⟨k.val - 3, by omega⟩) := by
              simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11]
            simp only [hk0, hk1, hk2, hk3, ↓reduceIte]
            have hL : (if h : k.val < 11 then y.a.coordFun ⟨k.val - 3, by omega⟩
                else if h23 : k.val < 19 then y.b.coordFun ⟨k.val - 11, by omega⟩
                else y.c.coordFun ⟨k.val - 19, by omega⟩) =
                y.a.coordFun ⟨k.val - 3, by omega⟩ := by
              split_ifs; rfl
            rw [hL, hbv, traceBilin_smul_left, traceBilin_embedJ12,
              compactOctonion_trace_basisVec_mul]
            ring
          · by_cases hk19 : k.val < 19
            · have hbv : H3Octonion.basisVec k =
                  H3Octonion.embedJ23 (CompactOctonion.basisVec ⟨k.val - 11, by omega⟩) := by
                simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11, hk19]
              simp only [hk0, hk1, hk2, hk3, ↓reduceIte]
              have hL : (if h : k.val < 11 then y.a.coordFun ⟨k.val - 3, by omega⟩
                  else if h23 : k.val < 19 then y.b.coordFun ⟨k.val - 11, by omega⟩
                  else y.c.coordFun ⟨k.val - 19, by omega⟩) =
                  y.b.coordFun ⟨k.val - 11, by omega⟩ := by
                split_ifs; rfl
              rw [hL, hbv, traceBilin_smul_left, traceBilin_embedJ23,
                compactOctonion_trace_basisVec_mul]
              ring
            · have hbv : H3Octonion.basisVec k =
                  H3Octonion.embedJ31 (CompactOctonion.basisVec ⟨k.val - 19, by omega⟩) := by
                simp [H3Octonion.basisVec, hk0, hk1, hk2, hk11, hk19]
              simp only [hk0, hk1, hk2, hk3, ↓reduceIte]
              have hL : (if h : k.val < 11 then y.a.coordFun ⟨k.val - 3, by omega⟩
                  else if h23 : k.val < 19 then y.b.coordFun ⟨k.val - 11, by omega⟩
                  else y.c.coordFun ⟨k.val - 19, by omega⟩) =
                  y.c.coordFun ⟨k.val - 19, by omega⟩ := by
                split_ifs; rfl
              rw [hL, hbv, traceBilin_smul_left, traceBilin_embedJ31,
                compactOctonion_trace_basisVec_mul]
              ring
  rw [LinearMap.trace_eq_matrix_trace ℝ h3OctonionBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, h3OctonionBasis_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hcoord]
  change traceBilin (octDualVecLocal k) (a * (a * H3Octonion.basisVec k)) = _
  have hwt : traceBilin (octDualVecLocal k) (a * (a * H3Octonion.basisVec k)) =
      octDualWeightLocal k *
        traceBilin (H3Octonion.basisVec k) (a * (a * H3Octonion.basisVec k)) := by
    dsimp [octDualVecLocal, octDualWeightLocal]
    split_ifs
    · rw [one_mul]
    · rw [traceBilin_smul_left]
  rw [hwt, ← h3Octonion_traceBilin_jordanLmul_assoc]

/-- Exact trace-square identity for Jordan left multiplication on `H3Octonion ℝ`:
`Tr(L_a²) = 3 ⟨a, a⟩ + 2 (tr a)²`. -/
theorem h3Octonion_jordanLmul_trace_sq (a : H3Octonion ℝ) :
    LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) a) =
      3 * traceBilin a a + 2 * (linearTrace a) ^ 2 := by
  rw [trace_eq_sum_coord_jordanLmul_sq, sum_fin27_split]
  have h0 : octDualWeightLocal 0 *
      traceBilin (a * H3Octonion.basisVec 0) (a * H3Octonion.basisVec 0) =
      a.α₁ * a.α₁ + (1 / 2 : ℝ) * CompactOctonion.norm a.a +
        (1 / 2 : ℝ) * CompactOctonion.norm a.c := by
    rw [basisVec_diag_0, mul_diag1_eval, traceBilin_self_eq]
    simp [octDualWeightLocal, CompactOctonion.norm_smul]
    ring
  have h1 : octDualWeightLocal 1 *
      traceBilin (a * H3Octonion.basisVec 1) (a * H3Octonion.basisVec 1) =
      a.α₂ * a.α₂ + (1 / 2 : ℝ) * CompactOctonion.norm a.a +
        (1 / 2 : ℝ) * CompactOctonion.norm a.b := by
    rw [basisVec_diag_1, mul_diag2_eval, traceBilin_self_eq]
    simp [octDualWeightLocal, CompactOctonion.norm_smul]
    ring
  have h2 : octDualWeightLocal 2 *
      traceBilin (a * H3Octonion.basisVec 2) (a * H3Octonion.basisVec 2) =
      a.α₃ * a.α₃ + (1 / 2 : ℝ) * CompactOctonion.norm a.b +
        (1 / 2 : ℝ) * CompactOctonion.norm a.c := by
    rw [basisVec_diag_2, mul_diag3_eval, traceBilin_self_eq]
    simp [octDualWeightLocal, CompactOctonion.norm_smul]
    ring
  have hs12 : (∑ i : Fin 8, octDualWeightLocal ⟨3 + i.val, by omega⟩ *
      traceBilin (a * H3Octonion.basisVec ⟨3 + i.val, by omega⟩)
        (a * H3Octonion.basisVec ⟨3 + i.val, by omega⟩)) =
      CompactOctonion.norm a.a + 2 * (a.α₁ + a.α₂) ^ 2 +
        2 * CompactOctonion.norm a.c + 2 * CompactOctonion.norm a.b := by
    have hterm : ∀ i : Fin 8,
        octDualWeightLocal ⟨3 + i.val, by omega⟩ *
          traceBilin (a * H3Octonion.basisVec ⟨3 + i.val, by omega⟩)
            (a * H3Octonion.basisVec ⟨3 + i.val, by omega⟩) =
        (1 / 4 : ℝ) * (CompactOctonion.trace
          (CompactOctonion.mul a.a (CompactOctonion.conj (CompactOctonion.basisVec i)))) ^ 2 +
        (1 / 4 : ℝ) * (a.α₁ + a.α₂) ^ 2 +
        (1 / 4 : ℝ) * CompactOctonion.norm a.c +
        (1 / 4 : ℝ) * CompactOctonion.norm a.b := by
      intro i
      rw [basisVec_off12, mul_embedJ12_eval, traceBilin_self_eq]
      have hwt : octDualWeightLocal ⟨3 + i.val, by omega⟩ = 1 / 2 := by
        simp [octDualWeightLocal]
      rw [hwt]
      simp only [CompactOctonion.norm_smul, CompactOctonion.norm_mul, CompactOctonion.norm_conj,
        compactOctonion_basisVec_norm_one, mul_one, one_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      compactOctonion_sum_trace_mul_conj_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hs23 : (∑ i : Fin 8, octDualWeightLocal ⟨11 + i.val, by omega⟩ *
      traceBilin (a * H3Octonion.basisVec ⟨11 + i.val, by omega⟩)
        (a * H3Octonion.basisVec ⟨11 + i.val, by omega⟩)) =
      CompactOctonion.norm a.b + 2 * (a.α₂ + a.α₃) ^ 2 +
        2 * CompactOctonion.norm a.c + 2 * CompactOctonion.norm a.a := by
    have hterm : ∀ i : Fin 8,
        octDualWeightLocal ⟨11 + i.val, by omega⟩ *
          traceBilin (a * H3Octonion.basisVec ⟨11 + i.val, by omega⟩)
            (a * H3Octonion.basisVec ⟨11 + i.val, by omega⟩) =
        (1 / 4 : ℝ) * (CompactOctonion.trace
          (CompactOctonion.mul a.b (CompactOctonion.conj (CompactOctonion.basisVec i)))) ^ 2 +
        (1 / 4 : ℝ) * (a.α₂ + a.α₃) ^ 2 +
        (1 / 4 : ℝ) * CompactOctonion.norm a.c +
        (1 / 4 : ℝ) * CompactOctonion.norm a.a := by
      intro i
      rw [basisVec_off23, mul_embedJ23_eval, traceBilin_self_eq]
      have hwt : octDualWeightLocal ⟨11 + i.val, by omega⟩ = 1 / 2 := by
        dsimp [octDualWeightLocal]
        split_ifs with h
        · omega
        · rfl
      rw [hwt]
      simp only [CompactOctonion.norm_smul, CompactOctonion.norm_mul, CompactOctonion.norm_conj,
        compactOctonion_basisVec_norm_one, mul_one, one_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      compactOctonion_sum_trace_mul_conj_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hs31 : (∑ i : Fin 8, octDualWeightLocal ⟨19 + i.val, by omega⟩ *
      traceBilin (a * H3Octonion.basisVec ⟨19 + i.val, by omega⟩)
        (a * H3Octonion.basisVec ⟨19 + i.val, by omega⟩)) =
      CompactOctonion.norm a.c + 2 * (a.α₃ + a.α₁) ^ 2 +
        2 * CompactOctonion.norm a.b + 2 * CompactOctonion.norm a.a := by
    have hterm : ∀ i : Fin 8,
        octDualWeightLocal ⟨19 + i.val, by omega⟩ *
          traceBilin (a * H3Octonion.basisVec ⟨19 + i.val, by omega⟩)
            (a * H3Octonion.basisVec ⟨19 + i.val, by omega⟩) =
        (1 / 4 : ℝ) * (CompactOctonion.trace
          (CompactOctonion.mul a.c (CompactOctonion.conj (CompactOctonion.basisVec i)))) ^ 2 +
        (1 / 4 : ℝ) * (a.α₃ + a.α₁) ^ 2 +
        (1 / 4 : ℝ) * CompactOctonion.norm a.b +
        (1 / 4 : ℝ) * CompactOctonion.norm a.a := by
      intro i
      rw [basisVec_off31, mul_embedJ31_eval, traceBilin_self_eq]
      have hwt : octDualWeightLocal ⟨19 + i.val, by omega⟩ = 1 / 2 := by
        dsimp [octDualWeightLocal]
        split_ifs with h
        · omega
        · rfl
      rw [hwt]
      simp only [CompactOctonion.norm_smul, CompactOctonion.norm_mul, CompactOctonion.norm_conj,
        compactOctonion_basisVec_norm_one, mul_one, one_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      compactOctonion_sum_trace_mul_conj_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [h0, h1, h2, hs12, hs23, hs31, traceBilin_self_eq, linearTrace]
  ring

theorem h3Octonion_jordanLmul_trace_mul (a b : H3Octonion ℝ) :
    LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) b) =
      3 * traceBilin a b + 2 * linearTrace a * linearTrace b := by
  have hab := h3Octonion_jordanLmul_trace_sq (a + b)
  have ha := h3Octonion_jordanLmul_trace_sq a
  have hb := h3Octonion_jordanLmul_trace_sq b
  have hadd : jordanLmul (R := ℝ) (a + b) = jordanLmul (R := ℝ) a + jordanLmul (R := ℝ) b := by
    apply LinearMap.ext; intro x; simp [jordanLmul_apply, add_mul]
  have htr_comm : LinearMap.trace ℝ (H3Octonion ℝ)
      (jordanLmul (R := ℝ) b * jordanLmul (R := ℝ) a) =
      LinearMap.trace ℝ (H3Octonion ℝ) (jordanLmul (R := ℝ) a * jordanLmul (R := ℝ) b) :=
    LinearMap.trace_mul_comm (R := ℝ) (M := H3Octonion ℝ)
      (jordanLmul (R := ℝ) b) (jordanLmul (R := ℝ) a)
  rw [hadd, add_mul, mul_add, mul_add, map_add, map_add, map_add, htr_comm, ha, hb,
    traceBilin_add_left, traceBilin_add_right, traceBilin_add_right,
    traceBilin_symm b a, linearTrace_add] at hab
  linarith

theorem h3Octonion_deriv_innerDeriv_trace (D : H3OctonionF4Derivations)
    (u v : H3Octonion ℝ) :
    LinearMap.trace ℝ (H3Octonion ℝ)
        (D.1 * (h3OctonionJordanInnerDerivation u v : EndH3O)) =
      3 * traceBilin (D.1 u) v := by
  have hinner : (h3OctonionJordanInnerDerivation u v : EndH3O) =
      jordanLmul (R := ℝ) u * jordanLmul (R := ℝ) v -
        jordanLmul (R := ℝ) v * jordanLmul (R := ℝ) u := by
    apply LinearMap.ext; intro z; rfl
  have hDL : D.1 * jordanLmul (R := ℝ) u - jordanLmul (R := ℝ) u * D.1 =
      jordanLmul (R := ℝ) (D.1 u) := by
    apply LinearMap.ext; intro z
    change D.1 (u * z) - u * D.1 z = D.1 u * z
    rw [D.2 u z]; abel
  have hcyc : LinearMap.trace ℝ (H3Octonion ℝ)
      (D.1 * (jordanLmul (R := ℝ) v * jordanLmul (R := ℝ) u)) =
      LinearMap.trace ℝ (H3Octonion ℝ)
        (jordanLmul (R := ℝ) u * D.1 * jordanLmul (R := ℝ) v) := by
    rw [← mul_assoc, LinearMap.trace_mul_cycle, mul_assoc]
  rw [hinner, mul_sub, map_sub, hcyc, ← mul_assoc, ← map_sub, ← sub_mul, hDL,
    h3Octonion_jordanLmul_trace_mul, h3Octonion_derivation_linearTrace_zero D u]
  ring

/-- The `H3Octonion ℝ` part `T(1)` of `T ∈ h3OctonionTKKDatum.str`. -/
def strLmulPart : h3OctonionTKKDatum.str →ₗ[ℝ] H3Octonion ℝ where
  toFun T := T.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `H3OctonionF4Derivations` part `T - L_{T(1)}` of `T ∈ h3OctonionTKKDatum.str`. -/
def strDerivPart (T : h3OctonionTKKDatum.str) : H3OctonionF4Derivations :=
  (h3OctonionStructureDirectSumEquiv.symm ⟨T.1, T.2⟩).1

theorem strDerivPart_coe (T : h3OctonionTKKDatum.str) :
    (strDerivPart T : EndH3O) = T.1 - jordanLmul (R := ℝ) (strLmulPart T) := by
  have hsurj := h3OctonionStructureDirectSumEquiv.apply_symm_apply ⟨T.1, T.2⟩
  have heq : T.1 = (strDerivPart T).1 + jordanLmul (R := ℝ)
      (h3OctonionStructureDirectSumEquiv.symm ⟨T.1, T.2⟩).2 :=
    (congrArg Subtype.val hsurj).symm
  have h1 := LinearMap.ext_iff.mp heq (1 : H3Octonion ℝ)
  have hb : (h3OctonionStructureDirectSumEquiv.symm ⟨T.1, T.2⟩).2 = strLmulPart T := by
    change T.1 1 = (strDerivPart T).1 1 + _ * 1 at h1
    rw [h3Octonion_derivation_apply_one_eq_zero, zero_add, h3Octonion_mul_one] at h1
    exact h1.symm
  rw [hb] at heq
  exact eq_sub_of_add_eq heq.symm

@[simp] theorem strDerivPart_add (T₁ T₂ : h3OctonionTKKDatum.str) :
    strDerivPart (T₁ + T₂) = strDerivPart T₁ + strDerivPart T₂ := by
  apply Subtype.ext
  change (strDerivPart (T₁ + T₂) : EndH3O) = (strDerivPart T₁ : EndH3O) + (strDerivPart T₂ : EndH3O)
  rw [strDerivPart_coe, strDerivPart_coe, strDerivPart_coe]
  apply LinearMap.ext; intro z
  simp [jordanLmul_apply, add_mul]
  abel

@[simp] theorem strDerivPart_smul (r : ℝ) (T : h3OctonionTKKDatum.str) :
    strDerivPart (r • T) = r • strDerivPart T := by
  apply Subtype.ext
  change (strDerivPart (r • T) : EndH3O) = r • (strDerivPart T : EndH3O)
  rw [strDerivPart_coe, strDerivPart_coe]
  apply LinearMap.ext; intro z
  simp [jordanLmul_apply, smul_mul_assoc]
  module

private theorem strLmulPart_derivation (D : H3OctonionF4Derivations)
    (hD : D.1 ∈ h3OctonionTKKDatum.str) :
    strLmulPart ⟨D.1, hD⟩ = 0 :=
  h3Octonion_derivation_apply_one_eq_zero D

private theorem strDerivPart_derivation (D : H3OctonionF4Derivations)
    (hD : D.1 ∈ h3OctonionTKKDatum.str) :
    strDerivPart ⟨D.1, hD⟩ = D := by
  apply Subtype.ext
  rw [strDerivPart_coe, strLmulPart_derivation D hD]
  apply LinearMap.ext; intro z; simp [jordanLmul_apply]

private theorem strLmulPart_jordanLmul (a : H3Octonion ℝ)
    (ha : jordanLmul (R := ℝ) a ∈ h3OctonionTKKDatum.str) :
    strLmulPart ⟨jordanLmul (R := ℝ) a, ha⟩ = a := by
  change a * (1 : H3Octonion ℝ) = a
  exact h3Octonion_mul_one a

private theorem strDerivPart_jordanLmul (a : H3Octonion ℝ)
    (ha : jordanLmul (R := ℝ) a ∈ h3OctonionTKKDatum.str) :
    strDerivPart ⟨jordanLmul (R := ℝ) a, ha⟩ = 0 := by
  apply Subtype.ext
  rw [strDerivPart_coe, strLmulPart_jordanLmul a ha, sub_self]
  rfl

private theorem strLmulPart_neg_adj (T : h3OctonionTKKDatum.str) :
    strLmulPart ⟨-h3OctonionTraceAdjoint T.1, neg_adj_mem_str T⟩ =
      -strLmulPart T := by
  have heq : T.1 = (strDerivPart T).1 + jordanLmul (R := ℝ) (strLmulPart T) := by
    rw [strDerivPart_coe]; abel
  have hadj : h3OctonionTraceAdjoint T.1 =
      -(strDerivPart T).1 + jordanLmul (R := ℝ) (strLmulPart T) := by
    rw [heq, ← h3OctonionTraceAdjointLM_apply, map_add, h3OctonionTraceAdjointLM_apply,
      h3OctonionTraceAdjointLM_apply,
      h3OctonionTraceAdjoint_derivation ⟨(strDerivPart T).1, (strDerivPart T).2⟩,
      h3OctonionTraceAdjoint_jordanLmul]
  change -(h3OctonionTraceAdjoint T.1 1) = -(T.1 1)
  rw [hadj]
  simp only [LinearMap.add_apply, LinearMap.neg_apply,
    h3Octonion_derivation_apply_one_eq_zero, neg_zero, zero_add, jordanLmul_apply,
    h3Octonion_mul_one]
  exact (LinearMap.ext_iff.mp heq (1 : H3Octonion ℝ) ▸
    by simp [h3Octonion_derivation_apply_one_eq_zero, jordanLmul_apply, h3Octonion_mul_one])

private theorem strDerivPart_neg_adj (T : h3OctonionTKKDatum.str) :
    strDerivPart ⟨-h3OctonionTraceAdjoint T.1, neg_adj_mem_str T⟩ =
      strDerivPart T := by
  apply Subtype.ext
  have hL := strLmulPart_neg_adj T
  rw [strDerivPart_coe]
  change -h3OctonionTraceAdjoint T.1 -
      jordanLmul (R := ℝ) (strLmulPart ⟨-h3OctonionTraceAdjoint T.1, neg_adj_mem_str T⟩) =
    (strDerivPart T).1
  rw [hL]
  have heq : T.1 = (strDerivPart T).1 + jordanLmul (R := ℝ) (strLmulPart T) := by
    rw [strDerivPart_coe]; abel
  have hadj : h3OctonionTraceAdjoint T.1 =
      -(strDerivPart T).1 + jordanLmul (R := ℝ) (strLmulPart T) := by
    rw [heq, ← h3OctonionTraceAdjointLM_apply, map_add, h3OctonionTraceAdjointLM_apply,
      h3OctonionTraceAdjointLM_apply,
      h3OctonionTraceAdjoint_derivation ⟨(strDerivPart T).1, (strDerivPart T).2⟩,
      h3OctonionTraceAdjoint_jordanLmul]
  rw [hadj]
  apply LinearMap.ext; intro z
  simp [jordanLmul_apply, neg_mul]

private def tkkInvRaw (X Y : H3OctonionTKKLie) : ℝ :=
  LinearMap.trace ℝ (H3Octonion ℝ) ((strDerivPart X.zero).1 * (strDerivPart Y.zero).1) +
    3 * traceBilin (strLmulPart X.zero) (strLmulPart Y.zero) +
    3 * (traceBilin X.neg Y.pos + traceBilin X.pos Y.neg)

private def tkkInvariantBilinRight (X : H3OctonionTKKLie) : H3OctonionTKKLie →ₗ[ℝ] ℝ where
  toFun Y := tkkInvRaw X Y
  map_add' Y₁ Y₂ := by
    dsimp [tkkInvRaw]
    have hD : (strDerivPart (Y₁.zero + Y₂.zero)).1 =
        (strDerivPart Y₁.zero).1 + (strDerivPart Y₂.zero).1 := by
      rw [strDerivPart_add]; rfl
    change LinearMap.trace ℝ (H3Octonion ℝ)
        ((strDerivPart X.zero).1 * (strDerivPart (Y₁.zero + Y₂.zero)).1) +
        3 * traceBilin (strLmulPart X.zero) (strLmulPart (Y₁.zero + Y₂.zero)) +
        3 * (traceBilin X.neg (Y₁.pos + Y₂.pos) + traceBilin X.pos (Y₁.neg + Y₂.neg)) = _
    rw [hD, mul_add, map_add, map_add, traceBilin_add_right, traceBilin_add_right,
      traceBilin_add_right]
    ring
  map_smul' r Y := by
    dsimp [tkkInvRaw]
    have hD : (strDerivPart (r • Y.zero)).1 = r • (strDerivPart Y.zero).1 := by
      rw [strDerivPart_smul]; rfl
    change LinearMap.trace ℝ (H3Octonion ℝ)
        ((strDerivPart X.zero).1 * (strDerivPart (r • Y.zero)).1) +
        3 * traceBilin (strLmulPart X.zero) (strLmulPart (r • Y.zero)) +
        3 * (traceBilin X.neg (r • Y.pos) + traceBilin X.pos (r • Y.neg)) = _
    rw [hD, mul_smul_comm, map_smul, map_smul, traceBilin_smul_right, traceBilin_smul_right,
      traceBilin_smul_right, smul_eq_mul]
    ring

private theorem tkkInvariantBilinRight_apply (X Y : H3OctonionTKKLie) :
    tkkInvariantBilinRight X Y = tkkInvRaw X Y := rfl

/-- The `ad`-invariant and `θ`-invariant symmetric bilinear form on `H3OctonionTKKLie`:
`B(X, Y) = Tr_{27}(D_X D_Y) + 3 ⟨a_X, a_Y⟩ + 3 (⟨x_X, y_Y⟩ + ⟨y_X, x_Y⟩)`. -/
def tkkInvariantBilin : LinearMap.BilinForm ℝ H3OctonionTKKLie where
  toFun := tkkInvariantBilinRight
  map_add' X₁ X₂ := by
    apply LinearMap.ext; intro Y
    change tkkInvariantBilinRight (X₁ + X₂) Y =
      tkkInvariantBilinRight X₁ Y + tkkInvariantBilinRight X₂ Y
    simp only [tkkInvariantBilinRight_apply, tkkInvRaw]
    have hD : (strDerivPart (X₁.zero + X₂.zero)).1 =
        (strDerivPart X₁.zero).1 + (strDerivPart X₂.zero).1 := by
      rw [strDerivPart_add]; rfl
    change LinearMap.trace ℝ (H3Octonion ℝ)
        ((strDerivPart (X₁.zero + X₂.zero)).1 * (strDerivPart Y.zero).1) +
        3 * traceBilin (strLmulPart (X₁.zero + X₂.zero)) (strLmulPart Y.zero) +
        3 * (traceBilin (X₁.neg + X₂.neg) Y.pos + traceBilin (X₁.pos + X₂.pos) Y.neg) = _
    rw [hD, add_mul, map_add, map_add, traceBilin_add_left, traceBilin_add_left,
      traceBilin_add_left]
    ring
  map_smul' r X := by
    apply LinearMap.ext; intro Y
    change tkkInvariantBilinRight (r • X) Y = r * tkkInvariantBilinRight X Y
    simp only [tkkInvariantBilinRight_apply, tkkInvRaw]
    have hD : (strDerivPart (r • X.zero)).1 = r • (strDerivPart X.zero).1 := by
      rw [strDerivPart_smul]; rfl
    change LinearMap.trace ℝ (H3Octonion ℝ)
        ((strDerivPart (r • X.zero)).1 * (strDerivPart Y.zero).1) +
        3 * traceBilin (strLmulPart (r • X.zero)) (strLmulPart Y.zero) +
        3 * (traceBilin (r • X.neg) Y.pos + traceBilin (r • X.pos) Y.neg) = _
    rw [hD, smul_mul_assoc, map_smul, map_smul, traceBilin_smul_left, traceBilin_smul_left,
      traceBilin_smul_left, smul_eq_mul]
    ring

theorem tkkInvariantBilin_apply (X Y : H3OctonionTKKLie) :
    tkkInvariantBilin X Y = tkkInvRaw X Y := rfl

theorem tkkInvariantBilin_symm (X Y : H3OctonionTKKLie) :
    tkkInvariantBilin X Y = tkkInvariantBilin Y X := by
  rw [tkkInvariantBilin_apply, tkkInvariantBilin_apply]
  dsimp [tkkInvRaw]
  rw [LinearMap.trace_mul_comm, traceBilin_symm (strLmulPart X.zero) (strLmulPart Y.zero),
    traceBilin_symm X.neg Y.pos, traceBilin_symm X.pos Y.neg]
  ring

theorem tkkInvariantBilin_isSymm : tkkInvariantBilin.IsSymm :=
  ⟨tkkInvariantBilin_symm⟩

theorem tkkInvariantBilin_cartanInvolution (X Y : H3OctonionTKKLie) :
    tkkInvariantBilin (h3OctonionCartanInvolution X) (h3OctonionCartanInvolution Y) =
      tkkInvariantBilin X Y := by
  rw [tkkInvariantBilin_apply, tkkInvariantBilin_apply]
  dsimp [tkkInvRaw]
  rw [strDerivPart_neg_adj X.zero, strDerivPart_neg_adj Y.zero,
    strLmulPart_neg_adj X.zero, strLmulPart_neg_adj Y.zero]
  simp only [traceBilin_neg_left, traceBilin_neg_right, neg_neg]
  ring

private theorem lie_F4_jordanLmul (D : H3OctonionF4Derivations) (a : H3Octonion ℝ) :
    D.1 ∘ₗ jordanLmul (R := ℝ) a - jordanLmul (R := ℝ) a ∘ₗ D.1 =
      jordanLmul (R := ℝ) (D.1 a) := by
  apply LinearMap.ext; intro z
  change D.1 (a * z) - a * D.1 z = D.1 a * z
  rw [D.2 a z]; abel

private theorem lie_jordanLmul_F4 (a : H3Octonion ℝ) (D : H3OctonionF4Derivations) :
    jordanLmul (R := ℝ) a ∘ₗ D.1 - D.1 ∘ₗ jordanLmul (R := ℝ) a =
      jordanLmul (R := ℝ) (-(D.1 a)) := by
  rw [← neg_sub, lie_F4_jordanLmul]
  apply LinearMap.ext; intro z; simp [jordanLmul_apply, neg_mul]

private theorem lie_jordanLmul_jordanLmul (a b : H3Octonion ℝ) :
    jordanLmul (R := ℝ) a ∘ₗ jordanLmul (R := ℝ) b -
      jordanLmul (R := ℝ) b ∘ₗ jordanLmul (R := ℝ) a =
      (h3OctonionJordanInnerDerivation a b : EndH3O) := rfl

private theorem tkkInvariantBilin_lieInvariant_F4 (D : H3OctonionF4Derivations)
    (X Y : H3OctonionTKKLie) :
    tkkInvariantBilin ⁅zeroInj ⟨D.1, deriv_mem_str D⟩, X⁆ Y +
      tkkInvariantBilin X ⁅zeroInj ⟨D.1, deriv_mem_str D⟩, Y⁆ = 0 := by
  let ZD : H3OctonionTKKLie := zeroInj ⟨D.1, deriv_mem_str D⟩
  have hcomm : ∀ W : H3OctonionTKKLie,
      D.1 ∘ₗ W.zero.1 - W.zero.1 ∘ₗ D.1 =
        (D.1 ∘ₗ (strDerivPart W.zero).1 - (strDerivPart W.zero).1 ∘ₗ D.1) +
          jordanLmul (R := ℝ) (D.1 (strLmulPart W.zero)) := by
    intro W
    have hW0 : W.zero.1 = (strDerivPart W.zero).1 + jordanLmul (R := ℝ) (strLmulPart W.zero) := by
      rw [strDerivPart_coe]; abel
    rw [hW0, LinearMap.comp_add, LinearMap.add_comp, ← lie_F4_jordanLmul D (strLmulPart W.zero)]
    abel
  have hcomm_mem : ∀ W : H3OctonionTKKLie,
      (D.1 ∘ₗ (strDerivPart W.zero).1 - (strDerivPart W.zero).1 ∘ₗ D.1) +
        jordanLmul (R := ℝ) (D.1 (strLmulPart W.zero)) ∈ h3OctonionTKKDatum.str := by
    intro W
    rw [← hcomm W]
    exact h3OctonionTKKDatum.str_lie_mem (deriv_mem_str D) W.zero.2
  have hbr : ∀ W : H3OctonionTKKLie,
      ⁅ZD, W⁆ = negInj (D.1 W.neg) +
        zeroInj ⟨D.1 ∘ₗ (strDerivPart W.zero).1 - (strDerivPart W.zero).1 ∘ₗ D.1 +
          jordanLmul (R := ℝ) (D.1 (strLmulPart W.zero)), hcomm_mem W⟩ +
        posInj (D.1 W.pos) := by
    intro W
    conv_lhs => rw [eq_neg_add_zero_add_pos W]
    simp only [ZD, lie_add, zeroInj_bracket_negInj, zeroInj_bracket_zeroInj,
      zeroInj_bracket_posInj]
    have hadj : -h3OctonionTraceAdjoint D.1 W.pos = D.1 W.pos := by
      have hd := congrArg (fun f : EndH3O => f W.pos)
        (h3OctonionTraceAdjoint_derivation ⟨D.1, D.2⟩)
      change h3OctonionTraceAdjoint D.1 W.pos = -D.1 W.pos at hd
      rw [hd, neg_neg]
    rw [hadj]
    apply JordanTKK.ext
    · simp [negInj, zeroInj, posInj]
    · apply Subtype.ext
      simp only [JordanTKK.add_zero_comp, negInj, zeroInj, posInj, JordanTKK.negLM_zero,
        JordanTKK.zeroLM_zero, JordanTKK.posLM_zero, zero_add, add_zero]
      exact hcomm W
    · simp [negInj, zeroInj, posInj]
  have hD_part : ∀ W : H3OctonionTKKLie,
      strDerivPart ⁅ZD, W⁆.zero = ⁅D, strDerivPart W.zero⁆ := by
    intro W
    have hb := congrArg JordanTKK.zero (hbr W)
    simp only [JordanTKK.add_zero_comp, negInj, zeroInj, posInj, JordanTKK.negLM_zero,
      JordanTKK.zeroLM_zero, JordanTKK.posLM_zero, zero_add, add_zero] at hb
    rw [hb]
    apply Subtype.ext
    rw [strDerivPart_coe]
    have hl1 : strLmulPart ⟨D.1 ∘ₗ (strDerivPart W.zero).1 -
        (strDerivPart W.zero).1 ∘ₗ D.1 + jordanLmul (R := ℝ) (D.1 (strLmulPart W.zero)),
        hcomm_mem W⟩ = D.1 (strLmulPart W.zero) := by
      change ((D.1 ∘ₗ (strDerivPart W.zero).1 - (strDerivPart W.zero).1 ∘ₗ D.1) +
          jordanLmul (R := ℝ) (D.1 (strLmulPart W.zero))) 1 = _
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        jordanLmul_apply, h3Octonion_derivation_apply_one_eq_zero, map_zero, sub_self,
        zero_add, h3Octonion_mul_one]
    rw [hl1]
    simp only [add_sub_cancel_right]
    rfl
  have ha_part : ∀ W : H3OctonionTKKLie,
      strLmulPart ⁅ZD, W⁆.zero = D.1 (strLmulPart W.zero) := by
    intro W
    have hb := congrArg JordanTKK.zero (hbr W)
    simp only [JordanTKK.add_zero_comp, negInj, zeroInj, posInj, JordanTKK.negLM_zero,
      JordanTKK.zeroLM_zero, JordanTKK.posLM_zero, zero_add, add_zero] at hb
    rw [hb]
    change ((D.1 ∘ₗ (strDerivPart W.zero).1 - (strDerivPart W.zero).1 ∘ₗ D.1) +
        jordanLmul (R := ℝ) (D.1 (strLmulPart W.zero))) 1 = _
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      jordanLmul_apply, h3Octonion_derivation_apply_one_eq_zero, map_zero, sub_self,
      zero_add, h3Octonion_mul_one]
  have hneg_part : ∀ W : H3OctonionTKKLie, ⁅ZD, W⁆.neg = D.1 W.neg := by
    intro W
    have hb := congrArg JordanTKK.neg (hbr W)
    simpa [negInj, zeroInj, posInj] using hb
  have hpos_part : ∀ W : H3OctonionTKKLie, ⁅ZD, W⁆.pos = D.1 W.pos := by
    intro W
    have hb := congrArg JordanTKK.pos (hbr W)
    simpa [negInj, zeroInj, posInj] using hb
  change tkkInvariantBilin ⁅ZD, X⁆ Y + tkkInvariantBilin X ⁅ZD, Y⁆ = 0
  rw [tkkInvariantBilin_apply, tkkInvariantBilin_apply]
  dsimp [tkkInvRaw]
  rw [hD_part X, hD_part Y, ha_part X, ha_part Y, hneg_part X, hneg_part Y,
    hpos_part X, hpos_part Y]
  have htr : LinearMap.trace ℝ (H3Octonion ℝ)
        (⁅D, strDerivPart X.zero⁆.1 * (strDerivPart Y.zero).1) +
      LinearMap.trace ℝ (H3Octonion ℝ)
        ((strDerivPart X.zero).1 * ⁅D, strDerivPart Y.zero⁆.1) = 0 := by
    change LinearMap.trace ℝ (H3Octonion ℝ)
        ((D.1 * (strDerivPart X.zero).1 - (strDerivPart X.zero).1 * D.1) *
          (strDerivPart Y.zero).1) +
      LinearMap.trace ℝ (H3Octonion ℝ)
        ((strDerivPart X.zero).1 *
          (D.1 * (strDerivPart Y.zero).1 - (strDerivPart Y.zero).1 * D.1)) = 0
    simp only [mul_sub, sub_mul, map_sub]
    have hcyc : LinearMap.trace ℝ (H3Octonion ℝ)
        (D.1 * (strDerivPart X.zero).1 * (strDerivPart Y.zero).1) =
        LinearMap.trace ℝ (H3Octonion ℝ)
          ((strDerivPart X.zero).1 * (strDerivPart Y.zero).1 * D.1) :=
      (LinearMap.trace_mul_cycle (R := ℝ) (M := H3Octonion ℝ)
        (strDerivPart X.zero).1 (strDerivPart Y.zero).1 D.1).symm
    rw [hcyc]
    simp only [mul_assoc]
    ring
  have h1 := h3Octonion_derivation_traceBilin_skew D (strLmulPart X.zero) (strLmulPart Y.zero)
  have h2 := h3Octonion_derivation_traceBilin_skew D X.neg Y.pos
  have h3 := h3Octonion_derivation_traceBilin_skew D X.pos Y.neg
  linarith [htr, h1, h2, h3]

private theorem tkkInvariantBilin_lieInvariant_lmul (c : H3Octonion ℝ)
    (X Y : H3OctonionTKKLie) :
    tkkInvariantBilin
        ⁅zeroInj ⟨jordanLmul (R := ℝ) c, h3OctonionTKKDatum.jordanLmul_mem_str c⟩, X⁆ Y +
      tkkInvariantBilin X
        ⁅zeroInj ⟨jordanLmul (R := ℝ) c, h3OctonionTKKDatum.jordanLmul_mem_str c⟩, Y⁆ = 0 := by
  have hcstr : jordanLmul (R := ℝ) c ∈ h3OctonionTKKDatum.str :=
    h3OctonionTKKDatum.jordanLmul_mem_str c
  let Zc : H3OctonionTKKLie := zeroInj ⟨jordanLmul (R := ℝ) c, hcstr⟩
  have hcomm : ∀ W : H3OctonionTKKLie,
      jordanLmul (R := ℝ) c ∘ₗ W.zero.1 - W.zero.1 ∘ₗ jordanLmul (R := ℝ) c =
        -jordanLmul (R := ℝ) ((strDerivPart W.zero).1 c) +
          (h3OctonionJordanInnerDerivation c (strLmulPart W.zero) : EndH3O) := by
    intro W
    have hW0 : W.zero.1 = (strDerivPart W.zero).1 + jordanLmul (R := ℝ) (strLmulPart W.zero) := by
      rw [strDerivPart_coe]; abel
    have h1 : jordanLmul (R := ℝ) c ∘ₗ (strDerivPart W.zero).1 -
        (strDerivPart W.zero).1 ∘ₗ jordanLmul (R := ℝ) c =
        -jordanLmul (R := ℝ) ((strDerivPart W.zero).1 c) := by
      rw [lie_jordanLmul_F4]; apply LinearMap.ext; intro z; simp [jordanLmul_apply, neg_mul]
    have h2 : jordanLmul (R := ℝ) c ∘ₗ jordanLmul (R := ℝ) (strLmulPart W.zero) -
        jordanLmul (R := ℝ) (strLmulPart W.zero) ∘ₗ jordanLmul (R := ℝ) c =
        (h3OctonionJordanInnerDerivation c (strLmulPart W.zero) : EndH3O) := rfl
    rw [hW0, LinearMap.comp_add, LinearMap.add_comp, ← h1, ← h2]
    abel
  have hcomm_mem : ∀ W : H3OctonionTKKLie,
      -jordanLmul (R := ℝ) ((strDerivPart W.zero).1 c) +
        (h3OctonionJordanInnerDerivation c (strLmulPart W.zero) : EndH3O) ∈
        h3OctonionTKKDatum.str := by
    intro W
    rw [← hcomm W]
    exact h3OctonionTKKDatum.str_lie_mem hcstr W.zero.2
  have hbr : ∀ W : H3OctonionTKKLie,
      ⁅Zc, W⁆ = negInj (c * W.neg) +
        zeroInj ⟨-jordanLmul (R := ℝ) ((strDerivPart W.zero).1 c) +
          (h3OctonionJordanInnerDerivation c (strLmulPart W.zero) : EndH3O),
          hcomm_mem W⟩ +
        posInj (-(c * W.pos)) := by
    intro W
    conv_lhs => rw [eq_neg_add_zero_add_pos W]
    simp only [Zc, lie_add, zeroInj_bracket_negInj, zeroInj_bracket_zeroInj,
      zeroInj_bracket_posInj, jordanLmul_apply, h3OctonionTraceAdjoint_jordanLmul]
    apply JordanTKK.ext
    · simp [negInj, zeroInj, posInj]
    · apply Subtype.ext
      simp only [JordanTKK.add_zero_comp, negInj, zeroInj, posInj, JordanTKK.negLM_zero,
        JordanTKK.zeroLM_zero, JordanTKK.posLM_zero, zero_add, add_zero]
      exact hcomm W
    · simp [negInj, zeroInj, posInj]
  have hD_part : ∀ W : H3OctonionTKKLie,
      strDerivPart ⁅Zc, W⁆.zero = h3OctonionJordanInnerDerivation c (strLmulPart W.zero) := by
    intro W
    have hb := congrArg JordanTKK.zero (hbr W)
    simp only [JordanTKK.add_zero_comp, negInj, zeroInj, posInj, JordanTKK.negLM_zero,
      JordanTKK.zeroLM_zero, JordanTKK.posLM_zero, zero_add, add_zero] at hb
    rw [hb]
    apply Subtype.ext
    rw [strDerivPart_coe]
    have hl1 : strLmulPart ⟨-jordanLmul (R := ℝ) ((strDerivPart W.zero).1 c) +
        (h3OctonionJordanInnerDerivation c (strLmulPart W.zero) : EndH3O),
        hcomm_mem W⟩ = -((strDerivPart W.zero).1 c) := by
      change (-jordanLmul (R := ℝ) ((strDerivPart W.zero).1 c) +
          (h3OctonionJordanInnerDerivation c (strLmulPart W.zero) : EndH3O)) 1 = _
      simp only [LinearMap.add_apply, LinearMap.neg_apply, jordanLmul_apply,
        h3Octonion_mul_one, h3OctonionJordanInnerDerivation_apply,
        _root_.mul_comm (strLmulPart W.zero) c, sub_self, add_zero]
    rw [hl1]
    apply LinearMap.ext; intro z
    simp [jordanLmul_apply, neg_mul]
  have ha_part : ∀ W : H3OctonionTKKLie,
      strLmulPart ⁅Zc, W⁆.zero = -((strDerivPart W.zero).1 c) := by
    intro W
    have hb := congrArg JordanTKK.zero (hbr W)
    simp only [JordanTKK.add_zero_comp, negInj, zeroInj, posInj, JordanTKK.negLM_zero,
      JordanTKK.zeroLM_zero, JordanTKK.posLM_zero, zero_add, add_zero] at hb
    rw [hb]
    change (-jordanLmul (R := ℝ) ((strDerivPart W.zero).1 c) +
        (h3OctonionJordanInnerDerivation c (strLmulPart W.zero) : EndH3O)) 1 = _
    simp only [LinearMap.add_apply, LinearMap.neg_apply, jordanLmul_apply,
      h3Octonion_mul_one, h3OctonionJordanInnerDerivation_apply,
      _root_.mul_comm (strLmulPart W.zero) c, sub_self, add_zero]
  have hneg_part : ∀ W : H3OctonionTKKLie, ⁅Zc, W⁆.neg = c * W.neg := by
    intro W; simpa [negInj, zeroInj, posInj] using congrArg JordanTKK.neg (hbr W)
  have hpos_part : ∀ W : H3OctonionTKKLie, ⁅Zc, W⁆.pos = -(c * W.pos) := by
    intro W; simpa [negInj, zeroInj, posInj] using congrArg JordanTKK.pos (hbr W)
  change tkkInvariantBilin ⁅Zc, X⁆ Y + tkkInvariantBilin X ⁅Zc, Y⁆ = 0
  rw [tkkInvariantBilin_apply, tkkInvariantBilin_apply]
  dsimp [tkkInvRaw]
  rw [hD_part X, hD_part Y, ha_part X, ha_part Y, hneg_part X, hneg_part Y,
    hpos_part X, hpos_part Y]
  have htrX : LinearMap.trace ℝ (H3Octonion ℝ)
      ((h3OctonionJordanInnerDerivation c (strLmulPart X.zero)).1 * (strDerivPart Y.zero).1) =
      3 * traceBilin ((strDerivPart Y.zero).1 c) (strLmulPart X.zero) := by
    rw [LinearMap.trace_mul_comm]
    exact h3Octonion_deriv_innerDeriv_trace (strDerivPart Y.zero) c (strLmulPart X.zero)
  have htrY : LinearMap.trace ℝ (H3Octonion ℝ)
      ((strDerivPart X.zero).1 * (h3OctonionJordanInnerDerivation c (strLmulPart Y.zero)).1) =
      3 * traceBilin ((strDerivPart X.zero).1 c) (strLmulPart Y.zero) :=
    h3Octonion_deriv_innerDeriv_trace (strDerivPart X.zero) c (strLmulPart Y.zero)
  rw [htrX, htrY, traceBilin_neg_left, traceBilin_neg_right, traceBilin_neg_left,
    traceBilin_neg_right, traceBilin_symm ((strDerivPart Y.zero).1 c) (strLmulPart X.zero),
    h3Octonion_traceBilin_jordanLmul_assoc c X.neg Y.pos,
    h3Octonion_traceBilin_jordanLmul_assoc c X.pos Y.neg]
  ring

private theorem tkkInvariantBilin_lieInvariant_neg (z : H3Octonion ℝ)
    (X Y : H3OctonionTKKLie) :
    tkkInvariantBilin ⁅negInj z, X⁆ Y + tkkInvariantBilin X ⁅negInj z, Y⁆ = 0 := by
  have hbr : ∀ W : H3OctonionTKKLie,
      ⁅negInj z, W⁆ = negInj (-(W.zero.1 z)) +
        zeroInj ⟨JordanTKK.tripleD ℝ z W.pos, h3OctonionTKKDatum.tripleD_mem_str z W.pos⟩ := by
    intro W
    conv_lhs => rw [eq_neg_add_zero_add_pos W]
    simp only [lie_add, negInj_bracket_negInj, negInj_bracket_zeroInj, negInj_bracket_posInj,
      zero_add]
  have hD_part : ∀ W : H3OctonionTKKLie,
      strDerivPart ⁅negInj z, W⁆.zero = h3OctonionJordanInnerDerivation z W.pos := by
    intro W
    have hb := congrArg JordanTKK.zero (hbr W)
    rw [hb]
    change strDerivPart ((0 : h3OctonionTKKDatum.str) +
        ⟨JordanTKK.tripleD ℝ z W.pos, h3OctonionTKKDatum.tripleD_mem_str z W.pos⟩) = _
    rw [zero_add]
    apply Subtype.ext
    rw [strDerivPart_coe]
    have htr := JordanTKK.tripleD_eq_left_add_inner (R := ℝ) z W.pos
    have hl1 : strLmulPart ⟨JordanTKK.tripleD ℝ z W.pos,
        h3OctonionTKKDatum.tripleD_mem_str z W.pos⟩ = z * W.pos := by
      change JordanTKK.tripleD ℝ z W.pos 1 = z * W.pos
      rw [htr]
      simp only [LinearMap.add_apply, jordanLmul_apply, h3Octonion_mul_one]
      have h1 : (jordanInnerDerivationBundled (R := ℝ) z W.pos : EndH3O) 1 = 0 :=
        h3Octonion_derivation_apply_one_eq_zero _
      rw [h1, add_zero]
    rw [hl1]
    change JordanTKK.tripleD ℝ z W.pos - jordanLmul (R := ℝ) (z * W.pos) = _
    rw [htr]
    simp only [add_sub_cancel_left]
    rfl
  have ha_part : ∀ W : H3OctonionTKKLie,
      strLmulPart ⁅negInj z, W⁆.zero = z * W.pos := by
    intro W
    have hb := congrArg JordanTKK.zero (hbr W)
    rw [hb]
    change strLmulPart ((0 : h3OctonionTKKDatum.str) +
        ⟨JordanTKK.tripleD ℝ z W.pos, h3OctonionTKKDatum.tripleD_mem_str z W.pos⟩) = _
    rw [zero_add]
    change JordanTKK.tripleD ℝ z W.pos 1 = z * W.pos
    rw [JordanTKK.tripleD_eq_left_add_inner (R := ℝ) z W.pos]
    simp only [LinearMap.add_apply, jordanLmul_apply, h3Octonion_mul_one]
    have h1 : (jordanInnerDerivationBundled (R := ℝ) z W.pos : EndH3O) 1 = 0 :=
      h3Octonion_derivation_apply_one_eq_zero _
    rw [h1, add_zero]
  have hneg_part : ∀ W : H3OctonionTKKLie,
      ⁅negInj z, W⁆.neg = -((strDerivPart W.zero).1 z + strLmulPart W.zero * z) := by
    intro W
    have hb := congrArg JordanTKK.neg (hbr W)
    rw [hb]
    change -(W.zero.1 z) + 0 = _
    rw [add_zero]
    have hW0 : W.zero.1 = (strDerivPart W.zero).1 + jordanLmul (R := ℝ) (strLmulPart W.zero) := by
      rw [strDerivPart_coe]; abel
    rw [hW0]
    simp [jordanLmul_apply]
  have hpos_part : ∀ W : H3OctonionTKKLie, ⁅negInj z, W⁆.pos = 0 := by
    intro W
    have hb := congrArg JordanTKK.pos (hbr W)
    rw [hb]
    change (0 : H3Octonion ℝ) + 0 = 0
    exact add_zero 0
  rw [tkkInvariantBilin_apply, tkkInvariantBilin_apply]
  dsimp [tkkInvRaw]
  rw [hD_part X, hD_part Y, ha_part X, ha_part Y, hneg_part X, hneg_part Y,
    hpos_part X, hpos_part Y]
  have htrX : LinearMap.trace ℝ (H3Octonion ℝ)
      ((h3OctonionJordanInnerDerivation z X.pos).1 * (strDerivPart Y.zero).1) =
      3 * traceBilin ((strDerivPart Y.zero).1 z) X.pos := by
    rw [LinearMap.trace_mul_comm]
    exact h3Octonion_deriv_innerDeriv_trace (strDerivPart Y.zero) z X.pos
  have htrY : LinearMap.trace ℝ (H3Octonion ℝ)
      ((strDerivPart X.zero).1 * (h3OctonionJordanInnerDerivation z Y.pos).1) =
      3 * traceBilin ((strDerivPart X.zero).1 z) Y.pos :=
    h3Octonion_deriv_innerDeriv_trace (strDerivPart X.zero) z Y.pos
  rw [htrX, htrY]
  simp only [traceBilin_zero_left, traceBilin_zero_right, zero_add, add_zero,
    traceBilin_neg_left, traceBilin_neg_right, traceBilin_add_left, traceBilin_add_right]
  have ha1 : traceBilin (strLmulPart X.zero * z) Y.pos =
      traceBilin (strLmulPart X.zero) (z * Y.pos) := by
    rw [_root_.mul_comm (strLmulPart X.zero) z, h3Octonion_traceBilin_jordanLmul_assoc z]
  have ha2 : traceBilin X.pos (strLmulPart Y.zero * z) =
      traceBilin (z * X.pos) (strLmulPart Y.zero) := by
    rw [traceBilin_symm X.pos, _root_.mul_comm (strLmulPart Y.zero) z,
      h3Octonion_traceBilin_jordanLmul_assoc z, traceBilin_symm (strLmulPart Y.zero)]
  rw [ha1, ha2, traceBilin_symm X.pos ((strDerivPart Y.zero).1 z)]
  ring

private theorem tkkInvariantBilin_lieInvariant_pos (w : H3Octonion ℝ)
    (X Y : H3OctonionTKKLie) :
    tkkInvariantBilin ⁅posInj w, X⁆ Y + tkkInvariantBilin X ⁅posInj w, Y⁆ = 0 := by
  have hθ : h3OctonionCartanInvolution (posInj w) = negInj (-w) := by
    apply JordanTKK.ext <;> simp [posInj, negInj]
    rw [show h3OctonionTraceAdjoint 0 = 0 from map_zero h3OctonionTraceAdjointLM]
  have hinv := tkkInvariantBilin_lieInvariant_neg (-w)
    (h3OctonionCartanInvolution X) (h3OctonionCartanInvolution Y)
  rw [← hθ, ← LieEquiv.map_lie, ← LieEquiv.map_lie,
    tkkInvariantBilin_cartanInvolution, tkkInvariantBilin_cartanInvolution] at hinv
  exact hinv

theorem tkkInvariantBilin_lieInvariant (Z X Y : H3OctonionTKKLie) :
    tkkInvariantBilin ⁅Z, X⁆ Y + tkkInvariantBilin X ⁅Z, Y⁆ = 0 := by
  conv_lhs => rw [eq_neg_add_zero_add_pos Z]
  obtain ⟨⟨D, a⟩, hDa⟩ := h3OctonionStructureDirectSumEquiv.surjective ⟨Z.zero.1, Z.zero.2⟩
  have hZ0 : zeroInj Z.zero =
      zeroInj ⟨D.1, deriv_mem_str D⟩ +
        zeroInj ⟨jordanLmul (R := ℝ) a, h3OctonionTKKDatum.jordanLmul_mem_str a⟩ := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact (congrArg Subtype.val hDa).symm
  rw [hZ0]
  simp only [add_lie, map_add, LinearMap.add_apply]
  have h1 := tkkInvariantBilin_lieInvariant_neg Z.neg X Y
  have h2 := tkkInvariantBilin_lieInvariant_F4 D X Y
  have h3 := tkkInvariantBilin_lieInvariant_lmul a X Y
  have h4 := tkkInvariantBilin_lieInvariant_pos Z.pos X Y
  linarith [h1, h2, h3, h4]

private def tkkCartanInnerRight (X : H3OctonionTKKLie) : H3OctonionTKKLie →ₗ[ℝ] ℝ where
  toFun Y := -tkkInvariantBilin X (h3OctonionCartanInvolution Y)
  map_add' Y₁ Y₂ := by simp only [map_add]; ring
  map_smul' r Y := by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; ring

private theorem tkkCartanInnerRight_apply (X Y : H3OctonionTKKLie) :
    tkkCartanInnerRight X Y = -tkkInvariantBilin X (h3OctonionCartanInvolution Y) := rfl

/-- The positive-definite Cartan inner product `⟨X, Y⟩_θ = -B(X, θ Y)` on `H3OctonionTKKLie`. -/
def tkkCartanInner : LinearMap.BilinForm ℝ H3OctonionTKKLie where
  toFun := tkkCartanInnerRight
  map_add' X₁ X₂ := by
    apply LinearMap.ext; intro Y
    change tkkCartanInnerRight (X₁ + X₂) Y = tkkCartanInnerRight X₁ Y + tkkCartanInnerRight X₂ Y
    simp only [tkkCartanInnerRight_apply, map_add, LinearMap.add_apply]
    ring
  map_smul' r X := by
    apply LinearMap.ext; intro Y
    change tkkCartanInnerRight (r • X) Y = r * tkkCartanInnerRight X Y
    simp only [tkkCartanInnerRight_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring

theorem tkkCartanInner_apply (X Y : H3OctonionTKKLie) :
    tkkCartanInner X Y = -tkkInvariantBilin X (h3OctonionCartanInvolution Y) := rfl

theorem tkkCartanInner_symm (X Y : H3OctonionTKKLie) :
    tkkCartanInner X Y = tkkCartanInner Y X := by
  rw [tkkCartanInner_apply, tkkCartanInner_apply, tkkInvariantBilin_symm,
    ← tkkInvariantBilin_cartanInvolution (h3OctonionCartanInvolution Y) X,
    h3OctonionCartanInvolution_involutive]

theorem tkkCartanInner_isSymm : LinearMap.IsSymm tkkCartanInner :=
  ⟨tkkCartanInner_symm⟩

theorem tkkCartanInner_self_eq (X : H3OctonionTKKLie) :
    tkkCartanInner X X =
      -LinearMap.trace ℝ (H3Octonion ℝ) ((strDerivPart X.zero).1 * (strDerivPart X.zero).1) +
      3 * traceBilin (strLmulPart X.zero) (strLmulPart X.zero) +
      3 * traceBilin X.neg X.neg +
      3 * traceBilin X.pos X.pos := by
  rw [tkkCartanInner_apply, tkkInvariantBilin_apply]
  dsimp [tkkInvRaw]
  rw [strDerivPart_neg_adj X.zero, strLmulPart_neg_adj X.zero]
  simp only [traceBilin_neg_right]
  ring

theorem tkkCartanInner_nonneg (X : H3OctonionTKKLie) : 0 ≤ tkkCartanInner X X := by
  rw [tkkCartanInner_self_eq]
  have hD := neg_nonneg.mpr (compactF4_trace_sq_nonpos (strDerivPart X.zero))
  have ha := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (traceBilin_self_nonneg (strLmulPart X.zero))
  have hx := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (traceBilin_self_nonneg X.neg)
  have hy := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (traceBilin_self_nonneg X.pos)
  linarith

theorem tkkCartanInner_eq_zero_iff (X : H3OctonionTKKLie) :
    tkkCartanInner X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [tkkCartanInner_self_eq] at h
    have hD := neg_nonneg.mpr (compactF4_trace_sq_nonpos (strDerivPart X.zero))
    have ha := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      (traceBilin_self_nonneg (strLmulPart X.zero))
    have hx := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (traceBilin_self_nonneg X.neg)
    have hy := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (traceBilin_self_nonneg X.pos)
    have hD0 : strDerivPart X.zero = 0 :=
      (compactF4_trace_sq_eq_zero_iff (strDerivPart X.zero)).mp (by linarith)
    have ha0 : strLmulPart X.zero = 0 :=
      (traceBilin_self_eq_zero_iff _).mp (by linarith)
    have hx0 : X.neg = 0 :=
      (traceBilin_self_eq_zero_iff _).mp (by linarith)
    have hy0 : X.pos = 0 :=
      (traceBilin_self_eq_zero_iff _).mp (by linarith)
    have hZ0 : X.zero = 0 := by
      apply Subtype.ext
      have hW0 : X.zero.1 = (strDerivPart X.zero).1 +
          jordanLmul (R := ℝ) (strLmulPart X.zero) := by
        rw [strDerivPart_coe]; abel
      rw [hW0, hD0, ha0]
      apply LinearMap.ext; intro z; simp [jordanLmul_apply]
    ext <;> simp [hx0, hZ0, hy0]
  · rintro rfl; simp

theorem tkkCartanInner_ad_skew_on_compact {Z : H3OctonionTKKLie}
    (hZ : Z ∈ h3OctonionCartanCompactSubalgebra) (X Y : H3OctonionTKKLie) :
    tkkCartanInner ⁅Z, X⁆ Y + tkkCartanInner X ⁅Z, Y⁆ = 0 := by
  rw [tkkCartanInner_apply, tkkCartanInner_apply, LieEquiv.map_lie, hZ]
  have hinv := tkkInvariantBilin_lieInvariant Z X (h3OctonionCartanInvolution Y)
  linarith

theorem tkkCartanInner_ad_self_on_noncompact {Z : H3OctonionTKKLie}
    (hZ : Z ∈ h3OctonionCartanNoncompactSubmodule) (X Y : H3OctonionTKKLie) :
    tkkCartanInner ⁅Z, X⁆ Y = tkkCartanInner X ⁅Z, Y⁆ := by
  rw [tkkCartanInner_apply, tkkCartanInner_apply, LieEquiv.map_lie, hZ, neg_lie,
    map_neg, neg_neg]
  have hinv := tkkInvariantBilin_lieInvariant Z X (h3OctonionCartanInvolution Y)
  linarith

private theorem trace_sq_nonpos_of_skew_ortho
    (A : Module.End ℝ H3OctonionTKKLie)
    (hskew : ∀ X Y, tkkCartanInner (A X) Y + tkkCartanInner X (A Y) = 0) :
    LinearMap.trace ℝ H3OctonionTKKLie (A * A) ≤ 0 ∧
      (LinearMap.trace ℝ H3OctonionTKKLie (A * A) = 0 → A = 0) := by
  have : FiniteDimensional ℝ H3OctonionTKKLie := inferInstance
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (B := tkkCartanInner) tkkCartanInner_isSymm
  have hpos : ∀ i, 0 < tkkCartanInner (v i) (v i) := fun i =>
    lt_of_le_of_ne (tkkCartanInner_nonneg (v i))
      (fun h => (v.ne_zero i) ((tkkCartanInner_eq_zero_iff (v i)).mp h.symm))
  have hrepr : ∀ i (W : H3OctonionTKKLie),
      v.repr W i = tkkCartanInner (v i) W / tkkCartanInner (v i) (v i) := by
    intro i W
    have hsum : tkkCartanInner (v i) W =
        ∑ j, v.repr W j * tkkCartanInner (v i) (v j) := by
      conv_lhs => rw [← v.sum_repr W]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hsum, Finset.sum_eq_single i]
    · exact (eq_div_iff (ne_of_gt (hpos i))).mpr rfl
    · intro j _ hji
      rw [hv hji.symm, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have htr : LinearMap.trace ℝ H3OctonionTKKLie (A * A) =
      ∑ i, -(tkkCartanInner (A (v i)) (A (v i)) / tkkCartanInner (v i) (v i)) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ v]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.End.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrepr i (A (A (v i)))]
    have hsk := hskew (v i) (A (v i))
    have hneg : tkkCartanInner (v i) (A (A (v i))) =
        -tkkCartanInner (A (v i)) (A (v i)) := by linarith
    rw [hneg, neg_div]
  rw [htr, Finset.sum_neg_distrib]
  refine ⟨neg_nonpos.mpr (Finset.sum_nonneg fun i _ =>
    div_nonneg (tkkCartanInner_nonneg _) (hpos i).le), ?_⟩
  intro hz
  rw [neg_eq_zero] at hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (tkkCartanInner_nonneg _) (hpos i).le).mp hz
  apply v.ext
  intro i
  have hi := hall i (Finset.mem_univ i)
  rw [div_eq_zero_iff] at hi
  have hAi0 : tkkCartanInner (A (v i)) (A (v i)) = 0 :=
    hi.resolve_right (ne_of_gt (hpos i))
  exact (tkkCartanInner_eq_zero_iff _).mp hAi0

private theorem trace_sq_nonneg_of_self_ortho
    (A : Module.End ℝ H3OctonionTKKLie)
    (hself : ∀ X Y, tkkCartanInner (A X) Y = tkkCartanInner X (A Y)) :
    0 ≤ LinearMap.trace ℝ H3OctonionTKKLie (A * A) ∧
      (LinearMap.trace ℝ H3OctonionTKKLie (A * A) = 0 → A = 0) := by
  have : FiniteDimensional ℝ H3OctonionTKKLie := inferInstance
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (B := tkkCartanInner) tkkCartanInner_isSymm
  have hpos : ∀ i, 0 < tkkCartanInner (v i) (v i) := fun i =>
    lt_of_le_of_ne (tkkCartanInner_nonneg (v i))
      (fun h => (v.ne_zero i) ((tkkCartanInner_eq_zero_iff (v i)).mp h.symm))
  have hrepr : ∀ i (W : H3OctonionTKKLie),
      v.repr W i = tkkCartanInner (v i) W / tkkCartanInner (v i) (v i) := by
    intro i W
    have hsum : tkkCartanInner (v i) W =
        ∑ j, v.repr W j * tkkCartanInner (v i) (v j) := by
      conv_lhs => rw [← v.sum_repr W]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    rw [hsum, Finset.sum_eq_single i]
    · exact (eq_div_iff (ne_of_gt (hpos i))).mpr rfl
    · intro j _ hji
      rw [hv hji.symm, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have htr : LinearMap.trace ℝ H3OctonionTKKLie (A * A) =
      ∑ i, tkkCartanInner (A (v i)) (A (v i)) / tkkCartanInner (v i) (v i) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ v]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.End.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrepr i (A (A (v i))), ← hself (v i) (A (v i))]
  rw [htr]
  refine ⟨Finset.sum_nonneg fun i _ =>
    div_nonneg (tkkCartanInner_nonneg _) (hpos i).le, ?_⟩
  intro hz
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (tkkCartanInner_nonneg _) (hpos i).le).mp hz
  apply v.ext
  intro i
  have hi := hall i (Finset.mem_univ i)
  rw [div_eq_zero_iff] at hi
  have hAi0 : tkkCartanInner (A (v i)) (A (v i)) = 0 :=
    hi.resolve_right (ne_of_gt (hpos i))
  exact (tkkCartanInner_eq_zero_iff _).mp hAi0

private theorem ad_eq_zero_iff (X : H3OctonionTKKLie) :
    LieAlgebra.ad ℝ H3OctonionTKKLie X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hmem : X ∈ LieAlgebra.center ℝ H3OctonionTKKLie := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro Y
      have hYX : ⁅X, Y⁆ = 0 := LinearMap.ext_iff.mp h Y
      rw [← lie_skew Y X, hYX, neg_zero]
    rw [center_H3OctonionTKKLie_eq_bot, LieSubmodule.mem_bot] at hmem
    exact hmem
  · rintro rfl; simp

/-- Negative semi-definiteness of the Killing form on the 79D compact eigenspace `k`. -/
theorem killingForm_cartanCompact_nonpos {X : H3OctonionTKKLie}
    (hX : X ∈ h3OctonionCartanCompactSubalgebra) :
    killingForm ℝ H3OctonionTKKLie X X ≤ 0 := by
  rw [killingForm_apply_apply]
  exact (trace_sq_nonpos_of_skew_ortho (LieAlgebra.ad ℝ H3OctonionTKKLie X)
    (tkkCartanInner_ad_skew_on_compact hX)).1

/-- Strict negative definiteness of the Killing form on `k`. -/
theorem killingForm_cartanCompact_eq_zero_iff {X : H3OctonionTKKLie}
    (hX : X ∈ h3OctonionCartanCompactSubalgebra) :
    killingForm ℝ H3OctonionTKKLie X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonpos_of_skew_ortho (LieAlgebra.ad ℝ H3OctonionTKKLie X)
      (tkkCartanInner_ad_skew_on_compact hX)).2 h
    exact (ad_eq_zero_iff X).mp had0
  · rintro rfl; simp

/-- Positive semi-definiteness of the Killing form on the 54D non-compact eigenspace `p`. -/
theorem killingForm_cartanNoncompact_nonneg {X : H3OctonionTKKLie}
    (hX : X ∈ h3OctonionCartanNoncompactSubmodule) :
    0 ≤ killingForm ℝ H3OctonionTKKLie X X := by
  rw [killingForm_apply_apply]
  exact (trace_sq_nonneg_of_self_ortho (LieAlgebra.ad ℝ H3OctonionTKKLie X)
    (tkkCartanInner_ad_self_on_noncompact hX)).1

/-- Strict positive definiteness of the Killing form on `p`. -/
theorem killingForm_cartanNoncompact_eq_zero_iff {X : H3OctonionTKKLie}
    (hX : X ∈ h3OctonionCartanNoncompactSubmodule) :
    killingForm ℝ H3OctonionTKKLie X X = 0 ↔ X = 0 := by
  constructor
  · intro h
    rw [killingForm_apply_apply] at h
    have had0 := (trace_sq_nonneg_of_self_ortho (LieAlgebra.ad ℝ H3OctonionTKKLie X)
      (tkkCartanInner_ad_self_on_noncompact hX)).2 h
    exact (ad_eq_zero_iff X).mp had0
  · rintro rfl; simp

/-- Killing orthogonality `k ⊥ p` of the Cartan decomposition. -/
theorem killingForm_cartanCompact_noncompact_ortho {X Y : H3OctonionTKKLie}
    (hX : X ∈ h3OctonionCartanCompactSubalgebra)
    (hY : Y ∈ h3OctonionCartanNoncompactSubmodule) :
    killingForm ℝ H3OctonionTKKLie X Y = 0 := by
  have heq := LieAlgebra.killingForm_of_equiv_apply h3OctonionCartanInvolution X Y
  rw [hX, hY, map_neg] at heq
  linarith

/-- `H3OctonionTKKLie` (`𝔈₇(-25)`) has non-degenerate Killing form (`IsKilling`, hence
`IsSemisimple ℝ` and `HasTrivialRadical ℝ`). -/
instance instIsKillingH3OctonionTKKLie : LieAlgebra.IsKilling ℝ H3OctonionTKKLie := by
  constructor
  rw [eq_bot_iff]
  intro Z hZ
  rw [LieSubmodule.mem_bot]
  have hZker : ∀ W : H3OctonionTKKLie,
      killingForm ℝ H3OctonionTKKLie W Z = 0 := fun W =>
    (LieIdeal.mem_killingCompl ℝ H3OctonionTKKLie ⊤).mp hZ W (LieSubmodule.mem_top W)
  let Zk : H3OctonionTKKLie := (1 / 2 : ℝ) • (Z + h3OctonionCartanInvolution Z)
  let Zp : H3OctonionTKKLie := (1 / 2 : ℝ) • (Z - h3OctonionCartanInvolution Z)
  have hZk : Zk ∈ h3OctonionCartanCompactSubalgebra := by
    change h3OctonionCartanInvolution Zk = Zk
    dsimp [Zk]
    rw [map_smul, map_add, h3OctonionCartanInvolution_involutive, add_comm]
  have hZp : Zp ∈ h3OctonionCartanNoncompactSubmodule := by
    change h3OctonionCartanInvolution Zp = -Zp
    dsimp [Zp]
    rw [map_smul, map_sub, h3OctonionCartanInvolution_involutive, ← smul_neg, neg_sub]
  have hsum : Z = Zk + Zp := by dsimp [Zk, Zp]; module
  have hZk0 : Zk = 0 := by
    apply (killingForm_cartanCompact_eq_zero_iff hZk).mp
    have h1 := hZker Zk
    rw [hsum, map_add, killingForm_cartanCompact_noncompact_ortho hZk hZp, add_zero] at h1
    exact h1
  have hZp0 : Zp = 0 := by
    apply (killingForm_cartanNoncompact_eq_zero_iff hZp).mp
    have h1 := hZker Zp
    rw [hsum, map_add, LieModule.traceForm_comm, killingForm_cartanCompact_noncompact_ortho hZk hZp,
      zero_add] at h1
    exact h1
  rw [hsum, hZk0, hZp0, add_zero]

end KillingFormAndInvariantBilin

section SignatureWitnesses

open H3OctonionTKKLie

theorem ad_sq_compact_witness_gradeOp :
    ⁅negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ),
      ⁅negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ), h3OctonionTKKGradeOp⁆⁆ =
      (-2 : ℝ) • h3OctonionTKKGradeOp := by
  have h1 : ⁅negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ), h3OctonionTKKGradeOp⁆ =
      -negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ) := by
    rw [sub_lie, ← lie_skew (negInj 1) h3OctonionTKKGradeOp,
      ← lie_skew (posInj 1) h3OctonionTKKGradeOp,
      h3OctonionTKKGradeOp_bracket_neg, h3OctonionTKKGradeOp_bracket_pos, neg_neg]
  rw [h1, sub_lie, lie_sub, lie_sub, lie_neg, lie_neg, negInj_bracket_negInj,
    posInj_bracket_posInj, negInj_one_bracket_posInj_one_eq_gradeOp,
    ← lie_skew (posInj 1) (negInj 1), negInj_one_bracket_posInj_one_eq_gradeOp]
  module

theorem ad_sq_noncompact_witness_gradeOp :
    ⁅negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ),
      ⁅negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ), h3OctonionTKKGradeOp⁆⁆ =
      (2 : ℝ) • h3OctonionTKKGradeOp := by
  have h1 : ⁅negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ), h3OctonionTKKGradeOp⁆ =
      -negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ) := by
    rw [add_lie, ← lie_skew (negInj 1) h3OctonionTKKGradeOp,
      ← lie_skew (posInj 1) h3OctonionTKKGradeOp,
      h3OctonionTKKGradeOp_bracket_neg, h3OctonionTKKGradeOp_bracket_pos, neg_neg]
  rw [h1, add_lie, lie_add, lie_add]
  simp only [lie_neg]
  rw [negInj_bracket_negInj, posInj_bracket_posInj, negInj_one_bracket_posInj_one_eq_gradeOp,
    ← lie_skew (posInj 1) (negInj 1), negInj_one_bracket_posInj_one_eq_gradeOp]
  module

theorem compact_witness_mem_cartanCompact :
    negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ) ∈
      h3OctonionCartanCompactSubalgebra := by
  apply JordanTKK.ext <;> simp [negInj, posInj]

theorem noncompact_witness_mem_cartanNoncompact :
    negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ) ∈
      h3OctonionCartanNoncompactSubmodule := by
  apply JordanTKK.ext <;> simp [negInj, posInj]
  rw [show h3OctonionTraceAdjoint 0 = 0 from map_zero h3OctonionTraceAdjointLM]
  simp

theorem killingForm_compact_witness_neg :
    killingForm ℝ H3OctonionTKKLie
      (negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ))
      (negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ)) < 0 := by
  have hle := killingForm_cartanCompact_nonpos compact_witness_mem_cartanCompact
  have hne : killingForm ℝ H3OctonionTKKLie
      (negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ))
      (negInj (1 : H3Octonion ℝ) - posInj (1 : H3Octonion ℝ)) ≠ 0 := by
    intro h0
    have hX0 := (killingForm_cartanCompact_eq_zero_iff compact_witness_mem_cartanCompact).mp h0
    have h1 := congrArg JordanTKK.neg hX0
    simp [negInj, posInj] at h1
    exact h3Octonion_one_ne_zero h1
  exact lt_of_le_of_ne hle hne

theorem killingForm_noncompact_witness_pos :
    0 < killingForm ℝ H3OctonionTKKLie
      (negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ))
      (negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ)) := by
  have hge := killingForm_cartanNoncompact_nonneg noncompact_witness_mem_cartanNoncompact
  have hne : killingForm ℝ H3OctonionTKKLie
      (negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ))
      (negInj (1 : H3Octonion ℝ) + posInj (1 : H3Octonion ℝ)) ≠ 0 := by
    intro h0
    have hX0 :=
      (killingForm_cartanNoncompact_eq_zero_iff noncompact_witness_mem_cartanNoncompact).mp h0
    have h1 := congrArg JordanTKK.neg hX0
    simp [negInj, posInj] at h1
    exact h3Octonion_one_ne_zero h1
  exact lt_of_le_of_ne hge (Ne.symm hne)

end SignatureWitnesses

end InfoGeometry.Algebra
