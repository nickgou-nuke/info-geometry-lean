/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.JordanTKKLieAlgebra
import InfoGeometry.Algebra.H3ZornReducedStructureLieAlgebra
import InfoGeometry.Canonical.H3ZornTKKNative

/-!
# 133-Dimensional Split Exceptional Lie Algebra `𝔈₇(7)` on `H3Zorn ℝ`

This module instantiates the generic 3-graded Jordan-TKK construction on the verified
27-dimensional real split Albert algebra `H3Zorn ℝ` with its 79-dimensional structure
Lie subalgebra `structureOperatorLieSubalgebra` and trace adjoint `h3zornTraceAdjoint`:

1. `h3zornTKKDatum : JordanTKKDatum ℝ (H3Zorn ℝ)` with verified adjoint laws
   `h3zornTraceAdjoint_comp`, `h3zornTraceAdjoint_jordanLmul`, and
   `h3zornTraceAdjoint_derivation`.
2. `H3ZornTKKLie := JordanTKK (H3Zorn ℝ) h3zornTKKDatum.str` equipped with
   `LieRing`, `LieAlgebra ℝ`, `Module.Finite ℝ`, and `finrank_H3ZornTKKLie = 133`
   (`27 + 79 + 27 = 133`).
3. Faithful Lie-bracket embedding `h3zornTKKToNative : H3ZornTKKLie → H3ZornTKKNative.TKKCarrier`
   preserving negation and `H3ZornTKKNative.tkkBracket`.
4. Grade constructors/projections, `h3zornCubicStabilizerToTKK` (`E₆(6)` Levi embedding),
   the grading element `h3zornTKKGradeOp` (`L₁ = id`), dual-eigenvector adjoint lemma,
   and non-triviality witnesses.
-/

noncomputable section

namespace InfoGeometry.Canonical.H3ZornTKKLieAlgebra

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Algebra.SplitAlbertStructureOperators

attribute [local instance 100] LieRing.ofAssociativeRing

instance instModuleFiniteH3Zorn : Module.Finite ℝ (H3Zorn ℝ) :=
  Module.Finite.of_basis h3ZornBasis

section TraceAdjointLaws

/-- `h3zornTraceAdjoint` packaged as an `ℝ`-linear endomorphism of `Module.End ℝ (H3Zorn ℝ)`. -/
def h3zornTraceAdjointLM : Module.End ℝ (H3Zorn ℝ) →ₗ[ℝ] Module.End ℝ (H3Zorn ℝ) where
  toFun := h3zornTraceAdjoint
  map_add' A B := by
    apply LinearMap.ext
    intro x
    apply H3Zorn.eq_of_traceBilin_left_eq
    intro y
    rw [LinearMap.add_apply, traceBilin_add_left, h3zornTraceAdjoint_pair,
      h3zornTraceAdjoint_pair, h3zornTraceAdjoint_pair, LinearMap.add_apply, traceBilin_add_right]
  map_smul' r A := by
    apply LinearMap.ext
    intro x
    apply H3Zorn.eq_of_traceBilin_left_eq
    intro y
    rw [LinearMap.smul_apply, traceBilin_smul_left, h3zornTraceAdjoint_pair,
      h3zornTraceAdjoint_pair, LinearMap.smul_apply, traceBilin_smul_right, RingHom.id_apply]

@[simp] theorem h3zornTraceAdjointLM_apply (A : Module.End ℝ (H3Zorn ℝ)) :
    h3zornTraceAdjointLM A = h3zornTraceAdjoint A := rfl

theorem h3zornTraceAdjoint_comp (A B : Module.End ℝ (H3Zorn ℝ)) :
    h3zornTraceAdjoint (A ∘ₗ B) = h3zornTraceAdjoint B ∘ₗ h3zornTraceAdjoint A := by
  apply LinearMap.ext
  intro x
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro y
  rw [LinearMap.comp_apply, h3zornTraceAdjoint_pair, h3zornTraceAdjoint_pair,
    h3zornTraceAdjoint_pair, LinearMap.comp_apply]

theorem h3zornTraceAdjoint_jordanLmul (a : H3Zorn ℝ) :
    h3zornTraceAdjoint (jordanLmul (R := ℝ) a) = jordanLmul (R := ℝ) a := by
  apply LinearMap.ext
  intro x
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro y
  rw [h3zornTraceAdjoint_pair, jordanLmul_apply, jordanLmul_apply,
    ← h3Zorn_traceBilin_jordanLmul_assoc a x y, mul_comm a x]

theorem h3zornTraceAdjoint_derivation (D : NonAssocDerivation.derivations ℝ (H3Zorn ℝ)) :
    h3zornTraceAdjoint (D : Module.End ℝ (H3Zorn ℝ)) = -(D : Module.End ℝ (H3Zorn ℝ)) := by
  apply LinearMap.ext
  intro x
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro y
  rw [h3zornTraceAdjoint_pair, LinearMap.neg_apply,
    show -((D : Module.End ℝ (H3Zorn ℝ)) x) = (-1 : ℝ) • ((D : Module.End ℝ (H3Zorn ℝ)) x) by
      module,
    traceBilin_smul_left, neg_one_mul]
  have hskew := h3ZornF4_derivation_traceBilin_skew ⟨(D : Module.End ℝ (H3Zorn ℝ)), D.2⟩ x y
  exact eq_neg_of_add_eq_zero_right hskew

theorem h3zornTraceAdjoint_id :
    h3zornTraceAdjoint (LinearMap.id : Module.End ℝ (H3Zorn ℝ)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro y
  rw [h3zornTraceAdjoint_pair, LinearMap.id_apply, LinearMap.id_apply]

/-- Trace-adjoint eigenvector transport for dual bases: if `T` acts diagonally on a basis `b`
with eigenvalues `w`, then `h3zornTraceAdjoint T` acts with eigenvalue `w j` on any vector `v`
`traceBilin`-orthogonal to `b k` for `k ≠ j`. -/
theorem h3zornTraceAdjoint_eigenvector
    (T : Module.End ℝ (H3Zorn ℝ)) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (H3Zorn ℝ)) (w : ι → ℝ) (hT : ∀ k, T (b k) = w k • b k)
    (v : H3Zorn ℝ) (j : ι) (hv : ∀ k, k ≠ j → traceBilin v (b k) = 0) :
    h3zornTraceAdjoint T v = w j • v := by
  apply H3Zorn.eq_of_traceBilin_left_eq
  intro z
  rw [← b.sum_repr z]
  change h3zornTraceBilin (h3zornTraceAdjoint T v) (∑ k, (b.repr z) k • b k) =
    h3zornTraceBilin (w j • v) (∑ k, (b.repr z) k • b k)
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul, LinearMap.map_smul]
  congr 1
  change traceBilin (h3zornTraceAdjoint T v) (b k) = traceBilin (w j • v) (b k)
  rw [h3zornTraceAdjoint_pair, hT k, traceBilin_smul_right, traceBilin_smul_left]
  by_cases hkj : k = j
  · subst hkj
    rfl
  · rw [hv k hkj, mul_zero, mul_zero]

end TraceAdjointLaws

/-- The verified TKK datum on the split Albert algebra `H3Zorn ℝ`. -/
def h3zornTKKDatum : JordanTKKDatum ℝ (H3Zorn ℝ) where
  str := structureOperatorLieSubalgebra.toSubmodule
  adj := h3zornTraceAdjointLM
  adj_comp := h3zornTraceAdjoint_comp
  adj_jordanLmul := h3zornTraceAdjoint_jordanLmul
  adj_derivation := h3zornTraceAdjoint_derivation
  str_decomp := by
    rintro T ⟨D, a, rfl⟩
    exact ⟨⟨(D : Module.End ℝ (H3Zorn ℝ)), D.2⟩, a, rfl⟩
  jordanLmul_mem_str a := ⟨0, a, by
    change jordanLmul (R := ℝ) a = (0 : Module.End ℝ (H3Zorn ℝ)) + jordanLmul (R := ℝ) a
    rw [zero_add]⟩
  innerDeriv_mem_str x y := by
    refine ⟨⟨_, h3ZornJordanInnerDerivation_mem_F4 x y⟩, 0, ?_⟩
    apply LinearMap.ext
    intro z
    change (jordanInnerDerivationBundled (R := ℝ) x y : Module.End ℝ (H3Zorn ℝ)) z =
      (h3ZornJordanInnerDerivation x y : Module.End ℝ (H3Zorn ℝ)) z + (0 : H3Zorn ℝ) * z
    rw [zero_mul, add_zero]
    rfl
  str_lie_mem {T U} hT hU := structureOperatorLieSubalgebra.lie_mem hT hU

/-- The 133-dimensional split real exceptional Lie algebra `𝔈₇(7)` on `H3Zorn ℝ`. -/
abbrev H3ZornTKKLie := JordanTKK (H3Zorn ℝ) h3zornTKKDatum.str

instance instLieRingH3ZornTKKLie : LieRing H3ZornTKKLie :=
  JordanTKK.lieRing h3zornTKKDatum

instance instLieAlgebraH3ZornTKKLie : LieAlgebra ℝ H3ZornTKKLie :=
  JordanTKK.lieAlgebra h3zornTKKDatum

/-- **Exact 133-dimensionality of `𝔈₇(7)`**: `27 + 79 + 27 = 133`. -/
theorem finrank_H3ZornTKKLie : Module.finrank ℝ H3ZornTKKLie = 133 := by
  rw [JordanTKK.finrank_jordanTKK (F := ℝ)]
  have h_str : Module.finrank ℝ h3zornTKKDatum.str = 79 := by
    change Module.finrank ℝ structureOperatorLieSubalgebra = 79
    exact finrank_structureOperatorLieSubalgebra
  rw [finrank_h3zorn, h_str]

section NativeEmbedding

theorem tripleD_eq_native (x y : H3Zorn ℝ) :
    JordanTKK.tripleD ℝ x y = H3ZornJordanTripleBridge.jordanTripleD x y := by
  apply LinearMap.ext
  intro z
  rfl

/-- Faithful Lie-bracket embedding from `H3ZornTKKLie` into `H3ZornTKKNative.TKKCarrier`. -/
def h3zornTKKToNative (X : H3ZornTKKLie) : H3ZornTKKNative.TKKCarrier where
  neg := X.neg
  zeroOp := X.zero.1
  zeroAdj := h3zornTraceAdjoint X.zero.1
  pos := X.pos

theorem h3zornTKKToNative_injective : Function.Injective h3zornTKKToNative := by
  intro X Y h
  apply JordanTKK.ext
  · exact congrArg H3ZornTKKNative.TKKCarrier.neg h
  · exact Subtype.ext (congrArg H3ZornTKKNative.TKKCarrier.zeroOp h)
  · exact congrArg H3ZornTKKNative.TKKCarrier.pos h

theorem h3zornTKKToNative_neg (X : H3ZornTKKLie) :
    h3zornTKKToNative (-X) = H3ZornTKKNative.tkkNeg (h3zornTKKToNative X) := by
  apply H3ZornTKKNative.TKKCarrier.ext
  · rfl
  · rfl
  · change h3zornTraceAdjoint (-X.zero.1) = -h3zornTraceAdjoint X.zero.1
    exact map_neg h3zornTraceAdjointLM X.zero.1
  · rfl

theorem h3zornTKKToNative_bracket (X Y : H3ZornTKKLie) :
    h3zornTKKToNative ⁅X, Y⁆ =
      H3ZornTKKNative.tkkBracket (h3zornTKKToNative X) (h3zornTKKToNative Y) := by
  apply H3ZornTKKNative.TKKCarrier.ext
  · rfl
  · change (X.zero.1 ∘ₗ Y.zero.1 - Y.zero.1 ∘ₗ X.zero.1) +
        (JordanTKK.tripleD ℝ X.neg Y.pos - JordanTKK.tripleD ℝ Y.neg X.pos) =
      (X.zero.1.comp Y.zero.1 - Y.zero.1.comp X.zero.1) +
        (H3ZornJordanTripleBridge.jordanTripleD X.neg Y.pos -
          H3ZornJordanTripleBridge.jordanTripleD Y.neg X.pos)
    rw [tripleD_eq_native X.neg Y.pos, tripleD_eq_native Y.neg X.pos]
  · change h3zornTraceAdjointLM
        ((X.zero.1 ∘ₗ Y.zero.1 - Y.zero.1 ∘ₗ X.zero.1) +
          (JordanTKK.tripleD ℝ X.neg Y.pos - JordanTKK.tripleD ℝ Y.neg X.pos)) =
      ((h3zornTraceAdjoint Y.zero.1).comp (h3zornTraceAdjoint X.zero.1) -
        (h3zornTraceAdjoint X.zero.1).comp (h3zornTraceAdjoint Y.zero.1)) +
        (H3ZornJordanTripleBridge.jordanTripleD Y.pos X.neg -
          H3ZornJordanTripleBridge.jordanTripleD X.pos Y.neg)
    rw [map_add, map_sub, map_sub, h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
      h3zornTraceAdjointLM_apply, h3zornTraceAdjointLM_apply,
      h3zornTraceAdjoint_comp, h3zornTraceAdjoint_comp]
    have h1 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ X.neg Y.pos) =
        H3ZornJordanTripleBridge.jordanTripleD Y.pos X.neg := by
      have hadj := h3zornTKKDatum.adj_tripleD X.neg Y.pos
      change h3zornTraceAdjoint (JordanTKK.tripleD ℝ X.neg Y.pos) = _ at hadj
      rw [hadj, tripleD_eq_native]
    have h2 : h3zornTraceAdjoint (JordanTKK.tripleD ℝ Y.neg X.pos) =
        H3ZornJordanTripleBridge.jordanTripleD X.pos Y.neg := by
      have hadj := h3zornTKKDatum.adj_tripleD Y.neg X.pos
      change h3zornTraceAdjoint (JordanTKK.tripleD ℝ Y.neg X.pos) = _ at hadj
      rw [hadj, tripleD_eq_native]
    rw [h1, h2]
  · rfl

end NativeEmbedding

section DownstreamAPI

/-- Grade `-1` injection `H3Zorn ℝ →ₗ[ℝ] H3ZornTKKLie`. -/
def negInj : H3Zorn ℝ →ₗ[ℝ] H3ZornTKKLie :=
  JordanTKK.negLM (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str)

/-- Grade `0` injection `h3zornTKKDatum.str →ₗ[ℝ] H3ZornTKKLie`. -/
def zeroInj : h3zornTKKDatum.str →ₗ[ℝ] H3ZornTKKLie :=
  JordanTKK.zeroLM (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str)

/-- Grade `+1` injection `H3Zorn ℝ →ₗ[ℝ] H3ZornTKKLie`. -/
def posInj : H3Zorn ℝ →ₗ[ℝ] H3ZornTKKLie :=
  JordanTKK.posLM (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str)

/-- Projection onto grade `-1`. -/
def projNeg : H3ZornTKKLie →ₗ[ℝ] H3Zorn ℝ :=
  JordanTKK.projNeg (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str)

/-- Projection onto grade `0`. -/
def projZero : H3ZornTKKLie →ₗ[ℝ] h3zornTKKDatum.str :=
  JordanTKK.projZero (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str)

/-- Projection onto grade `+1`. -/
def projPos : H3ZornTKKLie →ₗ[ℝ] H3Zorn ℝ :=
  JordanTKK.projPos (R := ℝ) (J := H3Zorn ℝ) (S := h3zornTKKDatum.str)

theorem negInj_injective : Function.Injective negInj := JordanTKK.negLM_injective
theorem zeroInj_injective : Function.Injective zeroInj := JordanTKK.zeroLM_injective
theorem posInj_injective : Function.Injective posInj := JordanTKK.posLM_injective

@[simp] theorem negInj_bracket_negInj (x₁ x₂ : H3Zorn ℝ) :
    ⁅negInj x₁, negInj x₂⁆ = 0 :=
  JordanTKK.neg_bracket_neg h3zornTKKDatum x₁ x₂

@[simp] theorem posInj_bracket_posInj (y₁ y₂ : H3Zorn ℝ) :
    ⁅posInj y₁, posInj y₂⁆ = 0 :=
  JordanTKK.pos_bracket_pos h3zornTKKDatum y₁ y₂

@[simp] theorem zeroInj_bracket_zeroInj (T₁ T₂ : h3zornTKKDatum.str) :
    ⁅zeroInj T₁, zeroInj T₂⁆ =
      zeroInj ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3zornTKKDatum.str_lie_mem T₁.2 T₂.2⟩ :=
  JordanTKK.zero_bracket_zero h3zornTKKDatum T₁ T₂

@[simp] theorem zeroInj_bracket_negInj (T : h3zornTKKDatum.str) (x : H3Zorn ℝ) :
    ⁅zeroInj T, negInj x⁆ = negInj (T.1 x) :=
  JordanTKK.zero_bracket_neg h3zornTKKDatum T x

@[simp] theorem negInj_bracket_zeroInj (x : H3Zorn ℝ) (T : h3zornTKKDatum.str) :
    ⁅negInj x, zeroInj T⁆ = negInj (-(T.1 x)) :=
  JordanTKK.neg_bracket_zero h3zornTKKDatum x T

@[simp] theorem zeroInj_bracket_posInj (T : h3zornTKKDatum.str) (y : H3Zorn ℝ) :
    ⁅zeroInj T, posInj y⁆ = posInj (-h3zornTraceAdjoint T.1 y) :=
  JordanTKK.zero_bracket_pos h3zornTKKDatum T y

@[simp] theorem posInj_bracket_zeroInj (y : H3Zorn ℝ) (T : h3zornTKKDatum.str) :
    ⁅posInj y, zeroInj T⁆ = posInj (h3zornTraceAdjoint T.1 y) :=
  JordanTKK.pos_bracket_zero h3zornTKKDatum y T

@[simp] theorem negInj_bracket_posInj (x y : H3Zorn ℝ) :
    ⁅negInj x, posInj y⁆ =
      zeroInj ⟨JordanTKK.tripleD ℝ x y, h3zornTKKDatum.tripleD_mem_str x y⟩ :=
  JordanTKK.neg_bracket_pos h3zornTKKDatum x y

@[simp] theorem posInj_bracket_negInj (y x : H3Zorn ℝ) :
    ⁅posInj y, negInj x⁆ =
      zeroInj ⟨-JordanTKK.tripleD ℝ x y,
        h3zornTKKDatum.str.neg_mem (h3zornTKKDatum.tripleD_mem_str x y)⟩ :=
  JordanTKK.pos_bracket_neg h3zornTKKDatum y x

/-- Canonical Lie-algebra inclusion of the 79D structure algebra into `H3ZornTKKLie`. -/
def zeroLieHom : structureOperatorLieSubalgebra →ₗ⁅ℝ⁆ H3ZornTKKLie where
  toFun T := zeroInj ⟨T.1, T.2⟩
  map_add' T₁ T₂ := by
    change zeroInj (⟨T₁.1, T₁.2⟩ + ⟨T₂.1, T₂.2⟩) = _
    rw [map_add]
  map_smul' r T := by
    change zeroInj (r • ⟨T.1, T.2⟩) = _
    rw [map_smul]
    rfl
  map_lie' {T₁ T₂} := by
    change zeroInj ⟨T₁.1 ∘ₗ T₂.1 - T₂.1 ∘ₗ T₁.1, h3zornTKKDatum.str_lie_mem T₁.2 T₂.2⟩ =
      ⁅zeroInj ⟨T₁.1, T₁.2⟩, zeroInj ⟨T₂.1, T₂.2⟩⁆
    exact (zeroInj_bracket_zeroInj ⟨T₁.1, T₁.2⟩ ⟨T₂.1, T₂.2⟩).symm

theorem zeroLieHom_injective : Function.Injective zeroLieHom := by
  intro T₁ T₂ h
  apply Subtype.ext
  exact congrArg (fun X => X.zero.1) h

theorem h3zornCubicStabilizer_le_structureOperatorLieSubalgebra :
    h3zornCubicStabilizer ≤ structureOperatorLieSubalgebra := by
  intro T hT
  have h1 : T ∈ h3zornCubicStabilizer.toSubmodule := hT
  rw [h3zornCubicStabilizer_eq_sup] at h1
  have hsup : H3ZornF4Derivations.toSubmodule ⊔ h3zornLmulTraceZeroSubmodule ≤
      structureOperatorLieSubalgebra.toSubmodule := by
    rw [structureOperatorLieSubalgebra_eq_sup]
    refine sup_le le_sup_left ?_
    rintro U ⟨a, _, rfl⟩
    exact Submodule.mem_sup_right (⟨a, rfl⟩ : jordanLmulLinear a ∈ h3zornLmulSubmodule)
  exact hsup h1

/-- Canonical Lie-algebra embedding of the 78D reduced structure algebra `str₀ = E₆(6)`
into `H3ZornTKKLie`. -/
def h3zornCubicStabilizerToTKK : h3zornCubicStabilizer →ₗ⁅ℝ⁆ H3ZornTKKLie :=
  zeroLieHom.comp (LieSubalgebra.inclusion h3zornCubicStabilizer_le_structureOperatorLieSubalgebra)

theorem h3zornCubicStabilizerToTKK_injective :
    Function.Injective h3zornCubicStabilizerToTKK := by
  intro T₁ T₂ h
  apply Subtype.ext
  exact congrArg (fun X => X.zero.1) h

/-- The identity operator `L₁ = id` in `h3zornTKKDatum.str`. -/
def h3zornStrOne : h3zornTKKDatum.str :=
  ⟨structureOperator 0 (1 : H3Zorn ℝ), structureOperator_mem 0 1⟩

theorem h3zornStrOne_coe_eq_id :
    (h3zornStrOne : Module.End ℝ (H3Zorn ℝ)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (0 : H3ZornF4Derivations).1 x + (1 : H3Zorn ℝ) * x = x
  rw [ZeroMemClass.coe_zero, LinearMap.zero_apply, zero_add]
  change candidateJordanMul (1 : H3Zorn ℝ) x = x
  exact candidateJordanMul_one_left x

@[simp] theorem h3zornStrOne_apply (x : H3Zorn ℝ) :
    (h3zornStrOne : Module.End ℝ (H3Zorn ℝ)) x = x := by
  rw [h3zornStrOne_coe_eq_id, LinearMap.id_apply]

theorem h3zornStrOne_not_mem_cubicStabilizer :
    (h3zornStrOne : Module.End ℝ (H3Zorn ℝ)) ∉ h3zornCubicStabilizer := by
  intro hmem
  have h1 : jordanLmul (R := ℝ) (1 : H3Zorn ℝ) ∈ h3zornCubicStabilizer := by
    have heq : (h3zornStrOne : Module.End ℝ (H3Zorn ℝ)) = jordanLmul (R := ℝ) (1 : H3Zorn ℝ) := by
      apply LinearMap.ext
      intro x
      rw [h3zornStrOne_apply, jordanLmul_apply]
      change x = candidateJordanMul 1 x
      exact (candidateJordanMul_one_left x).symm
    rwa [← heq]
  rw [jordanLmul_mem_h3zornCubicStabilizer_iff] at h1
  have htr : linearTrace (1 : H3Zorn ℝ) = 3 := by
    change (1 : ℝ) + 1 + 1 = 3
    norm_num
  rw [htr] at h1
  norm_num at h1

/-- The canonical 3-grading element `H₀ = L₁ = id` inside `H3ZornTKKLie`, with eigenvalues
`+1`, `0`, `-1` on `negInj`, `zeroInj`, `posInj` respectively. -/
def h3zornTKKGradeOp : H3ZornTKKLie :=
  zeroInj h3zornStrOne

@[simp] theorem h3zornTKKGradeOp_bracket_neg (x : H3Zorn ℝ) :
    ⁅h3zornTKKGradeOp, negInj x⁆ = negInj x := by
  simp [h3zornTKKGradeOp]

@[simp] theorem h3zornTKKGradeOp_bracket_pos (y : H3Zorn ℝ) :
    ⁅h3zornTKKGradeOp, posInj y⁆ = -posInj y := by
  rw [h3zornTKKGradeOp, zeroInj_bracket_posInj, h3zornStrOne_coe_eq_id, h3zornTraceAdjoint_id,
    LinearMap.id_apply, map_neg]

@[simp] theorem h3zornTKKGradeOp_bracket_zero (T : h3zornTKKDatum.str) :
    ⁅h3zornTKKGradeOp, zeroInj T⁆ = 0 := by
  rw [h3zornTKKGradeOp, zeroInj_bracket_zeroInj]
  have h0 : (⟨h3zornStrOne.1 ∘ₗ T.1 - T.1 ∘ₗ h3zornStrOne.1,
      h3zornTKKDatum.str_lie_mem h3zornStrOne.2 T.2⟩ : h3zornTKKDatum.str) = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    simp
  rw [h0, map_zero]

private theorem h3zorn_one_ne_zero : (1 : H3Zorn ℝ) ≠ 0 := by
  intro h
  have h1 := congrArg H3Zorn.α₁ h
  change (1 : ℝ) = 0 at h1
  exact one_ne_zero h1

theorem h3zornTKKGradeOp_bracket_neg_one_ne_zero :
    ⁅h3zornTKKGradeOp, negInj (1 : H3Zorn ℝ)⁆ ≠ 0 := by
  rw [h3zornTKKGradeOp_bracket_neg]
  intro h
  exact h3zorn_one_ne_zero (negInj_injective (h.trans (map_zero negInj).symm))

theorem negInj_one_bracket_posInj_one_eq_gradeOp :
    ⁅negInj (1 : H3Zorn ℝ), posInj (1 : H3Zorn ℝ)⁆ = h3zornTKKGradeOp := by
  rw [negInj_bracket_posInj, h3zornTKKGradeOp]
  congr 1
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  rw [JordanTKK.tripleD_apply, JordanTKK.triple, h3zornStrOne_apply]
  have h11 : (1 : H3Zorn ℝ) * 1 = 1 := by
    change candidateJordanMul 1 1 = 1
    exact candidateJordanMul_one_right 1
  have h1z : (1 : H3Zorn ℝ) * z = z := by
    change candidateJordanMul 1 z = z
    exact candidateJordanMul_one_left z
  have hz1 : z * (1 : H3Zorn ℝ) = z := by
    change candidateJordanMul z 1 = z
    exact candidateJordanMul_one_right z
  simp only [h11, h1z, hz1]
  abel

theorem negInj_one_bracket_posInj_one_ne_zero :
    ⁅negInj (1 : H3Zorn ℝ), posInj (1 : H3Zorn ℝ)⁆ ≠ 0 := by
  rw [negInj_one_bracket_posInj_one_eq_gradeOp]
  intro h
  have h1 := congrArg (fun X : H3ZornTKKLie => X.zero.1 1) h
  change h3zornStrOne.1 1 = (0 : Module.End ℝ (H3Zorn ℝ)) 1 at h1
  rw [h3zornStrOne_apply, LinearMap.zero_apply] at h1
  exact h3zorn_one_ne_zero h1

end DownstreamAPI

end InfoGeometry.Canonical.H3ZornTKKLieAlgebra
