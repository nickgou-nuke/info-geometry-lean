/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive
import InfoGeometry.OperatorAlgebra.IsometricCompression

/-!
# Finite Hilbert-space synthesis and multipliers

A finite family of actual Hilbert-space vectors defines a bounded synthesis
map from `EuclideanSpace`. Its adjoint is the analysis map. The native Gram
matrix, the sum of rank-one operators, and weighted multipliers are related
through these maps. No completeness, frame bound, or Parseval identity is
silently assumed of the vector family.

These finite frame results do not construct a Gabor lattice or a Gaussian
window and are not the Fock-space sampling formula of Knutsen's Lemma 5.2.
-/

noncomputable section

open scoped InnerProductSpace
open InnerProductSpace ContinuousLinearMap

namespace InfoGeometry.OperatorAlgebra.FiniteFrameMultipliers

variable {𝕜 ι E : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Synthesis of a finite vector family, with the native Euclidean coefficient norm. -/
def synthesis (φ : ι → E) : EuclideanSpace 𝕜 ι →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (φ i) (EuclideanSpace.basisFun ι 𝕜 i)

/-- Synthesis is the usual finite linear combination of the supplied vectors. -/
theorem synthesis_apply (φ : ι → E) (c : EuclideanSpace 𝕜 ι) :
    synthesis (𝕜 := 𝕜) φ c = ∑ i, c i • φ i := by
  simp [synthesis, EuclideanSpace.basisFun_inner]

/-- The coefficient basis vector synthesizes to its corresponding family member. -/
theorem synthesis_basis (φ : ι → E) (i : ι) :
    synthesis (𝕜 := 𝕜) φ (EuclideanSpace.basisFun ι 𝕜 i) = φ i := by
  classical
  simp [synthesis_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]

variable [CompleteSpace E]

/-- The adjoint synthesis map computes inner-product coefficients. -/
theorem adjoint_synthesis_apply (φ : ι → E) (x : E) (i : ι) :
    (synthesis (𝕜 := 𝕜) φ).adjoint x i = inner 𝕜 (φ i) x := by
  rw [← EuclideanSpace.basisFun_inner, adjoint_inner_right, synthesis_basis]

/-- The frame operator is the sum of the genuine rank-one operators. -/
theorem synthesis_comp_adjoint (φ : ι → E) :
    (synthesis (𝕜 := 𝕜) φ).comp (synthesis (𝕜 := 𝕜) φ).adjoint = ∑ i, rankOne 𝕜 (φ i) (φ i) := by
  ext x
  simp [synthesis_apply, adjoint_synthesis_apply]

/-- Gram multiplication is the coefficient-space analysis-after-synthesis map. -/
theorem adjoint_comp_synthesis_apply (φ : ι → E)
    (c : EuclideanSpace 𝕜 ι) (i : ι) :
    ((synthesis (𝕜 := 𝕜) φ).adjoint.comp (synthesis (𝕜 := 𝕜) φ)) c i =
      ∑ j, Matrix.gram 𝕜 φ i j * c j := by
  simp [adjoint_synthesis_apply, synthesis_apply, Matrix.gram_apply, mul_comm]

/-- Squaring the native Gram matrix inserts the actual frame operator. -/
theorem gram_mul_gram (φ : ι → E) (i j : ι) :
    (Matrix.gram 𝕜 φ * Matrix.gram 𝕜 φ) i j =
      inner 𝕜 (φ i) (((synthesis (𝕜 := 𝕜) φ).comp (synthesis (𝕜 := 𝕜) φ).adjoint) (φ j)) := by
  simp [Matrix.mul_apply, Matrix.gram_apply, synthesis_apply,
    adjoint_synthesis_apply, inner_sum, inner_smul_right, mul_comm]

/-- A Parseval family has an idempotent native Gram matrix. Its Hermitian
property is already supplied by `Matrix.isHermitian_gram`. -/
theorem gram_idempotent_of_parseval (φ : ι → E)
    (hφ : (synthesis (𝕜 := 𝕜) φ).comp (synthesis (𝕜 := 𝕜) φ).adjoint = 1) :
    Matrix.gram 𝕜 φ * Matrix.gram 𝕜 φ = Matrix.gram 𝕜 φ := by
  ext i j
  rw [gram_mul_gram, hφ]
  rfl

/-- Parseval analysis is a native linear isometry, constructed from the
frame identity rather than supplied as a separate assumption. -/
def analysisIsometry (φ : ι → E)
    (hφ : (synthesis (𝕜 := 𝕜) φ).comp (synthesis (𝕜 := 𝕜) φ).adjoint = 1) :
    E →ₗᵢ[𝕜] EuclideanSpace 𝕜 ι where
  toLinearMap := (synthesis (𝕜 := 𝕜) φ).adjoint.toLinearMap
  norm_map' := by
    apply (synthesis (𝕜 := 𝕜) φ).adjoint.norm_map_iff_adjoint_comp_self.mpr
    simpa using hφ

/-- The Gram operator of a Parseval family is an orthogonal projection on
coefficient space, even when the finite family is redundant. -/
theorem gram_operator_isStarProjection (φ : ι → E)
    (hφ : (synthesis (𝕜 := 𝕜) φ).comp (synthesis (𝕜 := 𝕜) φ).adjoint = 1) :
    IsStarProjection ((synthesis (𝕜 := 𝕜) φ).adjoint.comp (synthesis (𝕜 := 𝕜) φ)) := by
  constructor
  · change ((synthesis (𝕜 := 𝕜) φ).adjoint.comp (synthesis (𝕜 := 𝕜) φ)).comp
        ((synthesis (𝕜 := 𝕜) φ).adjoint.comp (synthesis (𝕜 := 𝕜) φ)) = _
    calc
      _ = (synthesis (𝕜 := 𝕜) φ).adjoint.comp
          (((synthesis (𝕜 := 𝕜) φ).comp (synthesis (𝕜 := 𝕜) φ).adjoint).comp (synthesis (𝕜 := 𝕜) φ)) := by
            simp only [comp_assoc]
      _ = _ := by rw [hφ]; simp [one_def]
  · change ((synthesis (𝕜 := 𝕜) φ).adjoint.comp (synthesis (𝕜 := 𝕜) φ)).adjoint = _
    simp [adjoint_comp]

/-- A scalar-weighted finite rank-one multiplier. -/
def multiplier (φ : ι → E) (b : ι → 𝕜) : E →L[𝕜] E :=
  ∑ i, b i • rankOne 𝕜 (φ i) (φ i)

/-- Adjoining the multiplier conjugates its scalar weights. -/
theorem adjoint_multiplier (φ : ι → E) (b : ι → 𝕜) :
    (multiplier φ b).adjoint = multiplier φ (fun i => star (b i)) := by
  simp [multiplier, map_smulₛₗ]

/-- A mask and its complementary weights partition the full frame operator. -/
theorem multiplier_add_complement (φ : ι → E) (b : ι → 𝕜) :
    multiplier φ b + multiplier φ (fun i => 1 - b i) =
      (synthesis (𝕜 := 𝕜) φ).comp (synthesis (𝕜 := 𝕜) φ).adjoint := by
  rw [synthesis_comp_adjoint]
  simp only [multiplier, ← Finset.sum_add_distrib, ← add_smul]
  simp

/-- Transporting a coefficient-space multiplier through synthesis gives the
corresponding multiplier of the vector family. -/
theorem multiplier_eq_synthesis_comp (φ : ι → E) (b : ι → 𝕜) :
    multiplier φ b = (synthesis (𝕜 := 𝕜) φ).comp
      ((multiplier (EuclideanSpace.basisFun ι 𝕜) b).comp (synthesis (𝕜 := 𝕜) φ).adjoint) := by
  simp only [multiplier, comp_finsetSum, finsetSum_comp, comp_smul, smul_comp,
    rankOne_comp, adjoint_adjoint, comp_rankOne, synthesis_basis]

omit [CompleteSpace E] in
/-- Nonnegative real weights give a positive operator on the actual Hilbert space. -/
theorem multiplier_isPositive (φ : ι → E) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    (multiplier φ (fun i => (b i : 𝕜))).IsPositive := by
  apply isPositive_sum
  intro i _
  exact (isPositive_rankOne_self (φ i)).smul_of_nonneg
    (by simpa only [RCLike.ofReal_nonneg] using hb i)

/-- For a Parseval family, the multiplier is the isometric compression of
the diagonal coefficient operator through the constructed analysis isometry. -/
theorem multiplier_eq_compress (φ : ι → E) (b : ι → 𝕜)
    (hφ : (synthesis (𝕜 := 𝕜) φ).comp (synthesis (𝕜 := 𝕜) φ).adjoint = 1) :
    multiplier φ b = IsometricCompression.compress (analysisIsometry φ hφ)
      (multiplier (EuclideanSpace.basisFun ι 𝕜) b) := by
  have hV : (analysisIsometry φ hφ).toContinuousLinearMap =
      (synthesis (𝕜 := 𝕜) φ).adjoint := by
    ext x
    rfl
  simp only [IsometricCompression.compress, hV, adjoint_adjoint]
  exact multiplier_eq_synthesis_comp φ b

/-- A basis multiplier acts by coordinatewise multiplication. -/
theorem multiplier_basis_apply (b : ι → 𝕜) (c : EuclideanSpace 𝕜 ι) (i : ι) :
    multiplier (EuclideanSpace.basisFun ι 𝕜) b c i = b i * c i := by
  classical
  simp [multiplier, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
    Pi.single_apply]

/-- Selecting a finite set of coefficient indices gives an actual orthogonal
projection. No metric or geometric porosity is attached to this finite mask. -/
theorem indicator_multiplier_isStarProjection [DecidableEq ι] (s : Finset ι) :
    IsStarProjection (multiplier (𝕜 := 𝕜) (EuclideanSpace.basisFun ι 𝕜)
      (fun i => if i ∈ s then 1 else 0)) := by
  classical
  constructor
  · ext c i
    change multiplier (𝕜 := 𝕜) (EuclideanSpace.basisFun ι 𝕜)
        (fun j => if j ∈ s then 1 else 0)
        (multiplier (EuclideanSpace.basisFun ι 𝕜)
          (fun j => if j ∈ s then 1 else 0) c) i = _
    simp only [multiplier_basis_apply]
    split_ifs <;> simp
  · change (multiplier (EuclideanSpace.basisFun ι 𝕜)
        (fun i => if i ∈ s then 1 else 0)).adjoint = _
    rw [adjoint_multiplier]
    simp

end InfoGeometry.OperatorAlgebra.FiniteFrameMultipliers
