/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.SkewGraphNeutralPairing
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Finite matrix coordinates for neutral skew graphs

Mathlib's `dotProductEquiv` identifies a finite real coordinate vector with
its evaluation covector. This file transports the existing neutral pairing
and generic dual-graph theorems through that linear equivalence.

The matrix results hold for every finite index type, including `Fin n`.
They concern linear algebra at a single fiber. A variable skew matrix is
not thereby proved to be a Poisson tensor or an integrable Dirac subbundle.
-/

noncomputable section

namespace InfoGeometry.Geometry.MatrixDiracGraphs

open Matrix
open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Geometry.SkewGraphNeutralPairing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix interpreted as a map from the actual algebraic dual to the primal space. -/
def matrixSharp (P : Matrix ι ι ℝ) :
    Module.Dual ℝ (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (Matrix.toLin' P).comp (dotProductEquiv ℝ ι).symm.toLinearMap

/-- The coordinate-to-covector identification on the second phase-space coordinate. -/
def coordinatePhase : ((ι → ℝ) × (ι → ℝ)) ≃ₗ[ℝ] PhaseSpaceCarrier (ι → ℝ) :=
  (LinearEquiv.refl ℝ (ι → ℝ)).prodCongr (dotProductEquiv ℝ ι)

@[simp] theorem coordinatePhase_apply (v : (ι → ℝ) × (ι → ℝ)) :
    coordinatePhase v = (v.1, dotProductEquiv ℝ ι v.2) := rfl

@[simp] theorem matrixSharp_apply_dotProductEquiv (P : Matrix ι ι ℝ) (ξ : ι → ℝ) :
    matrixSharp P (dotProductEquiv ℝ ι ξ) = P *ᵥ ξ := by
  simp [matrixSharp, Matrix.toLin'_apply]

@[simp] theorem matrixSharp_neg (P : Matrix ι ι ℝ) :
    matrixSharp (-P) = -matrixSharp P := by
  apply LinearMap.ext
  intro ξ
  obtain ⟨a, rfl⟩ := (dotProductEquiv ℝ ι).surjective ξ
  simp only [matrixSharp_apply_dotProductEquiv, LinearMap.neg_apply, Matrix.neg_mulVec]

/-- The original coordinate formula is the pullback of the existing neutral form. -/
theorem coordinatePhase_neutralPair (v w : (ι → ℝ) × (ι → ℝ)) :
    canonicalNeutralBilin (coordinatePhase v) (coordinatePhase w) =
      dotProduct v.1 w.2 + dotProduct w.1 v.2 := by
  rw [canonicalNeutralBilin_apply]
  change dotProduct v.2 w.1 + dotProduct w.2 v.1 =
    dotProduct v.1 w.2 + dotProduct w.1 v.2
  rw [dotProduct_comm v.2 w.1, dotProduct_comm w.2 v.1]
  exact add_comm _ _

/-- Evaluation-skewness of the transported map is exactly matrix skew-symmetry. -/
theorem matrixSharp_skew_iff (P : Matrix ι ι ℝ) :
    (∀ ξ η : Module.Dual ℝ (ι → ℝ), ξ (matrixSharp P η) = -η (matrixSharp P ξ)) ↔
      Pᵀ = -P := by
  constructor
  · intro h
    ext i j
    have hij := h (dotProductEquiv ℝ ι (Pi.single j 1))
      (dotProductEquiv ℝ ι (Pi.single i 1))
    rw [matrixSharp_apply_dotProductEquiv, matrixSharp_apply_dotProductEquiv] at hij
    change dotProduct (Pi.single j 1) (P *ᵥ Pi.single i 1) =
      -dotProduct (Pi.single i 1) (P *ᵥ Pi.single j 1) at hij
    simpa only [single_dotProduct, one_mul, Matrix.mulVec_single_one,
      Matrix.col_apply, Matrix.transpose_apply, Matrix.neg_apply] using hij
  · intro h ξ η
    obtain ⟨a, rfl⟩ := (dotProductEquiv ℝ ι).surjective ξ
    obtain ⟨b, rfl⟩ := (dotProductEquiv ℝ ι).surjective η
    rw [matrixSharp_apply_dotProductEquiv, matrixSharp_apply_dotProductEquiv]
    change dotProduct a (P *ᵥ b) = -dotProduct b (P *ᵥ a)
    rw [← Matrix.dotProduct_transpose_mulVec P b a, h, Matrix.neg_mulVec,
      dotProduct_neg]

@[simp] theorem coordinatePhase_mem_dualGraph_iff
    (P : Matrix ι ι ℝ) (v : (ι → ℝ) × (ι → ℝ)) :
    coordinatePhase v ∈ dualGraph (matrixSharp P) ↔ v.1 = P *ᵥ v.2 := by
  rw [mem_dualGraph]
  simp only [coordinatePhase_apply, matrixSharp_apply_dotProductEquiv]

@[simp] theorem coordinatePhase_mem_neg_dualGraph_iff
    (P : Matrix ι ι ℝ) (v : (ι → ℝ) × (ι → ℝ)) :
    coordinatePhase v ∈ dualGraph (-matrixSharp P) ↔ v.1 = -(P *ᵥ v.2) := by
  rw [mem_dualGraph]
  simp only [coordinatePhase_apply, LinearMap.neg_apply, matrixSharp_apply_dotProductEquiv]

/-- The actual matrix graph submodule is isotropic exactly for a skew matrix. -/
theorem matrix_dualGraph_isotropic_iff (P : Matrix ι ι ℝ) :
    (∀ z ∈ dualGraph (matrixSharp P), ∀ w ∈ dualGraph (matrixSharp P),
      canonicalNeutralBilin z w = 0) ↔ Pᵀ = -P :=
  (dualGraph_isotropic_iff (matrixSharp P)).trans (matrixSharp_skew_iff P)

/-- The same equivalence on all coordinate graph vectors, with the neutral form transported. -/
theorem matrix_graph_vectors_isotropic_iff (P : Matrix ι ι ℝ) :
    (∀ a b : ι → ℝ,
      canonicalNeutralBilin (coordinatePhase (P *ᵥ a, a))
        (coordinatePhase (P *ᵥ b, b)) = 0) ↔ Pᵀ = -P := by
  constructor
  · intro h
    apply (matrix_dualGraph_isotropic_iff P).mp
    intro z hz w hw
    rcases hz with ⟨ξ, rfl⟩
    rcases hw with ⟨η, rfl⟩
    obtain ⟨a, rfl⟩ := (dotProductEquiv ℝ ι).surjective ξ
    obtain ⟨b, rfl⟩ := (dotProductEquiv ℝ ι).surjective η
    simpa only [LinearMap.prod_apply, LinearMap.id_apply,
      matrixSharp_apply_dotProductEquiv, coordinatePhase_apply] using h a b
  · intro h a b
    exact (matrix_dualGraph_isotropic_iff P).mpr h
      (coordinatePhase (P *ᵥ a, a))
      ((coordinatePhase_mem_dualGraph_iff P (P *ᵥ a, a)).mpr rfl)
      (coordinatePhase (P *ᵥ b, b))
      ((coordinatePhase_mem_dualGraph_iff P (P *ᵥ b, b)).mpr rfl)

/-- Skew matrix graphs equal their neutral orthogonals. -/
theorem matrix_dualGraph_orthogonal_eq (P : Matrix ι ι ℝ) (hP : Pᵀ = -P) :
    (dualGraph (matrixSharp P)).orthogonalBilin canonicalNeutralBilin =
      dualGraph (matrixSharp P) :=
  dualGraph_orthogonal_eq (matrixSharp P) ((matrixSharp_skew_iff P).mpr hP)

/-- The opposite graph is also isotropic when the matrix is skew. -/
theorem matrix_neg_graph_isotropic (P : Matrix ι ι ℝ) (hP : Pᵀ = -P)
    (a b : ι → ℝ) :
    canonicalNeutralBilin (coordinatePhase (-(P *ᵥ a), a))
      (coordinatePhase (-(P *ᵥ b), b)) = 0 := by
  exact neg_dualGraph_isotropic (matrixSharp P) ((matrixSharp_skew_iff P).mpr hP)
    (coordinatePhase (-(P *ᵥ a), a))
    ((coordinatePhase_mem_neg_dualGraph_iff P (-(P *ᵥ a), a)).mpr rfl)
    (coordinatePhase (-(P *ᵥ b), b))
    ((coordinatePhase_mem_neg_dualGraph_iff P (-(P *ᵥ b), b)).mpr rfl)

/-- The unscaled neutral pairing of opposite graph vectors has the exact factor two. -/
theorem matrix_graph_cross_pair (P : Matrix ι ι ℝ) (hP : Pᵀ = -P)
    (a b : ι → ℝ) :
    canonicalNeutralBilin (coordinatePhase (P *ᵥ a, a))
      (coordinatePhase (-(P *ᵥ b), b)) = 2 * dotProduct (P *ᵥ a) b := by
  have h := dualGraph_cross_pair (matrixSharp P) ((matrixSharp_skew_iff P).mpr hP)
    (dotProductEquiv ℝ ι a) (dotProductEquiv ℝ ι b)
  rw [dotProduct_comm (P *ᵥ a) b]
  simpa only [coordinatePhase_apply, matrixSharp_apply_dotProductEquiv,
    LinearMap.neg_apply] using h

/-- Matrix graph intersection is exactly the zero primal coordinate over the matrix kernel.
No skewness assumption is needed for this statement. -/
theorem matrix_graph_intersection_iff (P : Matrix ι ι ℝ)
    (v : (ι → ℝ) × (ι → ℝ)) :
    (v.1 = P *ᵥ v.2 ∧ v.1 = -(P *ᵥ v.2)) ↔
      v.1 = 0 ∧ P *ᵥ v.2 = 0 := by
  simpa only [Submodule.mem_inf, coordinatePhase_mem_dualGraph_iff,
    coordinatePhase_mem_neg_dualGraph_iff, coordinatePhase_apply,
    matrixSharp_apply_dotProductEquiv] using
      mem_dualGraph_inf_neg (matrixSharp P) (coordinatePhase v)

end InfoGeometry.Geometry.MatrixDiracGraphs
