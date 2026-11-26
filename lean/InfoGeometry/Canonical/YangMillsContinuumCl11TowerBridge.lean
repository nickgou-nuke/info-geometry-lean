/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.DoubledMinkowskiLatticeContinuumLimit
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.Cl55WittCAR
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic

/-!
# Smooth Yang–Mills Continuum Limit to the Graded `Cl(1,1)` Tensor-Tower Carrier Bridge

Constructs explicit typed carrier maps identifying the smooth `C²` Yang–Mills differential-form
geometry and lattice `a → 0` continuum limits of `DoubledMinkowskiLatticeContinuumLimit`
(`Mat4C`, `latticeCovariantDiff`, `wilsonPlaquette`, `continuumCovariantDeriv`,
`continuumCurvature`, `continuumPlaquetteAction`) with the graded tensor-product tower
`Cl11TensorTower.MatStage n` of `2 × 2` real chiral spin matrices and its infinite direct limit
`Cl11TensorTowerLimit.Limit`:

1. **Faithful Complex-to-Real Matrix Realification (`ymRealifyHom : Mat4C →ₐ[ℝ] MatStage 3`)**:
   Maps each `4 × 4` complex two-sheet Yang–Mills matrix `M` to
   `mat4RealPart M ⊗ₖ I₂ + mat4ImagPart M ⊗ₖ bivector_J_base` in `M₂(ℝ)^{⊗3}`, proving
   injectivity, star/transpose compatibility, continuity, exact Hilbert–Schmidt action trace
   readout `(1 / 2) Tr((ymRealifyHom F)ᵀ (ymRealifyHom F)) = Re Tr(Fᴴ F)`, and idempotent
   self-adjoint transport of `chiralProjMat4`.
2. **Canonical Differential-Form Identification (`exteriorFormToCl11Stage4`)**:
   Maps `ExteriorAlgebra ℝ (Fin 4 → ℝ)` algebraically onto `MatStage 4` via `jwCreation 4 μ`
   using `Cl55WittCAR.creation_sq` and `Cl55WittCAR.creation_cross_site_anticommute`, proving
   non-vanishing of the top 4-form volume wedge `dx 0 * dx 1 * dx 2 * dx 3` and exact `ℤ₂`
   grading under `globalChirality 4` (1-forms are odd, 2-forms are even).
3. **Graded `MatStage 7` & Direct-Limit `Cl11TensorTowerLimit.Limit` Yang–Mills Carrier Maps**:
   Maps `A_μ dx^μ ↦ ymConnectionFormToTower A y : MatStage 7`,
   `F_{μν} dx^μ ∧ dx^ν ↦ ymCurvatureFormToTower A y : MatStage 7`, and the lattice Wilson
   plaquette difference quotient `wilsonPlaquetteFormToTower A y a : MatStage 7`, proving:
   - Wedge square `𝒜 ∧ 𝒜` matches the graded Yang–Mills commutator 2-form;
   - `formChirality7` renders connection 1-forms odd and curvature 2-forms even;
   - Exact `a → 0` (`𝓝[≠] 0`) convergence of covariant differences, Wilson plaquette 2-forms, and
     Hilbert–Schmidt action inside `MatStage 3` and `MatStage 7`;
   - Injective transport into `Cl11TensorTowerLimit.Limit` preserving bonding compatibility and
     the non-Abelian continuum curvature witness.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & ANALYTIC THEOREMS
* `exists_noncomm_mat4c_ym_tower`, `exists_noncomm_matStage3_ym_tower`,
  `exists_noncomm_matStage4_ym_tower`, `exists_noncomm_matStage7_ym_tower`
* `ymRealifyHom_properties`, `exteriorFormToCl11Stage4_properties`
* `ymConnectionFormToTower_sq_eq_commutator_twoForm`, `ymFormToTower_chiral_grading`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `tendsto_lattice_yang_mills_in_cl11_tower` (under `ContDiff ℝ 2 A` and `DifferentiableAt ℝ Φ y`)
* `ym_smooth_lattice_continuum_to_cl11_direct_limit` (packaging continuum-limit + direct-limit
  bonding compatibility and concrete non-Abelian witness transport)

#### BUCKET 3: OPEN CLOSURE DEBT
* Non-perturbative 4D quantum Yang–Mills measure existence and continuum mass gap remain open
  beyond this classical `C²` lattice-continuum and algebraic `Cl(1,1)` tower identification.
-/

set_option autoImplicit false

noncomputable section

open scoped _root_.Topology BigOperators Kronecker Matrix.Norms.Operator
open Matrix Filter

namespace InfoGeometry.Canonical.YangMillsContinuumCl11TowerBridge

open InfoGeometry.Lie
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Clifford
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR
open InfoGeometry.Canonical.Cl11TensorTowerGlobalParity
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- Explicit non-commutativity witness on `Mat4C`. -/
theorem exists_noncomm_mat4c_ym_tower : ∃ A B : Mat4C, A * B ≠ B * A :=
  circularConnectionMat4_mat4C_noncomm_witness

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem exists_noncomm_mat2_ym_tower :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨gamma_0_base, gamma_1_base, fun h => ?_⟩
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [gamma_0_base, gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

private lemma exists_noncomm_matStage_succ (k : ℕ) :
    ∃ A B : MatStage (k + 1), A * B ≠ B * A := by
  refine ⟨((1 : MatStage k) ⊗ₖ gamma_0_base : MatStage (k + 1)),
    ((1 : MatStage k) ⊗ₖ gamma_1_base : MatStage (k + 1)), fun h => ?_⟩
  change ((1 : MatStage k) ⊗ₖ gamma_0_base) * ((1 : MatStage k) ⊗ₖ gamma_1_base) =
    ((1 : MatStage k) ⊗ₖ gamma_1_base) * ((1 : MatStage k) ⊗ₖ gamma_0_base) at h
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul] at h
  have h00 := congrArg (fun M : Matrix (Idx k × Fin 2) (Idx k × Fin 2) ℝ =>
    M (default, (0 : Fin 2)) (default, (0 : Fin 2))) h
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul] at h00
  norm_num [gamma_0_base, gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus,
    Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Explicit non-commutativity witness on `MatStage 3`. -/
theorem exists_noncomm_matStage3_ym_tower : ∃ A B : MatStage 3, A * B ≠ B * A :=
  exists_noncomm_matStage_succ 2

/-- Explicit non-commutativity witness on `MatStage 4`. -/
theorem exists_noncomm_matStage4_ym_tower : ∃ A B : MatStage 4, A * B ≠ B * A :=
  exists_noncomm_matStage_succ 3

/-- Explicit non-commutativity witness on `MatStage 7`. -/
theorem exists_noncomm_matStage7_ym_tower : ∃ A B : MatStage 7, A * B ≠ B * A :=
  exists_noncomm_matStage_succ 6

/-! ### Part 1: Faithful `Mat4C →ₐ[ℝ] MatStage 3` Realification & Action Trace Readout -/

/-- Canonical index equivalence `TowerMatrix.Idx 2 ≃ Fin 4`. -/
def idx2EquivFin4 : TowerMatrix.Idx 2 ≃ Fin 4 where
  toFun p := ⟨2 * p.1.2.val + p.2.val, by omega⟩
  invFun i := ((default, ⟨i.val / 2, by omega⟩), ⟨i.val % 2, by omega⟩)
  left_inv p := by
    rcases p with ⟨⟨i0, i1⟩, i2⟩
    exact Prod.ext (Prod.ext (Subsingleton.elim i0 default).symm (Fin.ext (by dsimp; omega)))
      (Fin.ext (by dsimp; omega))
  right_inv i := Fin.ext (by dsimp; omega)

/-- Real `MatStage 2` coordinate slice of a `4 × 4` complex matrix `M : Mat4C`. -/
def mat4RealPart (M : Mat4C) : MatStage 2 :=
  fun i j => (M (idx2EquivFin4 i) (idx2EquivFin4 j)).re

/-- Imaginary `MatStage 2` coordinate slice of a `4 × 4` complex matrix `M : Mat4C`. -/
def mat4ImagPart (M : Mat4C) : MatStage 2 :=
  fun i j => (M (idx2EquivFin4 i) (idx2EquivFin4 j)).im

/-- Realification of `M : Mat4C` into `MatStage 3` using `bivector_J_base` (`J² = -I₂`). -/
def ymRealify (M : Mat4C) : MatStage 3 :=
  mat4RealPart M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + mat4ImagPart M ⊗ₖ bivector_J_base

private lemma bivector_J_base_transpose : bivector_J_baseᵀ = -bivector_J_base := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bivector_J_base]

private lemma bivector_J_base_trace : Matrix.trace bivector_J_base = 0 := by
  simp [bivector_J_base, Matrix.trace, Matrix.diag]

private lemma kron_neg_right_real {α β : Type*} (A : Matrix α α ℝ) (B : Matrix β β ℝ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kron_neg_left_real {α β : Type*} (A : Matrix α α ℝ) (B : Matrix β β ℝ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply]

private lemma kron_sub_left_real {α β : Type*} (A₁ A₂ : Matrix α α ℝ) (B : Matrix β β ℝ) :
    (A₁ - A₂) ⊗ₖ B = A₁ ⊗ₖ B - A₂ ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.kroneckerMap_apply, sub_mul]

private lemma matStage_kron_apply {n : ℕ} (A : MatStage n) (B : Matrix (Fin 2) (Fin 2) ℝ)
    (i j : Idx n) (a b : Fin 2) :
    ((A ⊗ₖ B : MatStage (n + 1)) (i, a) (j, b)) = A i j * B a b := rfl

private lemma matStage0_one_apply (i j : Idx 0) :
    (1 : MatStage 0) i j = 1 := by
  rw [Subsingleton.elim i j, Matrix.one_apply_eq]

private lemma kron_transpose_real {α β : Type*} (A : Matrix α α ℝ) (B : Matrix β β ℝ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; rfl

private lemma mat4RealPart_one : mat4RealPart (1 : Mat4C) = (1 : MatStage 2) := by
  ext i j
  dsimp [mat4RealPart]
  simp only [Matrix.one_apply, idx2EquivFin4.apply_eq_iff_eq]
  split_ifs <;> simp

private lemma mat4ImagPart_one : mat4ImagPart (1 : Mat4C) = (0 : MatStage 2) := by
  ext i j
  dsimp [mat4ImagPart]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

private lemma mat4RealPart_mul (M₁ M₂ : Mat4C) :
    mat4RealPart (M₁ * M₂) = mat4RealPart M₁ * mat4RealPart M₂ - mat4ImagPart M₁ * mat4ImagPart M₂ := by
  ext i j
  simp only [mat4RealPart, mat4ImagPart, Matrix.sub_apply, Matrix.mul_apply, Complex.re_sum,
    Complex.mul_re]
  rw [← Equiv.sum_comp idx2EquivFin4 (fun k => (M₁ (idx2EquivFin4 i) k).re * (M₂ k (idx2EquivFin4 j)).re -
      (M₁ (idx2EquivFin4 i) k).im * (M₂ k (idx2EquivFin4 j)).im)]
  rw [Finset.sum_sub_distrib]

private lemma mat4ImagPart_mul (M₁ M₂ : Mat4C) :
    mat4ImagPart (M₁ * M₂) = mat4RealPart M₁ * mat4ImagPart M₂ + mat4ImagPart M₁ * mat4RealPart M₂ := by
  ext i j
  simp only [mat4RealPart, mat4ImagPart, Matrix.add_apply, Matrix.mul_apply, Complex.im_sum,
    Complex.mul_im]
  rw [← Equiv.sum_comp idx2EquivFin4 (fun k => (M₁ (idx2EquivFin4 i) k).re * (M₂ k (idx2EquivFin4 j)).im +
      (M₁ (idx2EquivFin4 i) k).im * (M₂ k (idx2EquivFin4 j)).re)]
  rw [Finset.sum_add_distrib]

/-- Faithful unital `ℝ`-algebra homomorphism `Mat4C →ₐ[ℝ] MatStage 3` realized inside `M₂(ℝ)^{⊗3}`. -/
def ymRealifyHom : Mat4C →ₐ[ℝ] MatStage 3 where
  toFun := ymRealify
  map_one' := by
    simp [ymRealify, mat4RealPart_one, mat4ImagPart_one, Matrix.one_kronecker_one]
    rfl
  map_mul' M₁ M₂ := by
    change ((mat4RealPart (M₁ * M₂) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        mat4ImagPart (M₁ * M₂) ⊗ₖ bivector_J_base : Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ)) =
      ((mat4RealPart M₁ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        mat4ImagPart M₁ ⊗ₖ bivector_J_base : Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ)) *
      ((mat4RealPart M₂ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        mat4ImagPart M₂ ⊗ₖ bivector_J_base : Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ))
    rw [mat4RealPart_mul, mat4ImagPart_mul, kron_sub_left_real, Matrix.add_kronecker,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      bivector_J_base_sq, kron_neg_right_real]
    abel
  map_zero' := by
    have hR0 : mat4RealPart 0 = 0 := rfl
    have hI0 : mat4ImagPart 0 = 0 := rfl
    change (mat4RealPart 0 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      mat4ImagPart 0 ⊗ₖ bivector_J_base : Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ) = 0
    rw [hR0, hI0, Matrix.zero_kronecker, Matrix.zero_kronecker, add_zero]
  map_add' M₁ M₂ := by
    have hR : mat4RealPart (M₁ + M₂) = mat4RealPart M₁ + mat4RealPart M₂ := by
      ext i j; simp [mat4RealPart]
    have hI : mat4ImagPart (M₁ + M₂) = mat4ImagPart M₁ + mat4ImagPart M₂ := by
      ext i j; simp [mat4ImagPart]
    simp only [ymRealify, hR, hI, Matrix.add_kronecker]
    abel
  commutes' r := by
    have hrR : mat4RealPart (algebraMap ℝ Mat4C r) = r • (1 : MatStage 2) := by
      ext i j
      simp only [mat4RealPart, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply,
        Complex.real_smul, idx2EquivFin4.apply_eq_iff_eq]
      split_ifs <;> simp
    have hrI : mat4ImagPart (algebraMap ℝ Mat4C r) = 0 := by
      ext i j
      simp only [mat4ImagPart, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply,
        Complex.real_smul]
      split_ifs <;> simp
    have hAlg3 : (algebraMap ℝ (MatStage 3)) r = r • (1 : MatStage 3) :=
      Algebra.algebraMap_eq_smul_one r
    rw [hAlg3]
    change (mat4RealPart (algebraMap ℝ Mat4C r) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      mat4ImagPart (algebraMap ℝ Mat4C r) ⊗ₖ bivector_J_base :
        Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ) =
      (r • (1 : Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ))
    rw [hrR, hrI, Matrix.zero_kronecker, add_zero]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Prod.ext_iff]
    by_cases hi : i1 = j1 <;> by_cases hj : i2 = j2 <;> simp [hi, hj]

private lemma continuous_mat4C_entry (p q : Fin 4) : Continuous (fun M : Mat4C => M p q) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun M N => ?_).continuous
  have hDist : dist (M p q) (N p q) ≤ dist M N := by
    rw [dist_eq_norm, dist_eq_norm, ← Matrix.sub_apply]
    have h1 : ‖(M - N) p q‖₊ ≤ ∑ k : Fin 4, ‖(M - N) p k‖₊ :=
      Finset.single_le_sum (f := fun k : Fin 4 => ‖(M - N) p k‖₊)
        (fun _ _ => zero_le) (Finset.mem_univ q)
    have h2 : (∑ k : Fin 4, ‖(M - N) p k‖₊) ≤ ‖M - N‖₊ := by
      rw [Matrix.linfty_opNNNorm_def]
      exact Finset.le_sup (f := fun r : Fin 4 => ∑ k : Fin 4, ‖(M - N) r k‖₊) (Finset.mem_univ p)
    exact_mod_cast h1.trans h2
  simpa using hDist

private lemma scalar_hs_trace_half (x y : ℝ) :
    (1 / 2 : ℝ) * (2 * x + 2 * y) = x + y := by
  ring

private lemma scalar_complex_norm_sq_re_im (z : ℂ) :
    z.re * z.re + z.im * z.im = (star z * z).re := by
  simp [Complex.mul_re]

/-- **Theorem 1 (`ymRealifyHom` Faithfulness, Adjoint, Continuity, HS Action, & Chiral Projector)**:
1. `ymRealifyHom : Mat4C →ₐ[ℝ] MatStage 3` is injective and continuous.
2. Hermitian adjoint maps to real transpose: `(ymRealifyHom M)ᵀ = ymRealifyHom Mᴴ`.
3. Exact Hilbert–Schmidt action trace correspondence:
   `(1 / 2) * Tr((ymRealifyHom F)ᵀ * ymRealifyHom F) = Re Tr(Fᴴ * F)`.
4. `P_real := ymRealifyHom chiralProjMat4` is a real self-adjoint idempotent (`P² = P`, `Pᵀ = P`). -/
theorem ymRealifyHom_properties (M F : Mat4C) :
    Function.Injective ymRealifyHom ∧
    Continuous (fun X : Mat4C => ymRealifyHom X) ∧
    ((ymRealifyHom M)ᵀ = ymRealifyHom Mᴴ) ∧
    ((1 / 2 : ℝ) * Matrix.trace ((ymRealifyHom F)ᵀ * ymRealifyHom F) = ((Fᴴ * F).trace).re) ∧
    (ymRealifyHom chiralProjMat4 * ymRealifyHom chiralProjMat4 = ymRealifyHom chiralProjMat4 ∧
      (ymRealifyHom chiralProjMat4)ᵀ = ymRealifyHom chiralProjMat4) := by
  have hInj : Function.Injective ymRealifyHom := by
    intro A B h
    ext p q
    have hRe0 := congrArg (fun X : MatStage 3 => X (idx2EquivFin4.symm p, 0) (idx2EquivFin4.symm q, 0)) h
    have hIm0 := congrArg (fun X : MatStage 3 => X (idx2EquivFin4.symm p, 0) (idx2EquivFin4.symm q, 1)) h
    have hRe0' : ymRealify A (idx2EquivFin4.symm p, 0) (idx2EquivFin4.symm q, 0) =
        ymRealify B (idx2EquivFin4.symm p, 0) (idx2EquivFin4.symm q, 0) := hRe0
    have hIm0' : ymRealify A (idx2EquivFin4.symm p, 0) (idx2EquivFin4.symm q, 1) =
        ymRealify B (idx2EquivFin4.symm p, 0) (idx2EquivFin4.symm q, 1) := hIm0
    unfold ymRealify mat4RealPart mat4ImagPart at hRe0' hIm0'
    simp only [Matrix.add_apply, Matrix.kroneckerMap, Equiv.apply_symm_apply, bivector_J_base,
      Matrix.one_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte,
      mul_one, mul_zero, add_zero, zero_add] at hRe0' hIm0'
    exact Complex.ext hRe0' hIm0'
  have hCont : Continuous (fun X : Mat4C => ymRealifyHom X) := by
    refine continuous_pi fun ⟨i₁, i₂⟩ => continuous_pi fun ⟨j₁, j₂⟩ => ?_
    dsimp [ymRealifyHom, ymRealify, mat4RealPart, mat4ImagPart]
    exact ((Complex.continuous_re.comp (continuous_mat4C_entry _ _)).mul continuous_const).add
      ((Complex.continuous_im.comp (continuous_mat4C_entry _ _)).mul continuous_const)
  have hAdj : ∀ X : Mat4C, (ymRealifyHom X)ᵀ = ymRealifyHom Xᴴ := by
    intro X
    have hRe : (mat4RealPart X)ᵀ = mat4RealPart Xᴴ := by
      ext i j; simp [mat4RealPart, Matrix.conjTranspose_apply]
    have hIm : -(mat4ImagPart X)ᵀ = mat4ImagPart Xᴴ := by
      ext i j; simp [mat4ImagPart, Matrix.conjTranspose_apply]
    change (mat4RealPart X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + mat4ImagPart X ⊗ₖ bivector_J_base)ᵀ =
      mat4RealPart Xᴴ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + mat4ImagPart Xᴴ ⊗ₖ bivector_J_base
    rw [Matrix.transpose_add, kron_transpose_real, kron_transpose_real, Matrix.transpose_one,
      bivector_J_base_transpose, hRe, kron_neg_right_real, ← kron_neg_left_real, hIm]
  have hHS : (1 / 2 : ℝ) * Matrix.trace ((ymRealifyHom F)ᵀ * ymRealifyHom F) = ((Fᴴ * F).trace).re := by
    have hMat : ((ymRealifyHom F)ᵀ * ymRealifyHom F : MatStage 3) =
        ((mat4RealPart F)ᵀ * mat4RealPart F) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ((mat4RealPart F)ᵀ * mat4ImagPart F) ⊗ₖ bivector_J_base +
        ((mat4ImagPart F)ᵀ * mat4RealPart F) ⊗ₖ (-bivector_J_base) +
        ((mat4ImagPart F)ᵀ * mat4ImagPart F) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      change (mat4RealPart F ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + mat4ImagPart F ⊗ₖ bivector_J_base :
          Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ)ᵀ *
          (mat4RealPart F ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) + mat4ImagPart F ⊗ₖ bivector_J_base :
            Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ) = _
      rw [Matrix.transpose_add, kron_transpose_real, kron_transpose_real, Matrix.transpose_one,
        bivector_J_base_transpose, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
        Matrix.neg_mul, bivector_J_base_sq, neg_neg, kron_neg_right_real]
      abel
    have hTrNegJ : Matrix.trace (-bivector_J_base) = 0 := by
      rw [Matrix.trace_neg, bivector_J_base_trace, neg_zero]
    have hTrMat : Matrix.trace ((ymRealifyHom F)ᵀ * ymRealifyHom F) =
        Matrix.trace ((mat4RealPart F)ᵀ * mat4RealPart F) * 2 +
        Matrix.trace ((mat4ImagPart F)ᵀ * mat4ImagPart F) * 2 := by
      rw [hMat]
      change Matrix.trace (((mat4RealPart F)ᵀ * mat4RealPart F) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ((mat4RealPart F)ᵀ * mat4ImagPart F) ⊗ₖ bivector_J_base +
        ((mat4ImagPart F)ᵀ * mat4RealPart F) ⊗ₖ (-bivector_J_base) +
        ((mat4ImagPart F)ᵀ * mat4ImagPart F) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) :
          Matrix (Idx 2 × Fin 2) (Idx 2 × Fin 2) ℝ) = _
      rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
        Matrix.trace_kronecker, Matrix.trace_kronecker, Matrix.trace_kronecker, Matrix.trace_kronecker,
        trace_fin_two_one, bivector_J_base_trace, hTrNegJ, mul_zero, mul_zero, add_zero, add_zero]
    rw [hTrMat, mul_comm _ (2 : ℝ), mul_comm _ (2 : ℝ), scalar_hs_trace_half]
    have hReSum : Matrix.trace ((mat4RealPart F)ᵀ * mat4RealPart F) +
        Matrix.trace ((mat4ImagPart F)ᵀ * mat4ImagPart F) = ((Fᴴ * F).trace).re := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
        mat4RealPart, mat4ImagPart, Matrix.conjTranspose_apply, Complex.re_sum, ← Finset.sum_add_distrib]
      rw [Equiv.sum_comp idx2EquivFin4 (fun i : Fin 4 =>
        ∑ j : Idx 2, ((F (idx2EquivFin4 j) i).re * (F (idx2EquivFin4 j) i).re +
          (F (idx2EquivFin4 j) i).im * (F (idx2EquivFin4 j) i).im))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Equiv.sum_comp idx2EquivFin4 (fun j : Fin 4 =>
        (F j i).re * (F j i).re + (F j i).im * (F j i).im)]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact scalar_complex_norm_sq_re_im (F j i)
    exact hReSum
  have hProj : ymRealifyHom chiralProjMat4 * ymRealifyHom chiralProjMat4 = ymRealifyHom chiralProjMat4 ∧
      (ymRealifyHom chiralProjMat4)ᵀ = ymRealifyHom chiralProjMat4 := by
    refine ⟨?_, ?_⟩
    · rw [← map_mul, chiralProjMat4_idempotent]
    · rw [hAdj chiralProjMat4]
      change ymRealifyHom (star chiralProjMat4) = ymRealifyHom chiralProjMat4
      rw [chiralProjMat4_star]
  exact ⟨hInj, hCont, hAdj M, hHS, hProj⟩

/-! ### Part 2: Canonical Exterior Differential-Form Identification (`ExteriorAlgebra →ₐ[ℝ] MatStage 4`) -/

/-- Real exterior 1-form covector generator `dx μ := ι (Pi.single μ 1)` in `ExteriorAlgebra ℝ (Fin 4 → ℝ)`. -/
def dx (μ : Fin 4) : ExteriorAlgebra ℝ (Fin 4 → ℝ) :=
  ExteriorAlgebra.ι ℝ (Pi.single μ (1 : ℝ))

/-- `ℝ`-linear map `v ↦ ∑ μ, v μ • jwCreation 4 μ` into `MatStage 4`. -/
def formOneLinear : (Fin 4 → ℝ) →ₗ[ℝ] MatStage 4 where
  toFun v := ∑ μ : Fin 4, v μ • jwCreation 4 μ
  map_add' u v := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

theorem formOneLinear_sq_zero (v : Fin 4 → ℝ) :
    formOneLinear v * formOneLinear v = 0 := by
  dsimp [formOneLinear]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hPair : (∑ μ : Fin 4, ∑ ν : Fin 4, (v μ * v ν) • (jwCreation 4 μ * jwCreation 4 ν)) +
      (∑ μ : Fin 4, ∑ ν : Fin 4, (v μ * v ν) • (jwCreation 4 μ * jwCreation 4 ν)) = 0 := by
    conv_lhs =>
      rhs
      rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun μ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun ν _ => ?_
    by_cases h : μ = ν
    · subst h
      rw [Cl55WittCAR.creation_sq 4 μ, smul_zero, add_zero]
    · have hAnti : jwCreation 4 ν * jwCreation 4 μ = -(jwCreation 4 μ * jwCreation 4 ν) :=
        eq_neg_of_add_eq_zero_right (Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute 4 μ ν h)
      rw [mul_comm (v ν) (v μ), hAnti, smul_neg, add_neg_cancel]
  have h2 : (2 : ℝ) • (∑ μ : Fin 4, ∑ ν : Fin 4, (v μ * v ν) • (jwCreation 4 μ * jwCreation 4 ν)) = 0 := by
    rwa [two_smul]
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Algebra isomorphism/embedding of 4D differential forms `ExteriorAlgebra ℝ (Fin 4 → ℝ)`
into the graded `2 × 2` Clifford spin-tower matrix algebra `MatStage 4`. -/
def exteriorFormToCl11Stage4 : ExteriorAlgebra ℝ (Fin 4 → ℝ) →ₐ[ℝ] MatStage 4 :=
  ExteriorAlgebra.lift ℝ ⟨formOneLinear, formOneLinear_sq_zero⟩

private lemma exteriorFormToCl11Stage4_dx (μ : Fin 4) :
    exteriorFormToCl11Stage4 (dx μ) = jwCreation 4 μ := by
  dsimp [exteriorFormToCl11Stage4, dx]
  rw [ExteriorAlgebra.lift_ι_apply]
  simp only [formOneLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro ν _ hne
    simp [Pi.single_apply, hne]
  · simp

private lemma jwCreation_4_0_apply (r0 c0 : Idx 0) (rb0 rb1 rb2 rb3 cb0 cb1 cb2 cb3 : Fin 2) :
    jwCreation 4 0 ((((r0, rb0), rb1), rb2), rb3) ((((c0, cb0), cb1), cb2), cb3) =
      wittCreationBase rb0 cb0 *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) rb1 cb1 *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) rb2 cb2 *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) rb3 cb3 := by
  dsimp [jwCreation, jwStringWithBase, globalChirality, kronPow, Matrix.kroneckerMap]
  rw [matStage0_one_apply, one_mul]

private lemma jwCreation_4_1_apply (r0 c0 : Idx 0) (rb0 rb1 rb2 rb3 cb0 cb1 cb2 cb3 : Fin 2) :
    jwCreation 4 1 ((((r0, rb0), rb1), rb2), rb3) ((((c0, cb0), cb1), cb2), cb3) =
      gamma_chiral_base rb0 cb0 *
        wittCreationBase rb1 cb1 *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) rb2 cb2 *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) rb3 cb3 := by
  dsimp [jwCreation, jwStringWithBase, globalChirality, kronPow, Matrix.kroneckerMap]
  rw [matStage0_one_apply, one_mul]

private lemma jwCreation_4_2_apply (r0 c0 : Idx 0) (rb0 rb1 rb2 rb3 cb0 cb1 cb2 cb3 : Fin 2) :
    jwCreation 4 2 ((((r0, rb0), rb1), rb2), rb3) ((((c0, cb0), cb1), cb2), cb3) =
      gamma_chiral_base rb0 cb0 *
        gamma_chiral_base rb1 cb1 *
        wittCreationBase rb2 cb2 *
        (1 : Matrix (Fin 2) (Fin 2) ℝ) rb3 cb3 := by
  dsimp [jwCreation, jwStringWithBase, globalChirality, kronPow, Matrix.kroneckerMap]
  rw [matStage0_one_apply, one_mul]

private lemma jwCreation_4_3_apply (r0 c0 : Idx 0) (rb0 rb1 rb2 rb3 cb0 cb1 cb2 cb3 : Fin 2) :
    jwCreation 4 3 ((((r0, rb0), rb1), rb2), rb3) ((((c0, cb0), cb1), cb2), cb3) =
      gamma_chiral_base rb0 cb0 *
        gamma_chiral_base rb1 cb1 *
        gamma_chiral_base rb2 cb2 *
        wittCreationBase rb3 cb3 := by
  dsimp [jwCreation, jwStringWithBase, globalChirality, kronPow, Matrix.kroneckerMap]
  rw [matStage0_one_apply, one_mul]

/-- **Theorem 2 (Differential-Form Wedge Algebra & `ℤ₂` Chiral Grading inside `MatStage 4`)**:
1. Basis 1-forms `dx μ` map to `jwCreation 4 μ` and 2-forms `dx μ * dx ν` to `jwCreation 4 μ * jwCreation 4 ν`.
2. Top 4-form volume wedge `dx 0 * dx 1 * dx 2 * dx 3` is strictly nonzero inside `MatStage 4`.
3. `globalChirality 4` gives the exact differential-form parity grading (1-forms odd, 2-forms even). -/
theorem exteriorFormToCl11Stage4_properties (μ ν : Fin 4) :
    (exteriorFormToCl11Stage4 (dx μ) = jwCreation 4 μ) ∧
    (exteriorFormToCl11Stage4 (dx μ * dx ν) = jwCreation 4 μ * jwCreation 4 ν) ∧
    (exteriorFormToCl11Stage4 (dx 0 * dx 1 * dx 2 * dx 3) ≠ 0) ∧
    (globalChirality 4 * exteriorFormToCl11Stage4 (dx μ) =
      -(exteriorFormToCl11Stage4 (dx μ) * globalChirality 4)) ∧
    (globalChirality 4 * exteriorFormToCl11Stage4 (dx μ * dx ν) =
      exteriorFormToCl11Stage4 (dx μ * dx ν) * globalChirality 4) := by
  have h1 : exteriorFormToCl11Stage4 (dx μ) = jwCreation 4 μ := exteriorFormToCl11Stage4_dx μ
  have h2 : exteriorFormToCl11Stage4 (dx μ * dx ν) = jwCreation 4 μ * jwCreation 4 ν := by
    rw [map_mul, exteriorFormToCl11Stage4_dx, exteriorFormToCl11Stage4_dx]
  have hOdd : globalChirality 4 * exteriorFormToCl11Stage4 (dx μ) =
      -(exteriorFormToCl11Stage4 (dx μ) * globalChirality 4) := by
    rw [h1]
    exact eq_neg_of_add_eq_zero_left
      (by simpa [globalChirality, jwCreation] using globalChirality_anticomm_jwCreation 4 μ)
  have hEven : globalChirality 4 * exteriorFormToCl11Stage4 (dx μ * dx ν) =
      exteriorFormToCl11Stage4 (dx μ * dx ν) * globalChirality 4 := by
    rw [h2]
    have hGC : ∀ a : Fin 4, globalChirality 4 * jwCreation 4 a = -(jwCreation 4 a * globalChirality 4) :=
      fun a => eq_neg_of_add_eq_zero_left
        (by simpa [globalChirality, jwCreation] using globalChirality_anticomm_jwCreation 4 a)
    calc
      globalChirality 4 * (jwCreation 4 μ * jwCreation 4 ν)
          = (globalChirality 4 * jwCreation 4 μ) * jwCreation 4 ν := by rw [Matrix.mul_assoc]
      _ = -(jwCreation 4 μ * globalChirality 4) * jwCreation 4 ν := by rw [hGC μ]
      _ = -(jwCreation 4 μ * (globalChirality 4 * jwCreation 4 ν)) := by rw [Matrix.neg_mul, Matrix.mul_assoc]
      _ = (jwCreation 4 μ * jwCreation 4 ν) * globalChirality 4 := by
            rw [hGC ν, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  have hTop : exteriorFormToCl11Stage4 (dx 0 * dx 1 * dx 2 * dx 3) ≠ 0 := by
    rw [map_mul, map_mul, map_mul,
      exteriorFormToCl11Stage4_dx, exteriorFormToCl11Stage4_dx,
      exteriorFormToCl11Stage4_dx, exteriorFormToCl11Stage4_dx]
    intro h0
    let r0 : Idx 4 := ((((default, 0), 0), 0), 0)
    let r1 : Idx 4 := ((((default, 1), 0), 0), 0)
    let r2 : Idx 4 := ((((default, 1), 1), 0), 0)
    let r3 : Idx 4 := ((((default, 1), 1), 1), 0)
    let r4 : Idx 4 := ((((default, 1), 1), 1), 1)
    have hEntry := congrArg (fun M : MatStage 4 => M r0 r4) h0
    have hu0 : ∀ k : Idx 4, jwCreation 4 0 r0 k ≠ 0 → k = r1 := by
      intro k hk
      rcases k with ⟨⟨⟨⟨k0, b0⟩, b1⟩, b2⟩, b3⟩
      have hk0 : k0 = default := Subsingleton.elim k0 default
      dsimp only [r0, r1] at hk ⊢
      rw [hk0, jwCreation_4_0_apply] at hk
      rw [hk0]
      fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
        · (try norm_num [wittCreationBase, Matrix.one_apply] at hk)
          try rfl
    have hu1 : ∀ k : Idx 4, jwCreation 4 1 r1 k ≠ 0 → k = r2 := by
      intro k hk
      rcases k with ⟨⟨⟨⟨k0, b0⟩, b1⟩, b2⟩, b3⟩
      have hk0 : k0 = default := Subsingleton.elim k0 default
      dsimp only [r1, r2] at hk ⊢
      rw [hk0, jwCreation_4_1_apply] at hk
      rw [hk0]
      fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
        · (try norm_num [wittCreationBase, gamma_chiral_base, gamma_0_base,
            gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.one_apply,
            Matrix.mul_apply, Fin.sum_univ_two] at hk)
          try rfl
    have hu2 : ∀ k : Idx 4, jwCreation 4 2 r2 k ≠ 0 → k = r3 := by
      intro k hk
      rcases k with ⟨⟨⟨⟨k0, b0⟩, b1⟩, b2⟩, b3⟩
      have hk0 : k0 = default := Subsingleton.elim k0 default
      dsimp only [r2, r3] at hk ⊢
      rw [hk0, jwCreation_4_2_apply] at hk
      rw [hk0]
      fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
        · (try norm_num [wittCreationBase, gamma_chiral_base, gamma_0_base,
            gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.one_apply,
            Matrix.mul_apply, Fin.sum_univ_two] at hk)
          try rfl
    have hProd : (jwCreation 4 0 * jwCreation 4 1 * jwCreation 4 2 * jwCreation 4 3) r0 r4 =
        jwCreation 4 0 r0 r1 * jwCreation 4 1 r1 r2 * jwCreation 4 2 r2 r3 * jwCreation 4 3 r3 r4 := by
      have hm1 : ∀ c, (jwCreation 4 0 * jwCreation 4 1) r0 c =
          jwCreation 4 0 r0 r1 * jwCreation 4 1 r1 c := by
        intro c
        rw [Matrix.mul_apply, Finset.sum_eq_single r1]
        · intro k _ hkne
          have h0k : jwCreation 4 0 r0 k = 0 := by
            by_contra hne; exact hkne (hu0 k hne)
          rw [h0k, zero_mul]
        · simp
      have hm2 : ∀ c, (jwCreation 4 0 * jwCreation 4 1 * jwCreation 4 2) r0 c =
          jwCreation 4 0 r0 r1 * jwCreation 4 1 r1 r2 * jwCreation 4 2 r2 c := by
        intro c
        rw [Matrix.mul_apply, Finset.sum_eq_single r2]
        · rw [hm1 r2, mul_assoc]
        · intro k _ hkne
          rw [hm1 k]
          by_cases hk2 : jwCreation 4 1 r1 k = 0
          · rw [hk2, mul_zero, zero_mul]
          · exact absurd (hu1 k hk2) hkne
        · simp
      rw [Matrix.mul_apply, Finset.sum_eq_single r3]
      · rw [hm2 r3]
      · intro k _ hkne
        rw [hm2 k]
        by_cases hk3 : jwCreation 4 2 r2 k = 0
        · rw [hk3, mul_zero, zero_mul]
        · exact absurd (hu2 k hk3) hkne
      · simp
    rw [hProd, Matrix.zero_apply] at hEntry
    have hv0 : jwCreation 4 0 r0 r1 = 1 := by
      simp [r0, r1, jwCreation_4_0_apply, wittCreationBase, Matrix.one_apply]
    have hv1 : jwCreation 4 1 r1 r2 = 1 := by
      norm_num [r1, r2, jwCreation_4_1_apply, wittCreationBase, gamma_chiral_base, gamma_0_base,
        gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.one_apply, Matrix.mul_apply,
        Fin.sum_univ_two]
    have hv2 : jwCreation 4 2 r2 r3 = 1 := by
      norm_num [r2, r3, jwCreation_4_2_apply, wittCreationBase, gamma_chiral_base, gamma_0_base,
        gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.one_apply, Matrix.mul_apply,
        Fin.sum_univ_two]
    have hv3 : jwCreation 4 3 r3 r4 = 1 := by
      norm_num [r3, r4, jwCreation_4_3_apply, wittCreationBase, gamma_chiral_base, gamma_0_base,
        gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hv0, hv1, hv2, hv3] at hEntry
    norm_num at hEntry
  exact ⟨h1, h2, hTop, hOdd, hEven⟩

/-! ### Part 3: Graded Tensor Product `MatStage 7` & Direct-Limit `Cl11TensorTowerLimit` Bridge -/

/-- Canonical associator equivalence `(Idx a × Idx b) ≃ Idx (a + b)` for tensor stages. -/
def idxAddEquiv (a : ℕ) : (b : ℕ) → (Idx a × Idx b) ≃ Idx (a + b)
  | 0 =>
      { toFun := fun p => p.1
        invFun := fun x => (x, default)
        left_inv := fun p => Prod.ext rfl (Subsingleton.elim _ _).symm
        right_inv := fun _ => rfl }
  | b + 1 =>
      ((Equiv.prodAssoc (Idx a) (Idx b) (Fin 2)).symm).trans
        ((idxAddEquiv a b).prodCongr (Equiv.refl (Fin 2)))

/-- Tensor product of graded stage matrices `MatStage a × MatStage b → MatStage (a + b)`. -/
def kronMatStage (a b : ℕ) (A : MatStage a) (B : MatStage b) : MatStage (a + b) :=
  Matrix.reindexAlgEquiv ℝ ℝ (idxAddEquiv a b) (A ⊗ₖ B)

private lemma kronMatStage_mul (a b : ℕ) (A₁ A₂ : MatStage a) (B₁ B₂ : MatStage b) :
    kronMatStage a b (A₁ * A₂) (B₁ * B₂) = kronMatStage a b A₁ B₁ * kronMatStage a b A₂ B₂ := by
  unfold kronMatStage
  rw [Matrix.mul_kronecker_mul, map_mul]

private lemma kronMatStage_add_left (a b : ℕ) (A₁ A₂ : MatStage a) (B : MatStage b) :
    kronMatStage a b (A₁ + A₂) B = kronMatStage a b A₁ B + kronMatStage a b A₂ B := by
  unfold kronMatStage
  rw [Matrix.add_kronecker, map_add]

private lemma kronMatStage_smul_left (a b : ℕ) (c : ℝ) (A : MatStage a) (B : MatStage b) :
    kronMatStage a b (c • A) B = c • kronMatStage a b A B := by
  unfold kronMatStage
  rw [Matrix.smul_kronecker, map_smul]

private lemma continuous_kronMatStage_left (a b : ℕ) (B : MatStage b) :
    Continuous (fun A : MatStage a => kronMatStage a b A B) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [kronMatStage, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply]
  have hEntry : Continuous (fun A : MatStage a =>
      A ((idxAddEquiv a b).symm i).1 ((idxAddEquiv a b).symm j).1) :=
    (continuous_apply ((idxAddEquiv a b).symm j).1).comp
      (continuous_apply ((idxAddEquiv a b).symm i).1 :
        Continuous fun A : Idx a → Idx a → ℝ => A ((idxAddEquiv a b).symm i).1)
  exact hEntry.mul continuous_const

/-- Yang–Mills connection 1-form `𝒜(y) = ∑_μ A_μ(y) dx^μ` embedded in `MatStage 7`. -/
def ymConnectionFormToTower (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) : MatStage 7 :=
  ∑ μ : Fin 4, kronMatStage 3 4 (ymRealifyHom (A y μ)) (exteriorFormToCl11Stage4 (dx μ))

/-- Yang–Mills continuum curvature 2-form `(1/2) ∑_{μ,ν} F_{μν}(y) dx^μ ∧ dx^ν` in `MatStage 7`. -/
def ymCurvatureFormToTower (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) : MatStage 7 :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    (1 / 2 : ℝ) • kronMatStage 3 4
      (ymRealifyHom (continuumCurvature A y μ ν)) (exteriorFormToCl11Stage4 (dx μ * dx ν))

/-- Lattice Wilson plaquette 2-form `(1/2) ∑_{μ,ν} a⁻²(W_{μν}(y,a) - 1) dx^μ ∧ dx^ν` in `MatStage 7`. -/
def wilsonPlaquetteFormToTower (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (a : ℝ) : MatStage 7 :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    (1 / 2 : ℝ) • kronMatStage 3 4
      (ymRealifyHom ((a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1)))
      (exteriorFormToCl11Stage4 (dx μ * dx ν))

/-- Differential-form chirality operator `I₈ ⊗ Γ₄` inside `MatStage 7`. -/
def formChirality7 : MatStage 7 :=
  kronMatStage 3 4 (1 : MatStage 3) (globalChirality 4)

/-- **Theorem 3A (Wedge Square `𝒜 ∧ 𝒜` = Commutator 2-Form in `MatStage 7`)**:
Multiplying the matrix-valued 1-form `ymConnectionFormToTower A y` with itself automatically
produces `(1 / 2) ∑_{μ,ν} [A_μ(y), A_ν(y)] ⊗ (dx^μ ∧ dx^ν)` in `MatStage 7`. -/
theorem ymConnectionFormToTower_sq_eq_commutator_twoForm
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) :
    ymConnectionFormToTower A y * ymConnectionFormToTower A y =
      ∑ μ : Fin 4, ∑ ν : Fin 4,
        (1 / 2 : ℝ) • kronMatStage 3 4
          (ymRealifyHom (A y μ * A y ν - A y ν * A y μ))
          (exteriorFormToCl11Stage4 (dx μ * dx ν)) := by
  have hMul : ymConnectionFormToTower A y * ymConnectionFormToTower A y =
      ∑ μ : Fin 4, ∑ ν : Fin 4,
        kronMatStage 3 4 (ymRealifyHom (A y μ * A y ν))
          (exteriorFormToCl11Stage4 (dx μ * dx ν)) := by
    unfold ymConnectionFormToTower
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← kronMatStage_mul, ← map_mul, ← map_mul]
  have hSwap :
      (∑ μ : Fin 4, ∑ ν : Fin 4,
        kronMatStage 3 4 (ymRealifyHom (A y μ * A y ν))
          (exteriorFormToCl11Stage4 (dx μ * dx ν))) =
      -(∑ μ : Fin 4, ∑ ν : Fin 4,
        kronMatStage 3 4 (ymRealifyHom (A y ν * A y μ))
          (exteriorFormToCl11Stage4 (dx μ * dx ν))) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have hForm : exteriorFormToCl11Stage4 (dx ν * dx μ) =
        -(exteriorFormToCl11Stage4 (dx μ * dx ν)) := by
      rw [map_mul, map_mul, exteriorFormToCl11Stage4_dx, exteriorFormToCl11Stage4_dx]
      by_cases h : ν = μ
      · subst h
        rw [Cl55WittCAR.creation_sq 4 ν, neg_zero]
      · exact eq_neg_of_add_eq_zero_left
          (Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute 4 ν μ h)
    rw [hForm]
    unfold kronMatStage
    rw [kron_neg_right_real, map_neg]
  have hTwo : (2 : ℝ) • (ymConnectionFormToTower A y * ymConnectionFormToTower A y) =
      (∑ μ : Fin 4, ∑ ν : Fin 4,
        kronMatStage 3 4 (ymRealifyHom (A y μ * A y ν - A y ν * A y μ))
          (exteriorFormToCl11Stage4 (dx μ * dx ν))) := by
    rw [two_smul]
    conv_lhs =>
      lhs; rw [hMul]
    conv_lhs =>
      rhs; rw [hMul, hSwap]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [map_sub]
    unfold kronMatStage
    rw [kron_sub_left_real, map_sub]
    abel
  have hHalf := congrArg (fun X : MatStage 7 => (1 / 2 : ℝ) • X) hTwo
  rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul, Finset.smul_sum] at hHalf
  rw [hHalf]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.smul_sum]

/-- **Theorem 3B (`ℤ₂` Form Parity in `MatStage 7`)**:
Under `formChirality7 = I₈ ⊗ Γ₄`, the connection 1-form `ymConnectionFormToTower A y` is strictly
odd while the curvature 2-form `ymCurvatureFormToTower A y` is strictly even. -/
theorem ymFormToTower_chiral_grading (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) :
    (formChirality7 * ymConnectionFormToTower A y = -(ymConnectionFormToTower A y * formChirality7)) ∧
    (formChirality7 * ymCurvatureFormToTower A y = ymCurvatureFormToTower A y * formChirality7) := by
  constructor
  · unfold formChirality7 ymConnectionFormToTower
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← kronMatStage_mul, ← kronMatStage_mul, one_mul, mul_one,
      (exteriorFormToCl11Stage4_properties μ 0).2.2.2.1]
    unfold kronMatStage
    rw [kron_neg_right_real, map_neg]
  · unfold formChirality7 ymCurvatureFormToTower
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, ← kronMatStage_mul, ← kronMatStage_mul, one_mul, mul_one,
      (exteriorFormToCl11Stage4_properties μ ν).2.2.2.2]

/-- **Theorem 3C (Lattice-to-Continuum Convergence inside `MatStage 3` and `MatStage 7`)**:
As `a → 0` (`𝓝[≠] 0`), covariant finite differences, Wilson plaquette differential 2-forms, and
Hilbert–Schmidt action converge inside the graded `Cl(1,1)` real matrix tower. -/
theorem tendsto_lattice_yang_mills_in_cl11_tower
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ ν : Fin 4)
    (hA : ContDiff ℝ 2 A) (hΦ : DifferentiableAt ℝ Φ y) :
    Filter.Tendsto (fun a : ℝ => ymRealifyHom (latticeCovariantDiff A Φ y μ a))
      (𝓝[≠] 0) (𝓝 (ymRealifyHom (continuumCovariantDeriv A Φ y μ))) ∧
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteFormToTower A y a)
      (𝓝[≠] 0) (𝓝 (ymCurvatureFormToTower A y)) ∧
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A y μ ν a)
      (𝓝[≠] 0) (𝓝 ((1 / 2 : ℝ) * Matrix.trace
        ((ymRealifyHom (continuumCurvature A y μ ν))ᵀ *
          ymRealifyHom (continuumCurvature A y μ ν)))) := by
  have hContReal := (ymRealifyHom_properties 0 0).2.1
  refine ⟨?_, ?_, ?_⟩
  · exact (hContReal.continuousAt.tendsto).comp (tendsto_latticeCovariantDiff A Φ y μ hΦ)
  · unfold wilsonPlaquetteFormToTower ymCurvatureFormToTower
    refine tendsto_finsetSum Finset.univ fun α _ => ?_
    refine tendsto_finsetSum Finset.univ fun β _ => ?_
    have hTerm : Filter.Tendsto
        (fun a : ℝ => kronMatStage 3 4
          (ymRealifyHom ((a ^ 2)⁻¹ • (wilsonPlaquette A y α β a - 1)))
          (exteriorFormToCl11Stage4 (dx α * dx β)))
        (𝓝[≠] 0)
        (𝓝 (kronMatStage 3 4
          (ymRealifyHom (continuumCurvature A y α β))
          (exteriorFormToCl11Stage4 (dx α * dx β)))) :=
      ((continuous_kronMatStage_left 3 4 _).continuousAt.tendsto).comp
        ((hContReal.continuousAt.tendsto).comp (tendsto_wilsonPlaquette_curvature A y α β hA))
    exact hTerm.const_smul (1 / 2 : ℝ)
  · have hHS := (ymRealifyHom_properties 0 (continuumCurvature A y μ ν)).2.2.2.1
    change Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A y μ ν a) (𝓝[≠] 0)
      (𝓝 ((1 / 2 : ℝ) * Matrix.trace
        ((ymRealifyHom (continuumCurvature A y μ ν))ᵀ *
          ymRealifyHom (continuumCurvature A y μ ν))))
    rw [hHS]
    exact tendsto_wilsonPlaquetteAction A y μ ν hA

private lemma stageBond_injective : ∀ n : ℕ, Function.Injective (stageBond n) :=
  matStageEmbed_injective

private lemma wittCreationBase_col_zero (x : Fin 2) : wittCreationBase x 0 = 0 := by
  fin_cases x <;> rfl

private lemma jwCreation_4_col_bit2_zero (r c : Idx 4) (hc : c.1.2 = 0) :
    jwCreation 4 2 r c = 0 := by
  rcases r with ⟨⟨⟨⟨r0, rb0⟩, rb1⟩, rb2⟩, rb3⟩
  rcases c with ⟨⟨⟨⟨c0, cb0⟩, cb1⟩, cb2⟩, cb3⟩
  have hcb2 : cb2 = 0 := hc
  subst hcb2
  have h23 : ((2 : Fin 4) : ℕ) < 3 := by decide
  have h22 : ¬((2 : Fin 4) : ℕ) < 2 := by decide
  simp only [jwCreation, jwStringWithBase, h23, h22, ↓reduceDIte, Fin.coe_ofNat_eq_mod, Nat.mod_succ]
  have hL : (globalChirality 2 ⊗ₖ wittCreationBase) (((r0, rb0), rb1), rb2) (((c0, cb0), cb1), 0) = 0 := by
    change globalChirality 2 ((r0, rb0), rb1) ((c0, cb0), cb1) * wittCreationBase rb2 0 = 0
    rw [wittCreationBase_col_zero, mul_zero]
  change (globalChirality 2 ⊗ₖ wittCreationBase) (((r0, rb0), rb1), rb2) (((c0, cb0), cb1), 0) *
    (1 : Matrix (Fin 2) (Fin 2) ℝ) rb3 cb3 = 0
  rw [hL, zero_mul]

private lemma jwCreation_4_col_bit3_zero (r c : Idx 4) (hc : c.2 = 0) :
    jwCreation 4 3 r c = 0 := by
  rcases r with ⟨⟨⟨⟨r0, rb0⟩, rb1⟩, rb2⟩, rb3⟩
  rcases c with ⟨⟨⟨⟨c0, cb0⟩, cb1⟩, cb2⟩, cb3⟩
  have hcb3 : cb3 = 0 := hc
  subst hcb3
  have h33 : ¬((3 : Fin 4) : ℕ) < 3 := by decide
  simp only [jwCreation, jwStringWithBase, h33, ↓reduceDIte]
  change globalChirality 3 (((r0, rb0), rb1), rb2) (((c0, cb0), cb1), cb2) *
    wittCreationBase rb3 0 = 0
  rw [wittCreationBase_col_zero, mul_zero]

private lemma jwCreation_4_mul_entry_bit23_zero (μ ν : Fin 4) :
    (jwCreation 4 μ * jwCreation 4 ν) ((((default, 0), 0), 0), 0) ((((default, 1), 1), 0), 0) =
      if μ = 0 ∧ ν = 1 then 1 else if μ = 1 ∧ ν = 0 then -1 else 0 := by
  let r0 : Idx 4 := ((((default, 0), 0), 0), 0)
  let c01 : Idx 4 := ((((default, 1), 1), 0), 0)
  let r1 : Idx 4 := ((((default, 1), 0), 0), 0)
  change (jwCreation 4 μ * jwCreation 4 ν) r0 c01 = _
  have hcol2 : ∀ (M : MatStage 4) (x : Idx 4), (M * jwCreation 4 2) x c01 = 0 := by
    intro M x
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [jwCreation_4_col_bit2_zero k c01 rfl, mul_zero]
  have hcol3 : ∀ (M : MatStage 4) (x : Idx 4), (M * jwCreation 4 3) x c01 = 0 := by
    intro M x
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [jwCreation_4_col_bit3_zero k c01 rfl, mul_zero]
  have h01 : (jwCreation 4 0 * jwCreation 4 1) r0 c01 = 1 := by
    have hu0 : ∀ k : Idx 4, jwCreation 4 0 r0 k ≠ 0 → k = r1 := by
      intro k hk
      rcases k with ⟨⟨⟨⟨k0, b0⟩, b1⟩, b2⟩, b3⟩
      have hk0 : k0 = default := Subsingleton.elim k0 default
      dsimp only [r0, r1] at hk ⊢
      rw [hk0, jwCreation_4_0_apply] at hk
      rw [hk0]
      fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
        · (try norm_num [wittCreationBase, Matrix.one_apply] at hk)
          try rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single r1]
    · norm_num [r0, r1, c01, jwCreation_4_0_apply, jwCreation_4_1_apply, wittCreationBase,
        gamma_chiral_base, gamma_0_base, gamma_1_base, Cl11Matrix.J1, Cl11Matrix.Eminus,
        Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two]
    · intro k _ hk
      have hz : jwCreation 4 0 r0 k = 0 := by
        by_contra hne; exact hk (hu0 k hne)
      rw [hz, zero_mul]
    · simp
  have hSq : ∀ a : Fin 4, jwCreation 4 a * jwCreation 4 a = 0 := Cl55WittCAR.creation_sq 4
  have hAnti : ∀ {a b : Fin 4}, a ≠ b →
      jwCreation 4 a * jwCreation 4 b = -(jwCreation 4 b * jwCreation 4 a) := fun hab =>
    eq_neg_of_add_eq_zero_left
      (Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute 4 _ _ hab)
  fin_cases μ <;> fin_cases ν <;> dsimp only
  · rw [hSq _]; simp
  · simpa using h01
  · simpa using hcol2 (jwCreation 4 0) r0
  · simpa using hcol3 (jwCreation 4 0) r0
  · rw [hAnti (by decide), Matrix.neg_apply]; simpa [h01]
  · rw [hSq _]; simp
  · simpa using hcol2 (jwCreation 4 1) r0
  · simpa using hcol3 (jwCreation 4 1) r0
  · rw [hAnti (by decide), Matrix.neg_apply]; simpa [hcol2 (jwCreation 4 0) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simpa [hcol2 (jwCreation 4 1) r0]
  · rw [hSq _]; simp
  · simpa using hcol3 (jwCreation 4 2) r0
  · rw [hAnti (by decide), Matrix.neg_apply]; simpa [hcol3 (jwCreation 4 0) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simpa [hcol3 (jwCreation 4 1) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simpa [hcol3 (jwCreation 4 2) r0]
  · rw [hSq _]; simp

private lemma scalar_inv_two_add (x : ℝ) :
    (2 : ℝ)⁻¹ * x + (2 : ℝ)⁻¹ * x = x := by
  ring

/-- **Theorem 3D (Transport to Infinite Direct Limit `Cl11TensorTowerLimit.Limit`)**:
Transports the Yang–Mills matrix connection/curvature forms and continuum limits into the infinite
algebraic tensor-tower direct limit `Cl11TensorTowerLimit.Limit` via `ofStage 7`:
1. Wedge-square identity `ofStage 7 (𝒜_conn) * ofStage 7 (𝒜_conn)` matches the commutator 2-form.
2. Exact bonding compatibility `ofStage 8 (stageEmbed 7 (ℱ_curv)) = ofStage 7 (ℱ_curv)`.
3. Faithful embedding `Function.Injective (ofStage 7)` preserves the non-Abelian continuum curvature
   witness `ofStage 7 (ymCurvatureFormToTower A_wit y) ≠ 0`. -/
theorem ym_smooth_lattice_continuum_to_cl11_direct_limit
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) :
    (ofStage 7 (ymConnectionFormToTower A y) * ofStage 7 (ymConnectionFormToTower A y) =
      ofStage 7 (∑ μ : Fin 4, ∑ ν : Fin 4,
        (1 / 2 : ℝ) • kronMatStage 3 4
          (ymRealifyHom (A y μ * A y ν - A y ν * A y μ))
          (exteriorFormToCl11Stage4 (dx μ * dx ν)))) ∧
    (ofStage 8 (stageEmbed 7 (ymCurvatureFormToTower A y)) =
      ofStage 7 (ymCurvatureFormToTower A y)) ∧
    Function.Injective (ofStage 7) ∧
    (let A_wit : FourSpace → Fin 4 → Mat4C :=
      fun z μ => circularConnectionMat4 (witnessCircularField z μ)
     ofStage 7 (ymCurvatureFormToTower A_wit y) ≠ 0) := by
  have hInj7 : Function.Injective (ofStage 7) :=
    directLimitOf_injective (Stage := Cl11TensorTowerLimit.Stage) stageBond stageBond_injective 7
  refine ⟨?_, ofStage_apply_bond 7 _, hInj7, ?_⟩
  · rw [← ofStage_mul, ymConnectionFormToTower_sq_eq_commutator_twoForm A y]
  · dsimp
    let A_wit : FourSpace → Fin 4 → Mat4C :=
      fun z μ => circularConnectionMat4 (witnessCircularField z μ)
    have hW := circularLattice_nonabelian_continuum_witness y
    have hFne : continuumCurvature A_wit y 0 1 ≠ 0 := hW.2.2.1
    have hRealNe : ymRealifyHom (continuumCurvature A_wit y 0 1) ≠ 0 := by
      intro h0
      exact hFne ((ymRealifyHom_properties 0 0).1 (by rw [h0, map_zero]))
    obtain ⟨i, j, hij⟩ : ∃ i j : Idx 3, ymRealifyHom (continuumCurvature A_wit y 0 1) i j ≠ 0 := by
      by_contra hAll
      push_neg at hAll
      apply hRealNe
      ext i j
      exact hAll i j
    let r0 : Idx 4 := ((((default, 0), 0), 0), 0)
    let c01 : Idx 4 := ((((default, 1), 1), 0), 0)
    have hCurvNe : ymCurvatureFormToTower A_wit y ≠ 0 := by
      intro h0
      have hEval := congrArg
        (fun M : MatStage 7 => M (idxAddEquiv 3 4 (i, r0)) (idxAddEquiv 3 4 (j, c01))) h0
      simp only [ymCurvatureFormToTower, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        kronMatStage, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.kroneckerMap_apply, Matrix.zero_apply] at hEval
      have hTerm : ∀ μ ν : Fin 4,
          (1 / 2 : ℝ) * (ymRealifyHom (continuumCurvature A_wit y μ ν) i j *
            exteriorFormToCl11Stage4 (dx μ * dx ν) r0 c01) =
            if μ = 0 ∧ ν = 1 then
              (1 / 2 : ℝ) * (ymRealifyHom (continuumCurvature A_wit y 0 1) i j * 1)
            else if μ = 1 ∧ ν = 0 then
              (1 / 2 : ℝ) * ((-ymRealifyHom (continuumCurvature A_wit y 0 1) i j) * -1)
            else 0 := by
        intro μ ν
        rw [(exteriorFormToCl11Stage4_properties μ ν).2.1, jwCreation_4_mul_entry_bit23_zero μ ν]
        split_ifs with h01 h10
        · rcases h01 with ⟨rfl, rfl⟩; rfl
        · rcases h10 with ⟨rfl, rfl⟩
          rw [continuumCurvature_antisymm A_wit y 0 1, map_neg, Matrix.neg_apply]
        · simp
      simp_rw [hTerm] at hEval
      have hSum : (∑ μ : Fin 4, ∑ ν : Fin 4,
          (if μ = 0 ∧ ν = 1 then
            (1 / 2 : ℝ) * (ymRealifyHom (continuumCurvature A_wit y 0 1) i j * 1)
          else if μ = 1 ∧ ν = 0 then
            (1 / 2 : ℝ) * ((-ymRealifyHom (continuumCurvature A_wit y 0 1) i j) * -1)
          else 0)) =
          ymRealifyHom (continuumCurvature A_wit y 0 1) i j := by
        simp [Fin.sum_univ_four]
        exact scalar_inv_two_add _
      rw [hSum] at hEval
      exact hij hEval
    intro hLim0
    apply hCurvNe
    apply hInj7
    rw [hLim0, ofStage_zero]

end InfoGeometry.Canonical.YangMillsContinuumCl11TowerBridge
