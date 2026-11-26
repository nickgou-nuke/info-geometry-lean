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
import InfoGeometry.OperatorAlgebra.OsterwalderSchraderContinuumReconstruction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
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
* `ymRealifyHom_properties`, `exteriorFormToCl11Stage4_properties`, `exteriorFormToCl11Stage4_injective`
* `ymConnectionFormToTower_sq_eq_commutator_twoForm`, `ymFormToTower_chiral_grading`,
  `ymCurvatureFormToTower_eq_extDeriv_add_sq`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `tendsto_lattice_yang_mills_in_cl11_tower` (under `ContDiff ℝ 2 A` and `DifferentiableAt ℝ Φ y`)
* `ym_smooth_lattice_continuum_to_cl11_direct_limit` and `ym_cl11_direct_limit_and_os_continuum_bridge`
  (packaging continuum-limit + direct-limit bonding compatibility, Cartan equation `F = dA + A * A`,
  and OS continuum clustering)

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
    simp [ymRealify, mat4RealPart_one, mat4ImagPart_one]
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
      show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte,
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
    simp [hne]
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
      simp [r0, r1, jwCreation_4_0_apply, wittCreationBase]
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
        left_inv := fun _ => Prod.ext rfl (Subsingleton.elim _ _).symm
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
  rw [jwCreation_4_2_apply, wittCreationBase_col_zero]
  simp

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
  · simp [h01]
  · simp [hcol2 (jwCreation 4 0) r0]
  · simp [hcol3 (jwCreation 4 0) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simp [h01]
  · rw [hSq _]; simp
  · simp [hcol2 (jwCreation 4 1) r0]
  · simp [hcol3 (jwCreation 4 1) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simp [hcol2 (jwCreation 4 0) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simp [hcol2 (jwCreation 4 1) r0]
  · rw [hSq _]; simp
  · simp [hcol3 (jwCreation 4 2) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simp [hcol3 (jwCreation 4 0) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simp [hcol3 (jwCreation 4 1) r0]
  · rw [hAnti (by decide), Matrix.neg_apply]; simp [hcol3 (jwCreation 4 2) r0]
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
      push Not at hAll
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

/-! ### Part 4: Full Exterior Injectivity, Cartan Structure Equation, & OS Continuum Bridge -/

section ExteriorInjectivityAndOSBridge

open InfoGeometry.Canonical.RealDoubledChiralKreinFrame (frameBasis)
open InfoGeometry.OperatorAlgebra.OsterwalderSchraderContinuumReconstruction

private def finsetToIdxFun : ∀ n : ℕ, Finset (Fin n) → Idx n
  | 0, _ => (0 : Fin 1)
  | n + 1, S =>
      (finsetToIdxFun n (S.preimage Fin.castSucc (Fin.castSucc_injective n).injOn),
        if Fin.last n ∈ S then (0 : Fin 2) else (1 : Fin 2))

private def idxToFinsetFun : ∀ n : ℕ, Idx n → Finset (Fin n)
  | 0, _ => ∅
  | n + 1, (idx, b) =>
      let S' := (idxToFinsetFun n idx).map ⟨Fin.castSucc, Fin.castSucc_injective n⟩
      if b = 0 then insert (Fin.last n) S' else S'

private lemma finsetToIdxFun_leftInv :
    ∀ (n : ℕ) (S : Finset (Fin n)), idxToFinsetFun n (finsetToIdxFun n S) = S
  | 0, S => by
      ext x; exact Fin.elim0 x
  | n + 1, S => by
      dsimp [finsetToIdxFun, idxToFinsetFun]
      rw [finsetToIdxFun_leftInv n]
      by_cases hIn : Fin.last n ∈ S
      · simp only [hIn, ↓reduceIte]
        ext x
        by_cases hx : x = Fin.last n
        · subst hx; simp [hIn]
        · obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hx
          simp [Fin.castSucc_ne_last]
      · simp only [hIn, one_ne_zero, ↓reduceIte]
        ext x
        by_cases hx : x = Fin.last n
        · subst hx
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk, hIn, iff_false, not_exists,
            not_and]
          intro a _ ha
          exact (Fin.castSucc_lt_last a).ne ha
        · obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.mpr hx
          simp only [Finset.mem_map, Finset.mem_preimage, Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨a, ha, haEq⟩
            exact (Fin.castSucc_injective n haEq) ▸ ha
          · intro hk
            exact ⟨k, hk, rfl⟩

private lemma finsetToIdxFun_rightInv :
    ∀ (n : ℕ) (p : Idx n), finsetToIdxFun n (idxToFinsetFun n p) = p
  | 0, p => by
      dsimp [finsetToIdxFun]
      exact Subsingleton.elim _ _
  | n + 1, (idx, b) => by
      dsimp [idxToFinsetFun, finsetToIdxFun]
      by_cases hb : b = 0
      · subst hb
        have hPre :
            (insert (Fin.last n)
              ((idxToFinsetFun n idx).map ⟨Fin.castSucc, Fin.castSucc_injective n⟩)).preimage
                Fin.castSucc (Fin.castSucc_injective n).injOn =
              idxToFinsetFun n idx := by
          ext k
          rw [Finset.mem_preimage, Finset.mem_insert, Finset.mem_map]
          simp only [Function.Embedding.coeFn_mk]
          constructor
          · rintro (hk | ⟨a, ha, haEq⟩)
            · exact False.elim ((Fin.castSucc_lt_last k).ne hk)
            · exact Fin.castSucc_injective n haEq ▸ ha
          · intro hk
            exact Or.inr ⟨k, hk, rfl⟩
        simp only [↓reduceIte, Finset.mem_insert_self, hPre, finsetToIdxFun_rightInv n idx]
        rfl
      · have hb1 : b = 1 := by fin_cases b <;> simp_all
        subst hb1
        have hNot : Fin.last n ∉
            (idxToFinsetFun n idx).map ⟨Fin.castSucc, Fin.castSucc_injective n⟩ := by
          simp [Fin.castSucc_ne_last]
        have hPre :
            ((idxToFinsetFun n idx).map ⟨Fin.castSucc, Fin.castSucc_injective n⟩).preimage
                Fin.castSucc (Fin.castSucc_injective n).injOn =
              idxToFinsetFun n idx := by
          ext k
          rw [Finset.mem_preimage, Finset.mem_map]
          simp only [Function.Embedding.coeFn_mk]
          exact ⟨fun ⟨a, ha, haEq⟩ => Fin.castSucc_injective n haEq ▸ ha, fun hk => ⟨k, hk, rfl⟩⟩
        simp only [one_ne_zero, ↓reduceIte, hPre, finsetToIdxFun_rightInv n idx, hNot]
        rfl

/-- Canonical equivalence `Finset (Fin n) ≃ Idx n` matching exterior basis blades to
`2ⁿ`-component Fock spinor basis vectors (`0` occupied, `1` empty). -/
def finsetToIdx (n : ℕ) : Finset (Fin n) ≃ Idx n where
  toFun := finsetToIdxFun n
  invFun := idxToFinsetFun n
  left_inv := finsetToIdxFun_leftInv n
  right_inv := finsetToIdxFun_rightInv n

/-- Vacuum spinor basis vector `|∅⟩ = e_{(1,...,1)} : Idx n → ℝ`. -/
def vacVec (n : ℕ) : Idx n → ℝ :=
  Pi.single (finsetToIdx n ∅) (1 : ℝ)

private lemma scalar_kron_mul_reassoc (a b c d : ℝ) :
    a * b * (c * d) = (a * c) * (b * d) := by
  ring

private lemma mulVec_kron_single {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (A : Matrix α α ℝ) (B : Matrix β β ℝ) (u : α → ℝ) (v : β → ℝ)
    (i : α) (j : β) :
    (A ⊗ₖ B).mulVec (fun p => u p.1 * v p.2) (i, j) = A.mulVec u i * B.mulVec v j := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]
  calc
    ∑ a : α, ∑ b : β, A i a * B j b * (u a * v b)
        = ∑ a : α, ∑ b : β, (A i a * u a) * (B j b * v b) :=
          Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => scalar_kron_mul_reassoc _ _ _ _
    _ = ∑ a : α, (A i a * u a) * ∑ b : β, B j b * v b :=
          Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ = (∑ a : α, A i a * u a) * ∑ b : β, B j b * v b := (Finset.sum_mul _ _ _).symm

private lemma pi_single_prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (c : ℝ) :
    (Pi.single (a, b) c : α × β → ℝ) =
      fun p => (Pi.single a c : α → ℝ) p.1 * (Pi.single b (1 : ℝ) : β → ℝ) p.2 := by
  ext ⟨i, j⟩
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [hi, hj]

private lemma globalChirality_mulVec_single :
    ∀ (n : ℕ) (idx : Idx n), ∃ c : ℝ, c ^ 2 = 1 ∧
      (globalChirality n).mulVec (Pi.single idx (1 : ℝ)) = c • Pi.single idx (1 : ℝ)
  | 0, idx => by
      refine ⟨1, one_pow 2, ?_⟩
      ext i
      have hi : i = idx := Subsingleton.elim i idx
      subst hi
      simp [globalChirality, kronPow]
  | n + 1, (idx, b) => by
      obtain ⟨c, hc, ih⟩ := globalChirality_mulVec_single n idx
      have hG : ∀ k : Fin 2, ∃ d : ℝ, d ^ 2 = 1 ∧
          gamma_chiral_base.mulVec (Pi.single k (1 : ℝ)) = d • Pi.single k (1 : ℝ) := by
        intro k
        fin_cases k
        · refine ⟨-1, by norm_num, ?_⟩
          ext j; fin_cases j <;>
            norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
              InfoGeometry.Clifford.Cl11Matrix.J1, InfoGeometry.Clifford.Cl11Matrix.Eminus,
              Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
        · refine ⟨1, by norm_num, ?_⟩
          ext j; fin_cases j <;>
            norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
              InfoGeometry.Clifford.Cl11Matrix.J1, InfoGeometry.Clifford.Cl11Matrix.Eminus,
              Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
      obtain ⟨d, hd, hdb⟩ := hG b
      refine ⟨c * d, by rw [mul_pow, hc, hd, mul_one], ?_⟩
      ext ⟨i, j⟩
      change (globalChirality (n + 1) *ᵥ
          (Pi.single ((idx, b) : Idx n × Fin 2) (1 : ℝ) : Idx n × Fin 2 → ℝ)) (i, j) =
        ((c * d) •
          (Pi.single ((idx, b) : Idx n × Fin 2) (1 : ℝ) : Idx n × Fin 2 → ℝ)) (i, j)
      rw [pi_single_prod idx b 1]
      change (kronPow gamma_chiral_base n ⊗ₖ gamma_chiral_base).mulVec
          (fun p => (Pi.single idx (1 : ℝ) : Idx n → ℝ) p.1 *
            (Pi.single b (1 : ℝ) : Fin 2 → ℝ) p.2) (i, j) = _
      have ih' : (kronPow gamma_chiral_base n).mulVec (Pi.single idx (1 : ℝ)) =
          c • Pi.single idx (1 : ℝ) := ih
      rw [mulVec_kron_single, ih', hdb]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact scalar_kron_mul_reassoc _ _ _ _

private lemma wittCreationBase_mulVec_one :
    wittCreationBase.mulVec (Pi.single (1 : Fin 2) (1 : ℝ)) = Pi.single (0 : Fin 2) (1 : ℝ) := by
  ext j; fin_cases j <;>
    norm_num [wittCreationBase, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]

private lemma finsetToIdx_insert_castSucc {n : ℕ} (k : Fin n) (S : Finset (Fin (n + 1))) :
    finsetToIdxFun (n + 1) (insert k.castSucc S) =
      (finsetToIdxFun n (insert k (S.preimage Fin.castSucc
        (Fin.castSucc_injective n).injOn)),
       if Fin.last n ∈ S then (0 : Fin 2) else (1 : Fin 2)) := by
  dsimp [finsetToIdxFun]
  have hBool : (if Fin.last n ∈ insert k.castSucc S then (0 : Fin 2) else (1 : Fin 2)) =
      if Fin.last n ∈ S then (0 : Fin 2) else (1 : Fin 2) := by
    simp [(Fin.castSucc_ne_last k).symm]
  have hPre : (insert k.castSucc S).preimage Fin.castSucc
      (Fin.castSucc_injective n).injOn =
      insert k (S.preimage Fin.castSucc (Fin.castSucc_injective n).injOn) := by
    ext x
    rw [Finset.mem_preimage, Finset.mem_insert, Finset.mem_insert, Finset.mem_preimage,
      Fin.castSucc_inj]
  rw [hBool, hPre]

private lemma finsetToIdx_insert_last {n : ℕ} (S : Finset (Fin (n + 1))) :
    finsetToIdxFun (n + 1) (insert (Fin.last n) S) =
      (finsetToIdxFun n (S.preimage Fin.castSucc
        (Fin.castSucc_injective n).injOn),
       (0 : Fin 2)) := by
  dsimp [finsetToIdxFun]
  have hPre : (insert (Fin.last n) S).preimage Fin.castSucc
      (Fin.castSucc_injective n).injOn =
      S.preimage Fin.castSucc (Fin.castSucc_injective n).injOn := by
    ext x
    simp [Fin.castSucc_ne_last]
  simp only [Finset.mem_insert_self, ↓reduceIte, hPre]
  rfl

private lemma jwCreation_succ_castSucc (n : ℕ) (k' : Fin n) :
    jwCreation (n + 1) k'.castSucc =
      jwStringWithBase wittCreationBase n k' ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  change (if h : ((k'.castSucc : Fin (n + 1)) : ℕ) < n then
      jwStringWithBase wittCreationBase n ⟨(k'.castSucc : ℕ), h⟩ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
    else globalChirality n ⊗ₖ wittCreationBase) = _
  have hLt : ((k'.castSucc : Fin (n + 1)) : ℕ) < n := k'.isLt
  simp only [hLt, ↓reduceDIte]
  rfl

private lemma jwCreation_succ_last (n : ℕ) :
    jwCreation (n + 1) (Fin.last n) = globalChirality n ⊗ₖ wittCreationBase := by
  have hNot : ¬((Fin.last n : ℕ) < n) := by simp
  change (if h : ((Fin.last n : Fin (n + 1)) : ℕ) < n then
      jwStringWithBase wittCreationBase n ⟨(Fin.last n : ℕ), h⟩ ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)
    else globalChirality n ⊗ₖ wittCreationBase) = _
  split_ifs
  rfl

private lemma jwCreation_mulVec_finset :
    ∀ (n : ℕ) (k : Fin n) (S : Finset (Fin n)), k ∉ S →
      ∃ c : ℝ, c ^ 2 = 1 ∧
        (jwCreation n k).mulVec (Pi.single (finsetToIdx n S) (1 : ℝ)) =
          c • Pi.single (finsetToIdx n (insert k S)) (1 : ℝ)
  | 0, k, _, _ => Fin.elim0 k
  | n + 1, k, S, hk => by
      by_cases hlt : (k : ℕ) < n
      · let k' : Fin n := ⟨k, hlt⟩
        have hkEq : k = k'.castSucc := Fin.ext rfl
        rw [hkEq]
        rw [hkEq] at hk
        let S' : Finset (Fin n) := S.preimage Fin.castSucc (Fin.castSucc_injective n).injOn
        have hk' : k' ∉ S' := fun hMem => hk (Finset.mem_preimage.mp hMem)
        obtain ⟨c, hc, ih⟩ := jwCreation_mulVec_finset n k' S' hk'
        refine ⟨c, hc, ?_⟩
        dsimp [finsetToIdx]
        rw [finsetToIdx_insert_castSucc k' S, jwCreation_succ_castSucc n k']
        ext ⟨i, j⟩
        have hSingle :
            (Pi.single (finsetToIdxFun (n + 1) S : Idx n × Fin 2) (1 : ℝ) : Idx n × Fin 2 → ℝ) =
              fun p => (Pi.single (finsetToIdxFun n S') (1 : ℝ) : Idx n → ℝ) p.1 *
                (Pi.single (if Fin.last n ∈ S then (0 : Fin 2) else (1 : Fin 2)) (1 : ℝ) : Fin 2 → ℝ) p.2 := by
          dsimp [finsetToIdxFun, S']
          exact pi_single_prod _ _ 1
        change ((jwStringWithBase wittCreationBase n k' ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec
            (Pi.single (finsetToIdxFun (n + 1) S : Idx n × Fin 2) (1 : ℝ) : Idx n × Fin 2 → ℝ)) (i, j) =
          (c • (Pi.single (finsetToIdxFun n (insert k' S'),
            if Fin.last n ∈ S then (0 : Fin 2) else (1 : Fin 2)) (1 : ℝ) : Idx n × Fin 2 → ℝ)) (i, j)
        rw [hSingle, mulVec_kron_single]
        have ih' : (jwStringWithBase wittCreationBase n k').mulVec
            (Pi.single (finsetToIdxFun n S') (1 : ℝ)) =
            c • Pi.single (finsetToIdxFun n (insert k' S')) (1 : ℝ) := ih
        rw [ih', Matrix.one_mulVec]
        simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, Prod.mk.injEq]
        by_cases hi : i = finsetToIdxFun n (insert k' S') <;>
          by_cases hj : j = (if Fin.last n ∈ S then (0 : Fin 2) else (1 : Fin 2)) <;>
          simp [hi, hj]
      · have hlast : k = Fin.last n := Fin.eq_last_of_not_lt hlt
        subst hlast
        let S' : Finset (Fin n) := S.preimage Fin.castSucc (Fin.castSucc_injective n).injOn
        obtain ⟨c, hc, hgc⟩ := globalChirality_mulVec_single n (finsetToIdxFun n S')
        refine ⟨c, hc, ?_⟩
        dsimp [finsetToIdx]
        rw [finsetToIdx_insert_last S, jwCreation_succ_last n]
        have hSingle :
            (Pi.single (finsetToIdxFun (n + 1) S : Idx n × Fin 2) (1 : ℝ) : Idx n × Fin 2 → ℝ) =
              fun p => (Pi.single (finsetToIdxFun n S') (1 : ℝ) : Idx n → ℝ) p.1 *
                (Pi.single (1 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) p.2 := by
          dsimp [finsetToIdxFun, S']
          simp only [hk, ↓reduceIte]
          exact pi_single_prod _ _ 1
        ext ⟨i, j⟩
        change ((kronPow gamma_chiral_base n ⊗ₖ wittCreationBase).mulVec
            (Pi.single (finsetToIdxFun (n + 1) S : Idx n × Fin 2) (1 : ℝ) : Idx n × Fin 2 → ℝ)) (i, j) =
          (c • (Pi.single (finsetToIdxFun n S', (0 : Fin 2)) (1 : ℝ) : Idx n × Fin 2 → ℝ)) (i, j)
        rw [hSingle, mulVec_kron_single]
        have hgc' : (kronPow gamma_chiral_base n).mulVec (Pi.single (finsetToIdxFun n S') 1) =
            c • Pi.single (finsetToIdxFun n S') 1 := hgc
        rw [hgc', wittCreationBase_mulVec_one]
        simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, Prod.mk.injEq]
        by_cases hi : i = finsetToIdxFun n S' <;> by_cases hj : j = 0 <;> simp [hi, hj]

private lemma basis_exteriorAlgebra_singleton (n : ℕ) (k : Fin n) :
    (Pi.basisFun ℝ (Fin n)).ExteriorAlgebra ({k} : Finset (Fin n)) =
      ExteriorAlgebra.ι ℝ (Pi.single k (1 : ℝ)) := by
  have hkCard : ({k} : Finset (Fin n)).card = 1 := Finset.card_singleton k
  rw [ExteriorAlgebra.basis_apply_ofCard (Pi.basisFun ℝ (Fin n)) hkCard]
  dsimp [ExteriorAlgebra.ιMulti_family]
  change ExteriorAlgebra.ιMulti ℝ 1
      ((Pi.basisFun ℝ (Fin n)) ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.ofCard hkCard))) = _
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  have hEmpty : Matrix.vecTail
      ((Pi.basisFun ℝ (Fin n)) ∘ ⇑(Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.ofCard hkCard))) = Fin.elim0 := by
    ext x; exact Fin.elim0 x
  rw [hEmpty]
  have h1 : ExteriorAlgebra.ιMulti ℝ 0 (Fin.elim0 : Fin 0 → (Fin n → ℝ)) = 1 := rfl
  rw [h1, mul_one]
  congr 1
  simp only [Function.comp_apply, Pi.basisFun_apply]
  congr 1
  have hMem :
      (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard hkCard) 0) ∈
        ({k} : Finset (Fin n)) :=
    Finset.orderEmbOfFin_mem ({k} : Finset (Fin n)) hkCard 0
  exact Finset.mem_singleton.mp hMem

private lemma exteriorBasis4_mulVec_vacVec :
    ∀ S : Finset (Fin 4), ∃ c : ℝ, c ^ 2 = 1 ∧
      (exteriorFormToCl11Stage4 ((Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra S)).mulVec (vacVec 4) =
        c • Pi.single (finsetToIdx 4 S) (1 : ℝ) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, one_pow 2, ?_⟩
      have h0Card : (∅ : Finset (Fin 4)).card = 0 := Finset.card_empty
      have hEmpty : (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra ∅ = 1 := by
        rw [ExteriorAlgebra.basis_apply_ofCard (Pi.basisFun ℝ (Fin 4)) h0Card]
        dsimp [ExteriorAlgebra.ιMulti_family]
        rfl
      rw [hEmpty, map_one, Matrix.one_mulVec, one_smul]
      rfl
  | @insert k S hk ih =>
      obtain ⟨c, hc, hSVec⟩ := ih
      let s₀ : Set.powersetCard (Fin 4) 1 := ⟨{k}, Finset.card_singleton k⟩
      let t₀ : Set.powersetCard (Fin 4) S.card := ⟨S, rfl⟩
      have hDisj : Disjoint s₀.1 t₀.1 := Finset.disjoint_singleton_left.mpr hk
      have hMul := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun ℝ (Fin 4)) s₀ t₀ hDisj
      have hDisjVal : (Set.powersetCard.disjUnion hDisj).1 = insert k S := by
        ext x; simp [Set.powersetCard.disjUnion, s₀, t₀]
      let ε := (Set.powersetCard.permOfDisjoint hDisj).sign
      have hεSq : (ε : ℤ) * (ε : ℤ) = 1 := by
        rcases Int.units_eq_one_or ε with h | h <;> simp [h]
      have hBasisInsert :
          (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra (insert k S) =
            (ε : ℤ) • ((Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra {k} *
              (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra S) := by
        have hMul' : (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra {k} *
            (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra S =
            (ε : ℤ) • (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra (insert k S) := by
          simpa [s₀, t₀, hDisjVal, Units.smul_def] using hMul
        calc
          (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra (insert k S)
              = (1 : ℤ) • (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra (insert k S) := (one_zsmul _).symm
          _ = ((ε : ℤ) * (ε : ℤ)) • (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra (insert k S) := by
                rw [hεSq]
          _ = (ε : ℤ) • ((ε : ℤ) • (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra (insert k S)) :=
                mul_smul _ _ _
          _ = (ε : ℤ) • ((Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra {k} *
                (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra S) := by rw [← hMul']
      obtain ⟨d, hd, hJW⟩ := jwCreation_mulVec_finset 4 k S hk
      refine ⟨((ε : ℤ) : ℝ) * (c * d), ?_, ?_⟩
      · have hεR : (((ε : ℤ) : ℝ)) ^ 2 = 1 := by
          rcases Int.units_eq_one_or ε with h | h <;> simp [h]
        rw [mul_pow, mul_pow, hεR, hc, hd]; ring
      · rw [hBasisInsert, map_zsmul, map_mul, basis_exteriorAlgebra_singleton 4 k]
        have hDx : ExteriorAlgebra.ι ℝ (Pi.single k (1 : ℝ)) = dx k := rfl
        rw [hDx, exteriorFormToCl11Stage4_dx k, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
          hSVec, Matrix.mulVec_smul, hJW]
        ext idx
        simp [zsmul_eq_mul, mul_assoc]

/-- **Dirac–Kähler / Fock Spinor Linear Map (`16`-dimensional)** evaluating
`exteriorFormToCl11Stage4 ω` on the vacuum vector `vacVec 4`. -/
def exteriorFormToSpinorMap4 : ExteriorAlgebra ℝ (Fin 4 → ℝ) →ₗ[ℝ] (Idx 4 → ℝ) where
  toFun ω := (exteriorFormToCl11Stage4 ω).mulVec (vacVec 4)
  map_add' ω₁ ω₂ := by rw [map_add, Matrix.add_mulVec]
  map_smul' c ω := by rw [map_smul, Matrix.smul_mulVec]; rfl

theorem exteriorFormToSpinorMap4_injective :
    Function.Injective exteriorFormToSpinorMap4 := by
  intro ω₁ ω₂ h
  have hDiff : (exteriorFormToCl11Stage4 (ω₁ - ω₂)).mulVec (vacVec 4) = 0 := by
    rw [map_sub, Matrix.sub_mulVec]
    exact sub_eq_zero.mpr h
  let b := (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra
  have hDecomp : ω₁ - ω₂ = ∑ S : Finset (Fin 4), (b.repr (ω₁ - ω₂) S) • b S :=
    (b.sum_repr (ω₁ - ω₂)).symm
  have hVecSum : (exteriorFormToCl11Stage4 (ω₁ - ω₂)).mulVec (vacVec 4) =
      ∑ S : Finset (Fin 4), (b.repr (ω₁ - ω₂) S) •
        ((exteriorFormToCl11Stage4 (b S)).mulVec (vacVec 4)) := by
    conv_lhs => rw [hDecomp]
    rw [map_sum]
    simp_rw [map_smul]
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Matrix.smul_mulVec]
  rw [hVecSum] at hDiff
  have hZeroCoeff : ∀ S : Finset (Fin 4), b.repr (ω₁ - ω₂) S = 0 := by
    intro S
    have hCoord := congrFun hDiff (finsetToIdx 4 S)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hCoord
    obtain ⟨cS, hcSSq, hSVec⟩ := exteriorBasis4_mulVec_vacVec S
    have hSVec' : (exteriorFormToCl11Stage4 (b S)).mulVec (vacVec 4) =
        cS • Pi.single (finsetToIdx 4 S) (1 : ℝ) := hSVec
    have hTerm : (∑ T : Finset (Fin 4), b.repr (ω₁ - ω₂) T *
          ((exteriorFormToCl11Stage4 (b T)).mulVec (vacVec 4)) (finsetToIdx 4 S)) =
        b.repr (ω₁ - ω₂) S * cS := by
      rw [Finset.sum_eq_single S]
      · rw [hSVec']; simp
      · intro T _ hTS
        obtain ⟨cT, _, hTVec⟩ := exteriorBasis4_mulVec_vacVec T
        have hTVec' : (exteriorFormToCl11Stage4 (b T)).mulVec (vacVec 4) =
            cT • Pi.single (finsetToIdx 4 T) (1 : ℝ) := hTVec
        rw [hTVec']
        simp [(finsetToIdx 4).injective.ne (Ne.symm hTS)]
      · intro hm; exact False.elim (hm (Finset.mem_univ S))
    rw [hTerm] at hCoord
    have hcNe : cS ≠ 0 := by
      intro h0; rw [h0] at hcSSq; norm_num at hcSSq
    exact (mul_eq_zero.mp hCoord).resolve_right hcNe
  have hSub0 : ω₁ - ω₂ = 0 := b.repr.injective (Finsupp.ext fun S => by simpa using hZeroCoeff S)
  exact sub_eq_zero.mp hSub0

/-- **Theorem 4A (Strict Injectivity of `exteriorFormToCl11Stage4`)**:
The algebra map `ExteriorAlgebra ℝ (Fin 4 → ℝ) →ₐ[ℝ] MatStage 4` is strictly injective on all
differential-form degrees `0..4` simultaneously via the vacuum Fock vector `vacVec 4`. -/
theorem exteriorFormToCl11Stage4_injective :
    Function.Injective exteriorFormToCl11Stage4 := by
  intro ω₁ ω₂ h
  exact exteriorFormToSpinorMap4_injective (congrArg (fun M => M.mulVec (vacVec 4)) h)

/-- Explicit `ℝ`-linear isomorphism `ExteriorAlgebra ℝ (Fin 4 → ℝ) ≃ₗ[ℝ] (Idx 4 → ℝ)`
identifying the `16`-dimensional exterior algebra with the Fock spinor column space of `MatStage 4`. -/
def exteriorFormToSpinorEquiv4 : ExteriorAlgebra ℝ (Fin 4 → ℝ) ≃ₗ[ℝ] (Idx 4 → ℝ) :=
  LinearEquiv.ofBijective exteriorFormToSpinorMap4
    ⟨exteriorFormToSpinorMap4_injective, by
      have : Module.Finite ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ)) :=
        Module.Finite.of_basis (Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra
      have hFR : Module.finrank ℝ (ExteriorAlgebra ℝ (Fin 4 → ℝ)) = Module.finrank ℝ (Idx 4 → ℝ) := by
        rw [Module.finrank_eq_card_basis ((Pi.basisFun ℝ (Fin 4)).ExteriorAlgebra),
          Fintype.card_finset, Fintype.card_fin, Module.finrank_pi, idx_card_pow_two 4]
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hFR).mp
        exteriorFormToSpinorMap4_injective⟩

/-- Exterior derivative 2-form `d𝒜(y) = ∑_{μ,ν} ∂_μ A_ν(y) dx^μ ∧ dx^ν` inside `MatStage 7`. -/
def ymExtDerivConnToTower (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) : MatStage 7 :=
  ∑ μ : Fin 4, ∑ ν : Fin 4,
    kronMatStage 3 4
      (ymRealifyHom (fderiv ℝ (fun z => A z ν) y (frameBasis μ)))
      (exteriorFormToCl11Stage4 (dx μ * dx ν))

private lemma exteriorFormToCl11Stage4_dx_swap_neg (μ ν : Fin 4) :
    exteriorFormToCl11Stage4 (dx ν * dx μ) = -(exteriorFormToCl11Stage4 (dx μ * dx ν)) := by
  rw [map_mul, map_mul, exteriorFormToCl11Stage4_dx, exteriorFormToCl11Stage4_dx]
  by_cases h : ν = μ
  · subst h
    rw [Cl55WittCAR.creation_sq 4 ν, neg_zero]
  · exact eq_neg_of_add_eq_zero_left
      (Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute 4 ν μ h)

private lemma scalar_half_add_half (a : ℝ) : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * a = a := by
  ring

/-- **Theorem 4B (Exact Cartan Curvature Equation `ℱ = d𝒜 + 𝒜 * 𝒜` in `MatStage 7`)**:
Matches `ymCurvatureFormToTower` identically to `ymExtDerivConnToTower` +
`ymConnectionFormToTower * ymConnectionFormToTower`. -/
theorem ymCurvatureFormToTower_eq_extDeriv_add_sq
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) :
    ymCurvatureFormToTower A y =
      ymExtDerivConnToTower A y +
        ymConnectionFormToTower A y * ymConnectionFormToTower A y := by
  have hDeriv :
      (∑ μ : Fin 4, ∑ ν : Fin 4,
        (1 / 2 : ℝ) • kronMatStage 3 4
          (ymRealifyHom (fderiv ℝ (fun z => A z ν) y (frameBasis μ) -
            fderiv ℝ (fun z => A z μ) y (frameBasis ν)))
          (exteriorFormToCl11Stage4 (dx μ * dx ν))) =
      ymExtDerivConnToTower A y := by
    have hSwap :
        (∑ μ : Fin 4, ∑ ν : Fin 4,
          kronMatStage 3 4
            (ymRealifyHom (fderiv ℝ (fun z => A z μ) y (frameBasis ν)))
            (exteriorFormToCl11Stage4 (dx μ * dx ν))) =
        -(ymExtDerivConnToTower A y) := by
      unfold ymExtDerivConnToTower
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [exteriorFormToCl11Stage4_dx_swap_neg μ ν]
      unfold kronMatStage
      rw [kron_neg_right_real, map_neg]
    have hTwo : (2 : ℝ) • ymExtDerivConnToTower A y =
        (∑ μ : Fin 4, ∑ ν : Fin 4,
          kronMatStage 3 4
            (ymRealifyHom (fderiv ℝ (fun z => A z ν) y (frameBasis μ) -
              fderiv ℝ (fun z => A z μ) y (frameBasis ν)))
            (exteriorFormToCl11Stage4 (dx μ * dx ν))) := by
      rw [two_smul]
      conv_lhs => rhs; rw [← neg_neg (ymExtDerivConnToTower A y), ← hSwap]
      unfold ymExtDerivConnToTower
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [map_sub]
      unfold kronMatStage
      rw [kron_sub_left_real, map_sub, sub_eq_add_neg]
    have hHalf := congrArg (fun X : MatStage 7 => (1 / 2 : ℝ) • X) hTwo
    rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul, Finset.smul_sum] at hHalf
    symm
    rw [hHalf]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.smul_sum]
  have hSplit : ymCurvatureFormToTower A y =
      (∑ μ : Fin 4, ∑ ν : Fin 4,
        (1 / 2 : ℝ) • kronMatStage 3 4
          (ymRealifyHom (fderiv ℝ (fun z => A z ν) y (frameBasis μ) -
            fderiv ℝ (fun z => A z μ) y (frameBasis ν)))
          (exteriorFormToCl11Stage4 (dx μ * dx ν))) +
      (∑ μ : Fin 4, ∑ ν : Fin 4,
        (1 / 2 : ℝ) • kronMatStage 3 4
          (ymRealifyHom (A y μ * A y ν - A y ν * A y μ))
          (exteriorFormToCl11Stage4 (dx μ * dx ν))) := by
    unfold ymCurvatureFormToTower
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    unfold continuumCurvature
    rw [map_add, kronMatStage_add_left, smul_add]
  rw [hSplit, hDeriv, ymConnectionFormToTower_sq_eq_commutator_twoForm A y]

/-- **Theorem 4C (Master Capstone: `Cl(1,1)^{⊗ n}` Colimit + Cartan Structure + OS Continuum Bridge)**:
Unifies strict exterior-form and `Mat4C` realification injectivity, multi-step `bondMap stageBond 7 m h7m`
and `ofStage 7` Cartan equation `ℱ = d𝒜 + 𝒜 * 𝒜`, `a → 0` Wilson plaquette and covariant-difference
convergence, the nonzero non-Abelian colimit witness (`continuumPlaquetteAction = 4 > 0`), and
`OsterwalderSchraderContinuumReconstruction.fourDim_os_continuum_bridge_boundary`. -/
theorem ym_cl11_direct_limit_and_os_continuum_bridge
    {m : ℕ} (h7m : 7 ≤ m)
    {N : ℕ} (J : Fin N → ℝ) (hJ : ∀ s, 0 < J s) (q : OSQuotient (multiSiteOSForm J hJ))
    {m_phys t : ℝ} (hm : 0 < m_phys) (ht : 0 ≤ t)
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ ν : Fin 4) (hA : ContDiff ℝ 2 A) (hΦ : DifferentiableAt ℝ Φ y) :
    let bMap := bondMap stageBond 7 m h7m
    let A_w : FourSpace → Fin 4 → Mat4C :=
      fun z β => circularConnectionMat4 (witnessCircularField z β)
    (Function.Injective exteriorFormToCl11Stage4 ∧ Function.Injective ymRealifyHom) ∧
    (bMap (ymCurvatureFormToTower A y) =
      bMap (ymExtDerivConnToTower A y) +
        bMap (ymConnectionFormToTower A y) * bMap (ymConnectionFormToTower A y)) ∧
    (ofStage 7 (ymCurvatureFormToTower A y) =
      ofStage 7 (ymExtDerivConnToTower A y) +
        ofStage 7 (ymConnectionFormToTower A y) * ofStage 7 (ymConnectionFormToTower A y)) ∧
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteFormToTower A y a)
      (𝓝[≠] 0) (𝓝 (ymExtDerivConnToTower A y +
        ymConnectionFormToTower A y * ymConnectionFormToTower A y)) ∧
    Filter.Tendsto (fun a : ℝ => ymRealifyHom (latticeCovariantDiff A Φ y μ a))
      (𝓝[≠] 0) (𝓝 (ymRealifyHom (continuumCovariantDeriv A Φ y μ))) ∧
    (ofStage 7 (ymCurvatureFormToTower A_w y) ≠ 0 ∧ continuumPlaquetteAction A_w y 0 1 = 4) ∧
    ((osQuotInner (multiSiteOSForm J hJ) q q = 0 ↔ q = 0) ∧
     (0 ≤ osQuotInner (multiSiteOSForm J hJ) q q) ∧
     Filter.Tendsto (fun a : ℝ => (Real.tanh (criticalCoupling m_phys a)) ^ (Nat.floor (t / a)))
       (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (Real.exp (-m_phys * t)))) := by
  dsimp only
  have hRealInj : Function.Injective ymRealifyHom := (ymRealifyHom_properties 0 0).1
  have hCartan := ymCurvatureFormToTower_eq_extDeriv_add_sq A y
  have hBond : bondMap stageBond 7 m h7m (ymCurvatureFormToTower A y) =
      bondMap stageBond 7 m h7m (ymExtDerivConnToTower A y) +
        bondMap stageBond 7 m h7m (ymConnectionFormToTower A y) *
          bondMap stageBond 7 m h7m (ymConnectionFormToTower A y) := by
    rw [hCartan, map_add, map_mul]
  have hLim : ofStage 7 (ymCurvatureFormToTower A y) =
      ofStage 7 (ymExtDerivConnToTower A y) +
        ofStage 7 (ymConnectionFormToTower A y) * ofStage 7 (ymConnectionFormToTower A y) := by
    rw [hCartan, map_add, map_mul]
  have hConv := tendsto_lattice_yang_mills_in_cl11_tower A Φ y μ ν hA hΦ
  have hPlaq : Filter.Tendsto (fun a : ℝ => wilsonPlaquetteFormToTower A y a) (𝓝[≠] 0)
      (𝓝 (ymExtDerivConnToTower A y +
        ymConnectionFormToTower A y * ymConnectionFormToTower A y)) := by
    rw [← hCartan]; exact hConv.2.1
  have hDir := ym_smooth_lattice_continuum_to_cl11_direct_limit A y
  have hWit := circularLattice_nonabelian_continuum_witness y
  have hOS := fourDim_os_continuum_bridge_boundary J hJ q hm ht A y μ ν hA
  exact ⟨⟨exteriorFormToCl11Stage4_injective, hRealInj⟩, hBond, hLim, hPlaq, hConv.1,
    ⟨hDir.2.2.2, hWit.2.2.2.1⟩, ⟨hOS.1, hOS.2.1, hOS.2.2.1⟩⟩

end ExteriorInjectivityAndOSBridge

end InfoGeometry.Canonical.YangMillsContinuumCl11TowerBridge
