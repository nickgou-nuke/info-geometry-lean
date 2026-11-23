/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic
import InfoGeometry.Clifford.ThreeDHurwitz
import InfoGeometry.Clifford.QuaternionPauliRealForm
import InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv

/-!
# Real-Algebra Signature Distinction: `Cl(3,0) ≅ M₂(ℂ)` vs `Cl(2,2) ≅ M₄(ℝ)`

This module establishes the real-algebra classification and signature separation
between the positive-definite 3D Clifford algebra `Cl(3,0) = Cl3 1 1 1` and the
split-signature 4D Clifford algebra `Cl(2,2) = Clsplit 2`:

* `pauli1`, `pauli2`, `pauli3`: Hermitian Pauli matrices on `Matrix (Fin 2) (Fin 2) ℂ`
  squaring to `1`, pairwise anticommuting, with product `Complex.I • 1`.
* `cl30EquivMat2C : Cl3 1 1 1 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ`: genuine real-algebra
  equivalence constructed via `CliffordAlgebra.lift`, an explicit 8-term Pauli preimage,
  and `Module.finrank ℝ = 8`.
* `cl22EquivMat4R : Clsplit 2 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`: real-algebra equivalence
  from `Cl11SplitTowerMatrixEquiv.splitTowerEquivMatrix 2` (`finrank = 16`).
* Center characterizations and `z ^ 2 = -1` invariants:
  - `Subalgebra.center ℝ (Cl3 1 1 1) ≃ₐ[ℝ] ℂ` (real `finrank = 2`), containing the
    central pseudoscalar `pseudoscalar30 = g0 * g1 * g2` with `pseudoscalar30 ^ 2 = -1`.
  - `Subalgebra.center ℝ (Clsplit 2) ≃ₐ[ℝ] ℝ` (real `finrank = 1`), containing no
    central element `z` with `z ^ 2 = -1`.
* Explicit real-algebra and center non-isomorphism theorems separating `Cl(3,0)` from
  `Cl(2,2)` and `M₂(ℂ)` from `M₄(ℝ)`.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl30RealMatrixSignature

open scoped Matrix
open InfoGeometry.Clifford.ThreeDHurwitz
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv

/-- Complex `2 × 2` matrices viewed as an `ℝ`-algebra. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Real `4 × 4` matrices viewed as an `ℝ`-algebra. -/
abbrev Mat4R := Matrix (Fin 4) (Fin 4) ℝ

/-- The real Clifford algebra `Cl(3,0)` of positive-definite 3D space. -/
abbrev Cl30 := Cl3 1 1 1

/-- The real split Clifford algebra `Cl(2,2)`. -/
abbrev Cl22 := Clsplit 2

/-! ### Section 1: Hermitian Pauli Matrices -/

/-- First Pauli matrix `σ₁` on `Matrix (Fin 2) (Fin 2) ℂ`. -/
def pauli1 : Mat2C := QuaternionPauliRealForm.sigma1

/-- Second Pauli matrix `σ₂` on `Matrix (Fin 2) (Fin 2) ℂ`. -/
def pauli2 : Mat2C := QuaternionPauliRealForm.sigma2

/-- Third Pauli matrix `σ₃` on `Matrix (Fin 2) (Fin 2) ℂ`. -/
def pauli3 : Mat2C := QuaternionPauliRealForm.sigma3

@[simp] theorem pauli1_sq : pauli1 * pauli1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli1, QuaternionPauliRealForm.sigma1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem pauli2_sq : pauli2 * pauli2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli2, QuaternionPauliRealForm.sigma2, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem pauli3_sq : pauli3 * pauli3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli3, QuaternionPauliRealForm.sigma3, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauli1_pauli2_anticomm : pauli1 * pauli2 + pauli2 * pauli1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli2, QuaternionPauliRealForm.sigma1, QuaternionPauliRealForm.sigma2]

theorem pauli1_pauli3_anticomm : pauli1 * pauli3 + pauli3 * pauli1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli3, QuaternionPauliRealForm.sigma1, QuaternionPauliRealForm.sigma3]

theorem pauli2_pauli3_anticomm : pauli2 * pauli3 + pauli3 * pauli2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli2, pauli3, QuaternionPauliRealForm.sigma2, QuaternionPauliRealForm.sigma3]

theorem pauli1_hermitian : pauli1ᴴ = pauli1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli1, QuaternionPauliRealForm.sigma1]

theorem pauli2_hermitian : pauli2ᴴ = pauli2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli2, QuaternionPauliRealForm.sigma2]

theorem pauli3_hermitian : pauli3ᴴ = pauli3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli3, QuaternionPauliRealForm.sigma3]

theorem pauli1_mul_pauli2_mul_pauli3 :
    pauli1 * pauli2 * pauli3 = Complex.I • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli2, pauli3, QuaternionPauliRealForm.sigma1,
      QuaternionPauliRealForm.sigma2, QuaternionPauliRealForm.sigma3,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem pauli1_mul_pauli2_ne : pauli1 * pauli2 ≠ pauli2 * pauli1 := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  have h00' : Complex.I = -Complex.I := by
    simpa [pauli1, pauli2, QuaternionPauliRealForm.sigma1, QuaternionPauliRealForm.sigma2,
      Matrix.mul_apply, Fin.sum_univ_two] using h00
  have him := congrArg Complex.im h00'
  norm_num at him

/-! ### Section 2: Clifford Lift `Cl3 1 1 1 →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ` and Preimage -/

/-- Real-linear map sending the standard basis of `Space3` to `pauli1`, `pauli2`, `pauli3`. -/
noncomputable def generatorMap : Space3 →ₗ[ℝ] Mat2C where
  toFun v := v.1 • pauli1 + v.2.1 • pauli2 + v.2.2 • pauli3
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply, add_smul] <;> ring
  map_smul' r v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, smul_add] <;> ring

@[simp] theorem generatorMap_e0 : generatorMap e0 = pauli1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generatorMap, e0, Matrix.add_apply]

@[simp] theorem generatorMap_e1 : generatorMap e1 = pauli2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generatorMap, e1, Matrix.add_apply]

@[simp] theorem generatorMap_e2 : generatorMap e2 = pauli3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generatorMap, e2, Matrix.add_apply]

theorem generatorMap_sq (v : Space3) :
    generatorMap v * generatorMap v = algebraMap ℝ Mat2C (Qdiag3 1 1 1 v) := by
  rcases v with ⟨a, b, c⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generatorMap, Qdiag3, pauli1, pauli2, pauli3,
      QuaternionPauliRealForm.sigma1, QuaternionPauliRealForm.sigma2,
      QuaternionPauliRealForm.sigma3, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Algebra.algebraMap_eq_smul_one] <;>
    (ring_nf <;> simp only [Complex.I_sq] <;> ring)

/-- Universal `ℝ`-algebra homomorphism `Cl(3,0) →ₐ[ℝ] M₂(ℂ)`. -/
noncomputable def cl30ToMat : Cl30 →ₐ[ℝ] Mat2C :=
  CliffordAlgebra.lift (Qdiag3 1 1 1) ⟨generatorMap, generatorMap_sq⟩

@[simp] theorem cl30ToMat_iota (v : Space3) :
    cl30ToMat (CliffordAlgebra.ι (Qdiag3 1 1 1) v) = generatorMap v :=
  CliffordAlgebra.lift_ι_apply generatorMap generatorMap_sq v

@[simp] theorem cl30ToMat_g0 : cl30ToMat (g0 1 1 1) = pauli1 := by
  rw [g0, cl30ToMat_iota, generatorMap_e0]

@[simp] theorem cl30ToMat_g1 : cl30ToMat (g1 1 1 1) = pauli2 := by
  rw [g1, cl30ToMat_iota, generatorMap_e1]

@[simp] theorem cl30ToMat_g2 : cl30ToMat (g2 1 1 1) = pauli3 := by
  rw [g2, cl30ToMat_iota, generatorMap_e2]

/-- The pseudoscalar `g0 * g1 * g2` in `Cl3 1 1 1`. -/
noncomputable def pseudoscalar30 : Cl30 :=
  g0 1 1 1 * g1 1 1 1 * g2 1 1 1

@[simp] theorem cl30ToMat_pseudoscalar :
    cl30ToMat pseudoscalar30 = Complex.I • (1 : Mat2C) := by
  simp only [pseudoscalar30, map_mul, cl30ToMat_g0, cl30ToMat_g1, cl30ToMat_g2]
  exact pauli1_mul_pauli2_mul_pauli3

noncomputable def pauliCoeff0 (M : Mat2C) : ℂ := (M 0 0 + M 1 1) / 2
noncomputable def pauliCoeff1 (M : Mat2C) : ℂ := (M 0 1 + M 1 0) / 2
noncomputable def pauliCoeff2 (M : Mat2C) : ℂ := Complex.I * (M 0 1 - M 1 0) / 2
noncomputable def pauliCoeff3 (M : Mat2C) : ℂ := (M 0 0 - M 1 1) / 2

theorem mat2C_pauli_decompose (M : Mat2C) :
    M = pauliCoeff0 M • (1 : Mat2C) + pauliCoeff1 M • pauli1 +
      pauliCoeff2 M • pauli2 + pauliCoeff3 M • pauli3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliCoeff0, pauliCoeff1, pauliCoeff2, pauliCoeff3,
      pauli1, pauli2, pauli3, QuaternionPauliRealForm.sigma1,
      QuaternionPauliRealForm.sigma2, QuaternionPauliRealForm.sigma3,
      Matrix.smul_apply] <;>
    (ring_nf <;> simp only [Complex.I_sq] <;> ring)

/-- Preimage of a complex scalar `z • 1` in `Cl3 1 1 1`. -/
noncomputable def complexScalarPreimage (z : ℂ) : Cl30 :=
  z.re • (1 : Cl30) + z.im • pseudoscalar30

theorem cl30ToMat_complexScalarPreimage (z : ℂ) :
    cl30ToMat (complexScalarPreimage z) = z • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexScalarPreimage, cl30ToMat_pseudoscalar, Matrix.smul_apply]

/-- Explicit 8-term Pauli preimage of `M : Matrix (Fin 2) (Fin 2) ℂ` in `Cl3 1 1 1`. -/
noncomputable def cl30Preimage (M : Mat2C) : Cl30 :=
  complexScalarPreimage (pauliCoeff0 M) +
    complexScalarPreimage (pauliCoeff1 M) * g0 1 1 1 +
    complexScalarPreimage (pauliCoeff2 M) * g1 1 1 1 +
    complexScalarPreimage (pauliCoeff3 M) * g2 1 1 1

theorem cl30ToMat_cl30Preimage (M : Mat2C) :
    cl30ToMat (cl30Preimage M) = M := by
  simp only [cl30Preimage, map_add, map_mul, cl30ToMat_complexScalarPreimage,
    cl30ToMat_g0, cl30ToMat_g1, cl30ToMat_g2]
  simp only [smul_mul_assoc, one_mul]
  exact (mat2C_pauli_decompose M).symm

theorem cl30ToMat_surjective : Function.Surjective cl30ToMat := by
  intro M
  exact ⟨cl30Preimage M, cl30ToMat_cl30Preimage M⟩

/-! ### Section 3: Dimension `8`, Injectivity, and `cl30EquivMat2C` -/

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

theorem space3_finrank : Module.finrank ℝ Space3 = 3 := by
  simp [Space3, Module.finrank_prod]

noncomputable def space3Basis : Module.Basis (Fin 3) ℝ Space3 :=
  (Module.finBasis ℝ Space3).reindex (finCongr space3_finrank)

noncomputable def exterior3Basis :
    Module.Basis (Finset (Fin 3)) ℝ (ExteriorAlgebra ℝ Space3) :=
  space3Basis.ExteriorAlgebra

theorem exterior3_finrank :
    Module.finrank ℝ (ExteriorAlgebra ℝ Space3) = 8 := by
  rw [Module.finrank_eq_card_basis exterior3Basis]
  simp [Fintype.card_finset]

instance exterior3_finiteDimensional :
    FiniteDimensional ℝ (ExteriorAlgebra ℝ Space3) :=
  Module.Basis.finiteDimensional_of_finite exterior3Basis

instance cl30_finiteDimensional : FiniteDimensional ℝ Cl30 :=
  LinearEquiv.finiteDimensional (CliffordAlgebra.equivExterior (Qdiag3 1 1 1)).symm

theorem cl30_finrank : Module.finrank ℝ Cl30 = 8 := by
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior (Qdiag3 1 1 1))]
  exact exterior3_finrank

theorem mat2C_finrank : Module.finrank ℝ Mat2C = 8 := by
  simp [Mat2C, Module.finrank_matrix, Complex.finrank_real_complex]

theorem cl30ToMat_injective : Function.Injective cl30ToMat := by
  have h_rank : Module.finrank ℝ Cl30 = Module.finrank ℝ Mat2C := by
    rw [cl30_finrank, mat2C_finrank]
  have h_surj : Function.Surjective cl30ToMat.toLinearMap := cl30ToMat_surjective
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_rank).mpr h_surj

/-- The real Clifford algebra `Cl(3,0)` is `ℝ`-algebra isomorphic to `M₂(ℂ)`. -/
noncomputable def cl30EquivMat2C : Cl3 1 1 1 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  AlgEquiv.ofBijective cl30ToMat ⟨cl30ToMat_injective, cl30ToMat_surjective⟩

@[simp] theorem cl30EquivMat2C_g0 : cl30EquivMat2C (g0 1 1 1) = pauli1 :=
  cl30ToMat_g0

@[simp] theorem cl30EquivMat2C_g1 : cl30EquivMat2C (g1 1 1 1) = pauli2 :=
  cl30ToMat_g1

@[simp] theorem cl30EquivMat2C_g2 : cl30EquivMat2C (g2 1 1 1) = pauli3 :=
  cl30ToMat_g2

@[simp] theorem cl30EquivMat2C_pseudoscalar :
    cl30EquivMat2C pseudoscalar30 = Complex.I • (1 : Mat2C) :=
  cl30ToMat_pseudoscalar

theorem pseudoscalar30_sq : pseudoscalar30 ^ 2 = -1 := by
  apply cl30EquivMat2C.injective
  rw [map_pow, cl30EquivMat2C_pseudoscalar, map_neg, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem pseudoscalar30_mem_center :
    pseudoscalar30 ∈ Subalgebra.center ℝ (Cl3 1 1 1) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  apply cl30EquivMat2C.injective
  rw [map_mul, map_mul, cl30EquivMat2C_pseudoscalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Explicit non-commutativity witness on `Cl3 1 1 1`. -/
theorem cl30_generators_noncommutative :
    g0 1 1 1 * g1 1 1 1 ≠ g1 1 1 1 * g0 1 1 1 := by
  intro h
  have h_mat := congrArg cl30EquivMat2C h
  simp only [map_mul, cl30EquivMat2C_g0, cl30EquivMat2C_g1] at h_mat
  exact pauli1_mul_pauli2_ne h_mat

/-! ### Section 4: `Cl(2,2) ≃ₐ[ℝ] M₄(ℝ)` and Center Characterizations -/

/-- Real-algebra isomorphism `Cl(2,2) ≃ₐ[ℝ] M₄(ℝ)` from the split Clifford tower. -/
noncomputable def cl22EquivMat4R : Clsplit 2 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  (splitTowerEquivMatrix 2).trans
    (Matrix.reindexAlgEquiv ℝ ℝ (finCongr (by norm_num : 2 ^ 2 = 4)))

theorem mat4R_finrank : Module.finrank ℝ Mat4R = 16 := by
  simp [Mat4R, Module.finrank_matrix]

theorem cl22_finrank : Module.finrank ℝ (Clsplit 2) = 16 := by
  rw [LinearEquiv.finrank_eq cl22EquivMat4R.toLinearEquiv]
  exact mat4R_finrank

/-- Explicit non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℝ`. -/
theorem mat4R_noncommutative :
    (Matrix.single 0 1 (1 : ℝ) : Mat4R) * Matrix.single 1 0 1 ≠
      Matrix.single 1 0 1 * Matrix.single 0 1 1 := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp [Matrix.mul_apply, Matrix.single] at h00

/-- Explicit non-commutativity witness on `Clsplit 2`. -/
theorem cl22_noncommutative : ∃ a b : Clsplit 2, a * b ≠ b * a := by
  refine ⟨cl22EquivMat4R.symm (Matrix.single 0 1 (1 : ℝ)),
    cl22EquivMat4R.symm (Matrix.single 1 0 (1 : ℝ)), ?_⟩
  intro h
  have h_mat := congrArg cl22EquivMat4R h
  simp only [map_mul, AlgEquiv.apply_symm_apply] at h_mat
  exact mat4R_noncommutative h_mat

/-- Any `R`-algebra equivalence induces an `R`-algebra equivalence on centers. -/
noncomputable def centerAlgEquivOfAlgEquiv {R A B : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    (e : A ≃ₐ[R] B) :
    Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B :=
  (Subalgebra.equivMapOfInjective (Subalgebra.center R A) e.toAlgHom e.injective).trans
    (Subalgebra.equivOfEq _ _ (Subalgebra.map_center_eq e))

theorem mat2C_center_eq_scalar {z : Mat2C} (hz : z ∈ Subalgebra.center ℝ Mat2C) :
    z = Matrix.scalar (Fin 2) (z 0 0) := by
  rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map] at hz
  rcases hz with ⟨c, _, rfl⟩
  ext i j
  simp [Matrix.scalarAlgHom_apply, Matrix.scalar_apply]

theorem scalar_mem_center_mat2C (c : ℂ) :
    Matrix.scalar (Fin 2) c ∈ Subalgebra.center ℝ Mat2C := by
  rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
  exact ⟨c, Subalgebra.mem_center_iff.mpr (fun b => mul_comm b c), rfl⟩

/-- The center of `M₂(ℂ)` as an `ℝ`-algebra is isomorphic to `ℂ`. -/
noncomputable def mat2CCenterEquivComplex :
    Subalgebra.center ℝ (Matrix (Fin 2) (Fin 2) ℂ) ≃ₐ[ℝ] ℂ where
  toFun z := (z : Mat2C) 0 0
  invFun c := ⟨Matrix.scalar (Fin 2) c, scalar_mem_center_mat2C c⟩
  left_inv z := Subtype.ext (mat2C_center_eq_scalar z.2).symm
  right_inv c := by simp [Matrix.scalar_apply]
  map_mul' x y := by
    have hx := mat2C_center_eq_scalar x.2
    have hy := mat2C_center_eq_scalar y.2
    change ((x : Mat2C) * (y : Mat2C)) 0 0 = (x : Mat2C) 0 0 * (y : Mat2C) 0 0
    rw [hx, hy]
    simp [Matrix.scalar_apply]
  map_add' _ _ := rfl
  commutes' r := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]

theorem mat2C_center_finrank :
    Module.finrank ℝ (Subalgebra.center ℝ (Matrix (Fin 2) (Fin 2) ℂ)) = 2 := by
  rw [LinearEquiv.finrank_eq mat2CCenterEquivComplex.toLinearEquiv]
  exact Complex.finrank_real_complex

/-- The center of `Cl(3,0)` as an `ℝ`-algebra is isomorphic to `ℂ`. -/
noncomputable def cl30CenterEquivComplex :
    Subalgebra.center ℝ (Cl3 1 1 1) ≃ₐ[ℝ] ℂ :=
  (centerAlgEquivOfAlgEquiv cl30EquivMat2C).trans mat2CCenterEquivComplex

theorem cl30_center_finrank :
    Module.finrank ℝ (Subalgebra.center ℝ (Cl3 1 1 1)) = 2 := by
  rw [LinearEquiv.finrank_eq cl30CenterEquivComplex.toLinearEquiv]
  exact Complex.finrank_real_complex

/-- The center of `M₄(ℝ)` as an `ℝ`-algebra is isomorphic to `ℝ`. -/
noncomputable def mat4RCenterEquivReal :
    Subalgebra.center ℝ (Matrix (Fin 4) (Fin 4) ℝ) ≃ₐ[ℝ] ℝ :=
  (Subalgebra.equivOfEq _ _ (Algebra.IsCentral.center_eq_bot ℝ Mat4R)).trans
    (Algebra.botEquiv ℝ Mat4R)

theorem mat4R_center_finrank :
    Module.finrank ℝ (Subalgebra.center ℝ (Matrix (Fin 4) (Fin 4) ℝ)) = 1 := by
  rw [LinearEquiv.finrank_eq mat4RCenterEquivReal.toLinearEquiv]
  exact Module.finrank_self ℝ

/-- The center of `Cl(2,2)` as an `ℝ`-algebra is isomorphic to `ℝ`. -/
noncomputable def cl22CenterEquivReal :
    Subalgebra.center ℝ (Clsplit 2) ≃ₐ[ℝ] ℝ :=
  (centerAlgEquivOfAlgEquiv cl22EquivMat4R).trans mat4RCenterEquivReal

theorem cl22_center_finrank :
    Module.finrank ℝ (Subalgebra.center ℝ (Clsplit 2)) = 1 := by
  rw [LinearEquiv.finrank_eq cl22CenterEquivReal.toLinearEquiv]
  exact Module.finrank_self ℝ

/-! ### Section 5: `z ^ 2 = -1` Central Invariants and Non-Isomorphism Theorems -/

theorem mat2C_exists_central_sq_neg_one :
    ∃ z ∈ Subalgebra.center ℝ (Matrix (Fin 2) (Fin 2) ℂ), z ^ 2 = -1 := by
  refine ⟨Complex.I • (1 : Mat2C), ?_, ?_⟩
  · rw [Subalgebra.mem_center_iff]
    intro b
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem cl30_exists_central_sq_neg_one :
    ∃ z ∈ Subalgebra.center ℝ (Cl3 1 1 1), z ^ 2 = -1 :=
  ⟨pseudoscalar30, pseudoscalar30_mem_center, pseudoscalar30_sq⟩

private theorem real_sq_ne_neg_one (r : ℝ) : r ^ 2 ≠ -1 := by
  intro h
  nlinarith [sq_nonneg r]

theorem mat4R_no_central_sq_neg_one :
    ∀ z ∈ Subalgebra.center ℝ (Matrix (Fin 4) (Fin 4) ℝ), z ^ 2 ≠ -1 := by
  intro z hz hsq
  obtain ⟨r, rfl⟩ := (Algebra.IsCentral.mem_center_iff ℝ).mp hz
  have h_scalar : algebraMap ℝ Mat4R (r ^ 2) = algebraMap ℝ Mat4R (-1) := by
    simpa [map_pow, map_neg, map_one] using hsq
  have hr : r ^ 2 = -1 := (algebraMap ℝ Mat4R).injective h_scalar
  exact real_sq_ne_neg_one r hr

theorem cl22_no_central_sq_neg_one :
    ∀ z ∈ Subalgebra.center ℝ (Clsplit 2), z ^ 2 ≠ -1 := by
  intro z hz hsq
  have hz_mat : cl22EquivMat4R z ∈ Subalgebra.center ℝ Mat4R :=
    MulEquivClass.apply_mem_center cl22EquivMat4R hz
  have hsq_mat : (cl22EquivMat4R z) ^ 2 = -1 := by
    calc
      (cl22EquivMat4R z) ^ 2 = cl22EquivMat4R (z ^ 2) := (map_pow cl22EquivMat4R z 2).symm
      _ = cl22EquivMat4R (-1) := by rw [hsq]
      _ = -1 := by simp
  exact mat4R_no_central_sq_neg_one (cl22EquivMat4R z) hz_mat hsq_mat

theorem mat2C_center_not_algEquiv_mat4R_center :
    ¬ Nonempty (Subalgebra.center ℝ (Matrix (Fin 2) (Fin 2) ℂ) ≃ₐ[ℝ]
      Subalgebra.center ℝ (Matrix (Fin 4) (Fin 4) ℝ)) := by
  rintro ⟨e⟩
  have h_dim := LinearEquiv.finrank_eq e.toLinearEquiv
  rw [mat2C_center_finrank, mat4R_center_finrank] at h_dim
  omega

theorem cl30_center_not_algEquiv_cl22_center :
    ¬ Nonempty (Subalgebra.center ℝ (Cl3 1 1 1) ≃ₐ[ℝ] Subalgebra.center ℝ (Clsplit 2)) := by
  rintro ⟨e⟩
  have h_dim := LinearEquiv.finrank_eq e.toLinearEquiv
  rw [cl30_center_finrank, cl22_center_finrank] at h_dim
  omega

theorem mat2C_not_algEquiv_mat4R :
    ¬ Nonempty (Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) := by
  rintro ⟨e⟩
  exact mat2C_center_not_algEquiv_mat4R_center ⟨centerAlgEquivOfAlgEquiv e⟩

theorem cl30_not_algEquiv_cl22 :
    ¬ Nonempty (Cl3 1 1 1 ≃ₐ[ℝ] Clsplit 2) := by
  rintro ⟨e⟩
  exact cl30_center_not_algEquiv_cl22_center ⟨centerAlgEquivOfAlgEquiv e⟩

end InfoGeometry.Clifford.Cl30RealMatrixSignature
