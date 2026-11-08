import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic
import InfoGeometry.Clifford.ThreeDHurwitz
import InfoGeometry.Clifford.Cl11SplitQuaternions

/-!
# Universal Clifford Algebra Isomorphism Cl(1,2) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ

This module formalizes the complete native Mathlib universal Clifford algebra
isomorphism between `Cl(1,2)` and `Matrix (Fin 2) (Fin 2) ℂ` over `ℝ`.

Key components:
* `q12`: diagonal quadratic form of signature `(+1, -1, -1)` on `Space3`.
* `generatorMap`: linear map sending generators to `e₁C`, `e₂C`, `fC`.
* `cl12ToMat`: universal Clifford algebra homomorphism via `CliffordAlgebra.lift`.
* `cl12Preimage` / `cl12ToMat_surjective`: surjectivity via explicit basis decomposition.
* `exterior_finrank` / `cl12_finrank` / `mat2C_finrank`: dimension calculation (= 8).
* `cl12ToMat_injective`: injectivity via dimension equality and surjectivity.
* `cl12EquivMat`: the established algebra isomorphism `Cl(1,2) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ`.
* `volume_sq` and `volume_commutes`: properties of the central 3D volume element.
-/

noncomputable section

open scoped Matrix

namespace InfoGeometry.Clifford.Cl12RealCliffordEquivalence

open InfoGeometry.Clifford.ThreeDHurwitz
open InfoGeometry.Clifford.Cl11

abbrev Vec12 := Space3
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The quadratic form with diagonal signs `(+1,-1,-1)`. -/
noncomputable def q12 : QuadraticForm ℝ Vec12 := Qdiag3 1 (-1) (-1)

abbrev Cl12 := CliffordAlgebra q12

def basis0 : Vec12 := (1, (0, 0))
def basis1 : Vec12 := (0, (1, 0))
def basis2 : Vec12 := (0, (0, 1))

/-- The real-linear generator map into the complex matrix carrier. -/
noncomputable def generatorMap : Vec12 →ₗ[ℝ] Mat2C where
  toFun v := v.1 • e₁C + v.2.1 • e₂C + v.2.2 • fC
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply, add_smul] <;> ring
  map_smul' r v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, smul_add] <;> ring

@[simp] theorem generatorMap_basis0 : generatorMap basis0 = e₁C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generatorMap, basis0, Matrix.add_apply]

@[simp] theorem generatorMap_basis1 : generatorMap basis1 = e₂C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generatorMap, basis1, Matrix.add_apply]

@[simp] theorem generatorMap_basis2 : generatorMap basis2 = fC := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generatorMap, basis2, Matrix.add_apply]

/-- The generator map satisfies the full diagonal quadratic relation. -/
theorem generatorMap_sq (v : Vec12) :
    generatorMap v * generatorMap v =
      algebraMap ℝ Mat2C (q12 v) := by
  rcases v with ⟨a, b, c⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [generatorMap, q12, Qdiag3, e₁C, e₂C, fC, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply, Algebra.algebraMap_eq_smul_one];
     ring_nf; try rw [Complex.I_sq]; ring)

/-- The universal Clifford representation `Cl(1,2) → M₂(ℂ)`. -/
noncomputable def cl12ToMat : Cl12 →ₐ[ℝ] Mat2C :=
  CliffordAlgebra.lift q12 ⟨generatorMap, generatorMap_sq⟩

@[simp] theorem cl12ToMat_iota (v : Vec12) :
    cl12ToMat (CliffordAlgebra.ι q12 v) = generatorMap v :=
  CliffordAlgebra.lift_ι_apply generatorMap generatorMap_sq v

@[simp] theorem cl12ToMat_basis0 :
    cl12ToMat (CliffordAlgebra.ι q12 basis0) = e₁C := by
  rw [cl12ToMat_iota, generatorMap_basis0]

@[simp] theorem cl12ToMat_basis1 :
    cl12ToMat (CliffordAlgebra.ι q12 basis1) = e₂C := by
  rw [cl12ToMat_iota, generatorMap_basis1]

@[simp] theorem cl12ToMat_basis2 :
    cl12ToMat (CliffordAlgebra.ι q12 basis2) = fC := by
  rw [cl12ToMat_iota, generatorMap_basis2]

/-! ### The central three-dimensional volume in the represented algebra -/

/-- The central 3D volume element in `Cl(1,2)`. -/
noncomputable def volume : Cl12 :=
  CliffordAlgebra.ι q12 basis0 *
    (CliffordAlgebra.ι q12 basis1 * CliffordAlgebra.ι q12 basis2)

theorem cl12ToMat_volume : cl12ToMat volume = I_3D := by
  simp only [volume, map_mul, cl12ToMat_basis0, cl12ToMat_basis1, cl12ToMat_basis2]
  rw [I_3D, mul_assoc]

theorem represented_volume_eq_imaginary :
    cl12ToMat volume = -Complex.I • (1 : Mat2C) := by
  rw [cl12ToMat_volume, I_3D_eq_imaginary]

theorem represented_volume_sq :
    cl12ToMat volume * cl12ToMat volume = -1 := by
  rw [represented_volume_eq_imaginary]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem represented_volume_commutes (M : Mat2C) :
    cl12ToMat volume * M = M * cl12ToMat volume := by
  rw [cl12ToMat_volume]
  exact I_3D_comm M

/-! ### Explicit matrix preimages and surjectivity -/

noncomputable def coeff00 (M : Mat2C) : ℂ := (M 0 0 + M 1 1) / 2
noncomputable def coeff11 (M : Mat2C) : ℂ := (M 0 0 - M 1 1) / 2
noncomputable def coeff01 (M : Mat2C) : ℂ := (M 1 0 - M 0 1) / 2
noncomputable def coeff10 (M : Mat2C) : ℂ := -(M 0 1 + M 1 0) / 2

/-- Complex Pauli-basis decomposition of an arbitrary two by two matrix. -/
theorem mat2_complex_decompose (M : Mat2C) :
    M = coeff00 M • (1 : Mat2C) + coeff11 M • e₁C +
      coeff01 M • e₂C + coeff10 M • (e₁C * e₂C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [coeff00, coeff11, coeff01, coeff10, e₁C, e₂C, Matrix.smul_apply]; ring)

/-- A complex scalar is represented over the real Clifford algebra by the real
scalar plus the central represented volume. -/
noncomputable def complexScalarPreimage (z : ℂ) : Cl12 :=
  (z.re : ℝ) • (1 : Cl12) - z.im • volume

theorem cl12ToMat_complexScalarPreimage (z : ℂ) :
    cl12ToMat (complexScalarPreimage z) = z • (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexScalarPreimage, cl12ToMat_volume, I_3D_eq_imaginary,
      Matrix.smul_apply, Matrix.sub_apply]

/-- Explicit algebraic preimage assembled from the four real split-quaternion
words and their central-volume multiples. -/
noncomputable def cl12Preimage (M : Mat2C) : Cl12 :=
  complexScalarPreimage (coeff00 M) +
    complexScalarPreimage (coeff11 M) * CliffordAlgebra.ι q12 basis0 +
    complexScalarPreimage (coeff01 M) * CliffordAlgebra.ι q12 basis1 +
    complexScalarPreimage (coeff10 M) *
      (CliffordAlgebra.ι q12 basis0 * CliffordAlgebra.ι q12 basis1)

theorem cl12ToMat_cl12Preimage (M : Mat2C) :
    cl12ToMat (cl12Preimage M) = M := by
  simp only [cl12Preimage, map_add, map_mul, cl12ToMat_complexScalarPreimage,
    cl12ToMat_basis0, cl12ToMat_basis1]
  simp only [smul_mul_assoc, one_mul]
  exact (mat2_complex_decompose M).symm

theorem cl12ToMat_surjective : Function.Surjective cl12ToMat := by
  intro M
  exact ⟨cl12Preimage M, cl12ToMat_cl12Preimage M⟩

/-! ### Finite dimensionality, finrank, and algebra isomorphism -/

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

theorem vec12_finrank : Module.finrank ℝ Vec12 = 3 := by
  simp [Vec12, Module.finrank_prod]

noncomputable def vec12Basis : Module.Basis (Fin 3) ℝ Vec12 :=
  (Module.finBasis ℝ Vec12).reindex (finCongr vec12_finrank)

noncomputable def exteriorBasis :
    Module.Basis (Finset (Fin 3)) ℝ (ExteriorAlgebra ℝ Vec12) :=
  vec12Basis.ExteriorAlgebra

theorem exterior_finrank :
    Module.finrank ℝ (ExteriorAlgebra ℝ Vec12) = 8 := by
  rw [Module.finrank_eq_card_basis exteriorBasis]
  simp [Fintype.card_finset]

instance exterior_finiteDimensional :
    FiniteDimensional ℝ (ExteriorAlgebra ℝ Vec12) :=
  Module.Basis.finiteDimensional_of_finite exteriorBasis

instance cl12_finiteDimensional : FiniteDimensional ℝ Cl12 :=
  LinearEquiv.finiteDimensional (CliffordAlgebra.equivExterior q12).symm

theorem cl12_finrank : Module.finrank ℝ Cl12 = 8 := by
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior q12)]
  exact exterior_finrank

theorem mat2C_finrank : Module.finrank ℝ Mat2C = 8 := by
  simp [Mat2C, Module.finrank_matrix, Complex.finrank_real_complex]

theorem cl12ToMat_injective : Function.Injective cl12ToMat := by
  have h_rank : Module.finrank ℝ Cl12 = Module.finrank ℝ Mat2C := by
    rw [cl12_finrank, mat2C_finrank]
  have h_surj : Function.Surjective cl12ToMat.toLinearMap := cl12ToMat_surjective
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_rank).mpr h_surj

/-- The real Clifford algebra of signature `(1,2)` is explicitly isomorphic
to the complex two by two matrix algebra, regarded as a real algebra. -/
noncomputable def cl12EquivMat : Cl12 ≃ₐ[ℝ] Mat2C :=
  AlgEquiv.ofBijective cl12ToMat ⟨cl12ToMat_injective, cl12ToMat_surjective⟩

/-- The represented central volume is central already in the abstract native
Clifford algebra, by injectivity of the established equivalence. -/
theorem volume_commutes (x : Cl12) : volume * x = x * volume := by
  apply cl12ToMat_injective
  rw [map_mul, map_mul, cl12ToMat_volume]
  exact I_3D_comm (cl12ToMat x)

/-- The native volume squares to minus one, transported back from its explicit
complex matrix image through injectivity. -/
theorem volume_sq : volume * volume = -1 := by
  apply cl12ToMat_injective
  simp only [map_mul, map_neg, map_one, cl12ToMat_volume]
  exact I_3D_sq

/-- Certificate of non-commutativity in the represented complex matrix algebra. -/
theorem mat_generators_noncommutative : e₁C * e₂C ≠ e₂C * e₁C := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  revert h01
  simp [e₁C, e₂C, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- Certificate of non-commutativity of the native Clifford generators. -/
theorem generators_noncommutative :
    CliffordAlgebra.ι q12 basis0 * CliffordAlgebra.ι q12 basis1 ≠
    CliffordAlgebra.ι q12 basis1 * CliffordAlgebra.ι q12 basis0 := by
  intro h
  have h_mat := congrArg cl12ToMat h
  simp only [map_mul, cl12ToMat_basis0, cl12ToMat_basis1] at h_mat
  exact mat_generators_noncommutative h_mat

end InfoGeometry.Clifford.Cl12RealCliffordEquivalence
