import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Real Pauli Representation of Cl(1,1)

This module proves the algebra isomorphism `CliffordAlgebra q11 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ`
using the real Pauli matrices:
* `σ₃ = !![1, 0; 0, -1]` (squares to 1)
* `ε  = !![0, 1; -1, 0]` (squares to -1)
* `σ₁ = !![0, 1; 1, 0]` (the product σ₃ε)
-/

open scoped Matrix
open scoped Quaternion
open FiniteDimensional

namespace InfoGeometry.Clifford.Cl11Matrix

abbrev Vec11 : Type := ℝ × ℝ
abbrev Mat2  : Type := Matrix (Fin 2) (Fin 2) ℝ

/-- Standard split signature quadratic form on ℝ¹,¹ : q(x,y) = x² − y² -/
noncomputable def q11 : QuadraticForm ℝ Vec11 :=
  CliffordAlgebraQuaternion.Q (1 : ℝ) (-1 : ℝ)

@[simp] lemma q11_apply (v : Vec11) : q11 v = v.1 ^ 2 - v.2 ^ 2 := by
  dsimp [q11, CliffordAlgebraQuaternion.Q]
  ring

-- Real Pauli matrices
def Eplus  : Mat2 := !![(1 : ℝ), 0; 0, (-1 : ℝ)]  -- σ₃
def Eminus : Mat2 := !![(0 : ℝ), 1; (-1 : ℝ), 0] -- ε = iσ₂
def J1     : Mat2 := !![(0 : ℝ), 1; 1, 0]        -- σ₁

lemma Eplus_sq : Eplus * Eplus = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Eplus, Matrix.mul_apply, Fin.sum_univ_two]

lemma Eminus_sq : Eminus * Eminus = -1 • (1 : Mat2) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Eminus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

lemma Eplus_mul_Eminus : Eplus * Eminus = J1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Eplus, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two]

lemma J1_sq : J1 * J1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J1, Matrix.mul_apply, Fin.sum_univ_two]

lemma J1_transpose : J1ᵀ = J1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J1, Matrix.transpose_apply]

/-- The generating linear map v ↦ γ(v) mapping to real Pauli matrices. -/
noncomputable def gen : Vec11 →ₗ[ℝ] Mat2 where
  toFun v := v.1 • Eplus + v.2 • Eminus
  map_add' u v := by 
    ext i j; fin_cases i <;> fin_cases j <;> (simp [Eplus, Eminus, Matrix.add_apply]; try ring)
  map_smul' c v := by 
    ext i j; fin_cases i <;> fin_cases j <;> (simp [Eplus, Eminus, Matrix.smul_apply]; try ring)


lemma gen_sq (v : Vec11) : gen v * gen v = (q11 v) • (1 : Mat2) := by
  rcases v with ⟨a, b⟩
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [gen, q11_apply, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]; ring)

/-- Algebra morphism Cl(1,1) → Mat₂(ℝ) induced by the Pauli representation. -/
noncomputable def cl11ToMat : CliffordAlgebra q11 →ₐ[ℝ] Mat2 :=
  CliffordAlgebra.lift q11 ⟨gen, fun v => by
    simp [Algebra.algebraMap_eq_smul_one, gen_sq v]⟩

@[simp] theorem cl11ToMat_iota_pos :
    cl11ToMat (CliffordAlgebra.ι q11 (1, 0)) = Eplus := by
  simp [cl11ToMat, gen, Eplus, Eminus]

@[simp] theorem cl11ToMat_iota_neg :
    cl11ToMat (CliffordAlgebra.ι q11 (0, 1)) = Eminus := by
  simp [cl11ToMat, gen, Eplus, Eminus]

theorem cl11ToMat_iota_pos_sq :
    cl11ToMat (CliffordAlgebra.ι q11 (1, 0)) *
        cl11ToMat (CliffordAlgebra.ι q11 (1, 0)) = 1 := by
  rw [cl11ToMat_iota_pos, Eplus_sq]

theorem cl11ToMat_iota_neg_sq :
    cl11ToMat (CliffordAlgebra.ι q11 (0, 1)) *
        cl11ToMat (CliffordAlgebra.ι q11 (0, 1)) = -1 := by
  rw [cl11ToMat_iota_neg, Eminus_sq]
  simp

theorem cl11ToMat_iota_pos_neg_anticomm :
    cl11ToMat (CliffordAlgebra.ι q11 (1, 0)) *
        cl11ToMat (CliffordAlgebra.ι q11 (0, 1)) +
      cl11ToMat (CliffordAlgebra.ι q11 (0, 1)) *
        cl11ToMat (CliffordAlgebra.ι q11 (1, 0)) = 0 := by
  rw [cl11ToMat_iota_pos, cl11ToMat_iota_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

-- Decomposition of any 2x2 matrix into the Pauli basis
noncomputable def alpha (M : Mat2) : ℝ := (M 0 0 + M 1 1) / 2
noncomputable def beta  (M : Mat2) : ℝ := (M 0 0 - M 1 1) / 2
noncomputable def delta (M : Mat2) : ℝ := (M 0 1 + M 1 0) / 2
noncomputable def gamma (M : Mat2) : ℝ := (M 0 1 - M 1 0) / 2

theorem mat2_decompose (M : Mat2) :
    M = (alpha M) • (1 : Mat2) + (beta M) • Eplus + (gamma M) • Eminus + (delta M) • J1 := by
  ext i j; fin_cases i <;> fin_cases j <;> (simp [alpha, beta, gamma, delta, Eplus, Eminus, J1, Matrix.smul_apply, Matrix.add_apply]; ring)

noncomputable def J1_cl : CliffordAlgebra q11 :=
  (CliffordAlgebra.ι q11 (1, 0)) * (CliffordAlgebra.ι q11 (0, 1))

/-- Inverse mapping from matrices back to Clifford elements. -/
noncomputable def preimage (M : Mat2) : CliffordAlgebra q11 :=
    (alpha M) • 1
  + (beta M)  • (CliffordAlgebra.ι q11 (1, 0))
  + (gamma M) • (CliffordAlgebra.ι q11 (0, 1))
  + (delta M) • J1_cl

lemma cl11ToMat_preimage (M : Mat2) : cl11ToMat (preimage M) = M := by
  simp only [preimage, J1_cl, map_add, map_smul, map_mul, map_one, cl11ToMat, CliffordAlgebra.lift_ι_apply]
  have h1 : gen (1, 0) = Eplus := by ext i j; fin_cases i <;> fin_cases j <;> simp [gen, Eplus, Eminus]
  have h2 : gen (0, 1) = Eminus := by ext i j; fin_cases i <;> fin_cases j <;> simp [gen, Eplus, Eminus]
  simp only [h1, h2]
  have he : Eplus * Eminus = J1 := Eplus_mul_Eminus
  simp only [he]
  exact (mat2_decompose M).symm

lemma cl11ToMat_surjective : Function.Surjective cl11ToMat :=
  fun M ↦ ⟨preimage M, cl11ToMat_preimage M⟩

lemma finrank_mat2 : Module.finrank ℝ Mat2 = 4 := by
  simp [Mat2, Module.finrank_matrix, Module.finrank_self]

/-- Prove dim(Cl(1,1)) = 4 using the quaternion equivalence already in Mathlib. -/
lemma finrank_cl11 : Module.finrank ℝ (CliffordAlgebra q11) = 4 := by
  let e1 : CliffordAlgebra q11 ≃ₐ[ℝ] ℍ[ℝ, 1, 0, -1] := CliffordAlgebraQuaternion.equiv
  let e2 : ℍ[ℝ, 1, 0, -1] ≃ₗ[ℝ] (Fin 4 → ℝ) := QuaternionAlgebra.linearEquivTuple 1 0 (-1)
  let e3 : CliffordAlgebra q11 ≃ₗ[ℝ] (Fin 4 → ℝ) := e1.toLinearEquiv.trans e2
  rw [LinearEquiv.finrank_eq e3]
  simp [Fintype.card_fin]

/-- The algebra isomorphism Cl(1,1) ≃ Mat₂(ℝ). -/
noncomputable def cl11EquivMat : CliffordAlgebra q11 ≃ₐ[ℝ] Mat2 :=
  AlgEquiv.ofBijective cl11ToMat (by
    constructor
    · -- Injectivity via dimension equality and surjectivity
      have h_rank : Module.finrank ℝ (CliffordAlgebra q11) = Module.finrank ℝ Mat2 := by
        rw [finrank_cl11, finrank_mat2]
      have h_surj : Function.Surjective (cl11ToMat.toLinearMap) := cl11ToMat_surjective
      let e1 : CliffordAlgebra q11 ≃ₐ[ℝ] ℍ[ℝ, 1, 0, -1] := CliffordAlgebraQuaternion.equiv
      let e2 : ℍ[ℝ, 1, 0, -1] ≃ₗ[ℝ] (Fin 4 → ℝ) := QuaternionAlgebra.linearEquivTuple 1 0 (-1)
      haveI : FiniteDimensional ℝ (CliffordAlgebra q11) := 
        LinearEquiv.finiteDimensional (e1.toLinearEquiv.trans e2).symm
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_rank).mpr h_surj
    · -- Surjectivity
      exact cl11ToMat_surjective)

/-! ## 5. Generator laws transported through the algebra equivalence -/

@[simp] theorem cl11EquivMat_iota_pos :
    cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) = Eplus := by
  exact cl11ToMat_iota_pos

@[simp] theorem cl11EquivMat_iota_neg :
    cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)) = Eminus := by
  exact cl11ToMat_iota_neg

theorem cl11EquivMat_iota_pos_sq :
    cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) *
        cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) = 1 := by
  rw [cl11EquivMat_iota_pos]
  exact Eplus_sq

theorem cl11EquivMat_iota_neg_sq :
    cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)) *
        cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)) = -1 := by
  rw [cl11EquivMat_iota_neg]
  simpa using Eminus_sq

theorem cl11EquivMat_iota_pos_neg_anticomm :
    cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) *
        cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)) +
      cl11EquivMat (CliffordAlgebra.ι q11 (0, 1)) *
        cl11EquivMat (CliffordAlgebra.ι q11 (1, 0)) = 0 := by
  simpa [cl11EquivMat] using cl11ToMat_iota_pos_neg_anticomm

end InfoGeometry.Clifford.Cl11Matrix
