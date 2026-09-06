import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Complex `Cl(3,0)` matrix-product classification

This module closes the explicit finite classification

`CliffordAlgebra q3 ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ`.

The proof follows the repository's existing matrix-corridor pattern:

* build the Pauli representation by `CliffordAlgebra.lift`;
* split the two simple blocks with the central chirality projector;
* prove surjectivity by an explicit preimage formula;
* prove injectivity by an eight-word spanning bound and finite-dimensional rank equality.

This file is intentionally standalone: it does not edit or depend on dirty aggregator state.
-/

open scoped Matrix

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Clifford.Cl3ComplexMatrixProduct

abbrev Vec3 : Type := ℂ × ℂ × ℂ
abbrev Mat2C : Type := Matrix (Fin 2) (Fin 2) ℂ
abbrev ProdMat2C : Type := Mat2C × Mat2C

@[simp] lemma I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  rw [pow_two, Complex.I_mul_I]

noncomputable def q3 : QuadraticForm ℂ Vec3 :=
  QuadraticMap.sq.prod (QuadraticMap.sq.prod QuadraticMap.sq)

@[simp] lemma q3_apply (v : Vec3) : q3 v = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
  simp [q3, QuadraticMap.prod_apply]
  ring

def s1 : Mat2C := !![(0 : ℂ), 1; 1, 0]
def s2 : Mat2C := !![(0 : ℂ), -Complex.I; Complex.I, 0]
def s3 : Mat2C := !![(1 : ℂ), 0; 0, -1]

lemma s1_sq : s1 * s1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [s1, Matrix.mul_apply, Fin.sum_univ_two]

lemma s2_sq : s2 * s2 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [s2, Matrix.mul_apply, Fin.sum_univ_two]

lemma s3_sq : s3 * s3 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [s3, Matrix.mul_apply, Fin.sum_univ_two]

noncomputable def gen : Vec3 →ₗ[ℂ] ProdMat2C where
  toFun v := (v.1 • s1 + v.2.1 • s2 + v.2.2 • s3,
    v.1 • s1 + v.2.1 • s2 - v.2.2 • s3)
  map_add' u v := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [s1, s2, s3] <;> ring
  map_smul' c v := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [s1, s2, s3, mul_add] <;> ring

lemma gen_sq (v : Vec3) : gen v * gen v = algebraMap ℂ ProdMat2C (q3 v) := by
  rcases v with ⟨a,b,c⟩
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gen, q3_apply, s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two,
      Algebra.algebraMap_eq_smul_one] <;> ring_nf <;> simp <;> ring

noncomputable def cl3ToProd : CliffordAlgebra q3 →ₐ[ℂ] ProdMat2C :=
  CliffordAlgebra.lift q3 ⟨gen, gen_sq⟩

noncomputable def matAlpha (M : Mat2C) : ℂ := (M 0 0 + M 1 1) / 2
noncomputable def matBeta (M : Mat2C) : ℂ := (M 0 1 + M 1 0) / 2
noncomputable def matGamma (M : Mat2C) : ℂ := (Complex.I * (M 0 1 - M 1 0)) / 2
noncomputable def matDelta (M : Mat2C) : ℂ := (M 0 0 - M 1 1) / 2

lemma mat2_decompose (M : Mat2C) :
    M = matAlpha M • (1 : Mat2C) + matBeta M • s1 + matGamma M • s2 + matDelta M • s3 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matAlpha, matBeta, matGamma, matDelta, s1, s2, s3, Matrix.smul_apply,
      Algebra.algebraMap_eq_smul_one] <;> ring_nf <;> simp <;> ring

noncomputable def e1 : CliffordAlgebra q3 := CliffordAlgebra.ι q3 (1,0,0)
noncomputable def e2 : CliffordAlgebra q3 := CliffordAlgebra.ι q3 (0,1,0)
noncomputable def e3 : CliffordAlgebra q3 := CliffordAlgebra.ι q3 (0,0,1)
noncomputable def volume : CliffordAlgebra q3 := e1 * (e2 * e3)
noncomputable def chirality : CliffordAlgebra q3 :=
  algebraMap ℂ (CliffordAlgebra q3) (-Complex.I) * volume
noncomputable def pL : CliffordAlgebra q3 := (2 : ℂ)⁻¹ • (1 + chirality)
noncomputable def pR : CliffordAlgebra q3 := (2 : ℂ)⁻¹ • (1 - chirality)

@[simp] lemma gen_e1 : gen (1,0,0) = (s1, s1) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [gen, s1, s2, s3]

@[simp] lemma gen_e2 : gen (0,1,0) = (s2, s2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [gen, s1, s2, s3]

@[simp] lemma gen_e3 : gen (0,0,1) = (s3, -s3) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [gen, s1, s2, s3]

lemma s1_mul_s2_mul_s3 : s1 * s2 * s3 = Complex.I • (1 : Mat2C) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [s1, s2, s3, Matrix.mul_apply, Fin.sum_univ_two]

lemma s1_mul_s2_mul_s3_right : s1 * (s2 * s3) = Complex.I • (1 : Mat2C) := by
  rw [← mul_assoc, s1_mul_s2_mul_s3]

@[simp] lemma cl3ToProd_e1 : cl3ToProd e1 = (s1, s1) := by
  rw [e1, cl3ToProd, CliffordAlgebra.lift_ι_apply]
  exact gen_e1

@[simp] lemma cl3ToProd_e2 : cl3ToProd e2 = (s2, s2) := by
  rw [e2, cl3ToProd, CliffordAlgebra.lift_ι_apply]
  exact gen_e2

@[simp] lemma cl3ToProd_e3 : cl3ToProd e3 = (s3, -s3) := by
  rw [e3, cl3ToProd, CliffordAlgebra.lift_ι_apply]
  exact gen_e3

lemma cl3ToProd_chirality : cl3ToProd chirality = (1, -1) := by
  simp [chirality, volume, s1_mul_s2_mul_s3_right, Algebra.algebraMap_eq_smul_one]
  constructor <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply] <;> ring

lemma cl3ToProd_pL : cl3ToProd pL = (1, 0) := by
  simp [pL, cl3ToProd_chirality]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply] <;> norm_num

lemma cl3ToProd_pR : cl3ToProd pR = (0, 1) := by
  simp [pR, cl3ToProd_chirality]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply] <;> norm_num

noncomputable def preimage (X : ProdMat2C) : CliffordAlgebra q3 :=
    (matAlpha X.1) • pL + (matBeta X.1) • (pL * e1) + (matGamma X.1) • (pL * e2)
  + (matDelta X.1) • (pL * e3)
  + (matAlpha X.2) • pR + (matBeta X.2) • (pR * e1) + (matGamma X.2) • (pR * e2)
  - (matDelta X.2) • (pR * e3)

lemma cl3ToProd_preimage (X : ProdMat2C) : cl3ToProd (preimage X) = X := by
  rcases X with ⟨A,B⟩
  simp only [preimage, map_add, map_sub, map_smul, map_mul, cl3ToProd_pL, cl3ToProd_pR,
    cl3ToProd_e1, cl3ToProd_e2, cl3ToProd_e3]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [matAlpha, matBeta, matGamma, matDelta, s1, s2, s3, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.smul_apply] <;> ring_nf <;> simp <;> ring

theorem cl3ToProd_surjective : Function.Surjective cl3ToProd :=
  fun X => ⟨preimage X, cl3ToProd_preimage X⟩

lemma e1_sq : e1 * e1 = 1 := by
  rw [e1, CliffordAlgebra.ι_sq_scalar]
  simp [q3_apply, Algebra.algebraMap_eq_smul_one]

lemma e2_sq : e2 * e2 = 1 := by
  rw [e2, CliffordAlgebra.ι_sq_scalar]
  simp [q3_apply, Algebra.algebraMap_eq_smul_one]

lemma e3_sq : e3 * e3 = 1 := by
  rw [e3, CliffordAlgebra.ι_sq_scalar]
  simp [q3_apply, Algebra.algebraMap_eq_smul_one]

lemma e1_mul_e2_neg : e1 * e2 = -(e2 * e1) := by
  rw [e1, e2, CliffordAlgebra.ι_mul_ι_comm]
  simp [q3, QuadraticMap.polar, QuadraticMap.prod_apply, Algebra.algebraMap_eq_smul_one]

lemma e1_mul_e3_neg : e1 * e3 = -(e3 * e1) := by
  rw [e1, e3, CliffordAlgebra.ι_mul_ι_comm]
  simp [q3, QuadraticMap.polar, QuadraticMap.prod_apply, Algebra.algebraMap_eq_smul_one]

lemma e2_mul_e3_neg : e2 * e3 = -(e3 * e2) := by
  rw [e2, e3, CliffordAlgebra.ι_mul_ι_comm]
  simp [q3, QuadraticMap.polar, QuadraticMap.prod_apply, Algebra.algebraMap_eq_smul_one]

lemma e2_mul_e1 : e2 * e1 = -(e1 * e2) := by
  have h := congrArg Neg.neg e1_mul_e2_neg
  simpa using h.symm

lemma e3_mul_e2 : e3 * e2 = -(e2 * e3) := by
  have h := congrArg Neg.neg e2_mul_e3_neg
  simpa using h.symm

lemma e3_mul_e1 : e3 * e1 = -(e1 * e3) := by
  have h := congrArg Neg.neg e1_mul_e3_neg
  simpa using h.symm

@[simp] lemma e1_mul_e1 : e1 * e1 = 1 := e1_sq
@[simp] lemma e2_mul_e2 : e2 * e2 = 1 := e2_sq
@[simp] lemma e3_mul_e3 : e3 * e3 = 1 := e3_sq

@[simp] lemma e2_mul_e1_rewrite : e2 * e1 = -(e1 * e2) := e2_mul_e1
@[simp] lemma e1_mul_e3_rewrite : e1 * e3 = -(e3 * e1) := e1_mul_e3_neg
@[simp] lemma e3_mul_e2_rewrite : e3 * e2 = -(e2 * e3) := e3_mul_e2

noncomputable def cl3BasisWord (i : Fin 8) : CliffordAlgebra q3 :=
  if i = 0 then 1
  else if i = 1 then e1
  else if i = 2 then e2
  else if i = 3 then e3
  else if i = 4 then e1 * e2
  else if i = 5 then e2 * e3
  else if i = 6 then e3 * e1
  else volume

abbrev cl3Span : Submodule ℂ (CliffordAlgebra q3) :=
  Submodule.span ℂ (Set.range cl3BasisWord)

lemma cl3BasisWord_mem_span (i : Fin 8) : cl3BasisWord i ∈ cl3Span :=
  Submodule.subset_span ⟨i, rfl⟩

@[simp] lemma one_mem_cl3Span : (1 : CliffordAlgebra q3) ∈ cl3Span := by
  simpa [cl3Span, cl3BasisWord] using cl3BasisWord_mem_span 0

@[simp] lemma e1_mem_cl3Span : e1 ∈ cl3Span := by
  simpa [cl3Span, cl3BasisWord] using cl3BasisWord_mem_span 1

@[simp] lemma e2_mem_cl3Span : e2 ∈ cl3Span := by
  simpa [cl3Span, cl3BasisWord] using cl3BasisWord_mem_span 2

@[simp] lemma e3_mem_cl3Span : e3 ∈ cl3Span := by
  simpa [cl3Span, cl3BasisWord] using cl3BasisWord_mem_span 3

@[simp] lemma e1e2_mem_cl3Span : e1 * e2 ∈ cl3Span := by
  simpa [cl3Span, cl3BasisWord] using cl3BasisWord_mem_span 4

@[simp] lemma e2e3_mem_cl3Span : e2 * e3 ∈ cl3Span := by
  simpa [cl3Span, cl3BasisWord] using cl3BasisWord_mem_span 5

@[simp] lemma e3e1_mem_cl3Span : e3 * e1 ∈ cl3Span := by
  simpa [cl3Span, cl3BasisWord] using cl3BasisWord_mem_span 6

@[simp] lemma volume_mem_cl3Span : volume ∈ cl3Span := by
  simpa [cl3Span, cl3BasisWord] using cl3BasisWord_mem_span 7

@[simp] lemma e2_mul_e3_mul_e1 : e2 * (e3 * e1) = volume := by
  rw [volume]
  calc
    e2 * (e3 * e1) = e2 * (-(e1 * e3)) := by rw [e3_mul_e1]
    _ = -(e2 * (e1 * e3)) := by rw [mul_neg]
    _ = -((e2 * e1) * e3) := by rw [mul_assoc]
    _ = -((-(e1 * e2)) * e3) := by rw [e2_mul_e1]
    _ = (e1 * e2) * e3 := by simp
    _ = e1 * (e2 * e3) := by rw [mul_assoc]

@[simp] lemma e3_mul_e1_mul_e2 : e3 * (e1 * e2) = volume := by
  rw [volume]
  calc
    e3 * (e1 * e2) = (e3 * e1) * e2 := by rw [mul_assoc]
    _ = (-(e1 * e3)) * e2 := by rw [e3_mul_e1]
    _ = -((e1 * e3) * e2) := by rw [neg_mul]
    _ = -(e1 * (e3 * e2)) := by rw [mul_assoc]
    _ = -(e1 * (-(e2 * e3))) := by rw [e3_mul_e2]
    _ = e1 * (e2 * e3) := by simp

@[simp] lemma e1_mul_e2_mul_e3 : e1 * (e2 * e3) = volume := by
  rfl

@[simp] lemma e1_mul_e1e2 : e1 * (e1 * e2) = e2 := by
  rw [← mul_assoc, e1_sq, one_mul]

@[simp] lemma e1_mul_e3e1 : e1 * (e3 * e1) = -e3 := by
  calc
    e1 * (e3 * e1) = (e1 * e3) * e1 := by rw [mul_assoc]
    _ = (-(e3 * e1)) * e1 := by rw [e1_mul_e3_neg]
    _ = -((e3 * e1) * e1) := by rw [neg_mul]
    _ = -e3 := by rw [mul_assoc, e1_sq, mul_one]

@[simp] lemma e1_mul_volume : e1 * volume = e2 * e3 := by
  rw [volume, ← mul_assoc, e1_sq, one_mul]

@[simp] lemma e2_mul_e1e2 : e2 * (e1 * e2) = -e1 := by
  calc
    e2 * (e1 * e2) = (e2 * e1) * e2 := by rw [mul_assoc]
    _ = (-(e1 * e2)) * e2 := by rw [e2_mul_e1]
    _ = -((e1 * e2) * e2) := by rw [neg_mul]
    _ = -e1 := by rw [mul_assoc, e2_sq, mul_one]

@[simp] lemma e2_mul_e2e3 : e2 * (e2 * e3) = e3 := by
  rw [← mul_assoc, e2_sq, one_mul]

@[simp] lemma e2_mul_volume : e2 * volume = e3 * e1 := by
  calc
    e2 * volume = e2 * (e1 * (e2 * e3)) := rfl
    _ = (e2 * e1) * (e2 * e3) := by rw [mul_assoc]
    _ = (-(e1 * e2)) * (e2 * e3) := by rw [e2_mul_e1]
    _ = -((e1 * e2) * (e2 * e3)) := by rw [neg_mul]
    _ = -(e1 * (e2 * (e2 * e3))) := by rw [mul_assoc]
    _ = -(e1 * e3) := by rw [e2_mul_e2e3]
    _ = e3 * e1 := by rw [e1_mul_e3_neg]; simp

@[simp] lemma e3_mul_e2e3 : e3 * (e2 * e3) = -e2 := by
  calc
    e3 * (e2 * e3) = (e3 * e2) * e3 := by rw [mul_assoc]
    _ = (-(e2 * e3)) * e3 := by rw [e3_mul_e2]
    _ = -((e2 * e3) * e3) := by rw [neg_mul]
    _ = -e2 := by rw [mul_assoc, e3_sq, mul_one]

@[simp] lemma e3_mul_e3e1 : e3 * (e3 * e1) = e1 := by
  rw [← mul_assoc, e3_sq, one_mul]

@[simp] lemma e3_mul_volume : e3 * volume = e1 * e2 := by
  calc
    e3 * volume = e3 * (e1 * (e2 * e3)) := rfl
    _ = (e3 * (e1 * e2)) * e3 := by
      rw [← mul_assoc e1 e2 e3, ← mul_assoc]
    _ = volume * e3 := by rw [e3_mul_e1_mul_e2]
    _ = (e1 * (e2 * e3)) * e3 := rfl
    _ = e1 * ((e2 * e3) * e3) := by rw [mul_assoc]
    _ = e1 * (e2 * (e3 * e3)) := by rw [mul_assoc]
    _ = e1 * e2 := by rw [e3_sq, mul_one]

lemma e1_mul_basis_mem (i : Fin 8) : e1 * cl3BasisWord i ∈ cl3Span := by
  fin_cases i <;>
    simp [cl3BasisWord, cl3Span]

lemma e2_mul_basis_mem (i : Fin 8) : e2 * cl3BasisWord i ∈ cl3Span := by
  fin_cases i <;>
    simp [cl3BasisWord, cl3Span]

lemma e3_mul_basis_mem (i : Fin 8) : e3 * cl3BasisWord i ∈ cl3Span := by
  fin_cases i <;>
    simp [cl3BasisWord, cl3Span]

lemma e1_mul_span_mem {x : CliffordAlgebra q3} (hx : x ∈ cl3Span) : e1 * x ∈ cl3Span := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact e1_mul_basis_mem i
  | zero => simpa using (Submodule.zero_mem cl3Span)
  | add x y _ _ hx hy => simpa [mul_add] using cl3Span.add_mem hx hy
  | smul a x _ hx => simpa [mul_smul_comm] using cl3Span.smul_mem a hx

lemma e2_mul_span_mem {x : CliffordAlgebra q3} (hx : x ∈ cl3Span) : e2 * x ∈ cl3Span := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact e2_mul_basis_mem i
  | zero => simpa using (Submodule.zero_mem cl3Span)
  | add x y _ _ hx hy => simpa [mul_add] using cl3Span.add_mem hx hy
  | smul a x _ hx => simpa [mul_smul_comm] using cl3Span.smul_mem a hx

lemma e3_mul_span_mem {x : CliffordAlgebra q3} (hx : x ∈ cl3Span) : e3 * x ∈ cl3Span := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨i, rfl⟩
      exact e3_mul_basis_mem i
  | zero => simpa using (Submodule.zero_mem cl3Span)
  | add x y _ _ hx hy => simpa [mul_add] using cl3Span.add_mem hx hy
  | smul a x _ hx => simpa [mul_smul_comm] using cl3Span.smul_mem a hx

lemma iota_mem_cl3Span (v : Vec3) : CliffordAlgebra.ι q3 v ∈ cl3Span := by
  rcases v with ⟨a,b,c⟩
  have h :
      CliffordAlgebra.ι q3 (a,b,c) =
        a • e1 + b • e2 + c • e3 := by
    have hv : (a, b, c) =
        a • ((1 : ℂ), (0 : ℂ), (0 : ℂ)) +
          b • ((0 : ℂ), (1 : ℂ), (0 : ℂ)) +
          c • ((0 : ℂ), (0 : ℂ), (1 : ℂ)) := by
      ext <;> simp
    rw [hv]
    rw [map_add, map_add, map_smul, map_smul, map_smul]
    rfl
  rw [h]
  exact cl3Span.add_mem
    (cl3Span.add_mem (cl3Span.smul_mem a e1_mem_cl3Span)
      (cl3Span.smul_mem b e2_mem_cl3Span))
    (cl3Span.smul_mem c e3_mem_cl3Span)

lemma iota_mul_span_mem (v : Vec3) {x : CliffordAlgebra q3}
    (hx : x ∈ cl3Span) : CliffordAlgebra.ι q3 v * x ∈ cl3Span := by
  rcases v with ⟨a,b,c⟩
  have h :
      CliffordAlgebra.ι q3 (a,b,c) =
        a • e1 + b • e2 + c • e3 := by
    have hv : (a, b, c) =
        a • ((1 : ℂ), (0 : ℂ), (0 : ℂ)) +
          b • ((0 : ℂ), (1 : ℂ), (0 : ℂ)) +
          c • ((0 : ℂ), (0 : ℂ), (1 : ℂ)) := by
      ext <;> simp
    rw [hv]
    rw [map_add, map_add, map_smul, map_smul, map_smul]
    rfl
  rw [h]
  simpa [add_mul, smul_mul_assoc] using
    cl3Span.add_mem
      (cl3Span.add_mem (cl3Span.smul_mem a (e1_mul_span_mem hx))
        (cl3Span.smul_mem b (e2_mul_span_mem hx)))
      (cl3Span.smul_mem c (e3_mul_span_mem hx))

theorem span_cl3BasisWord_top : cl3Span = ⊤ := by
  have h_all : ∀ x : CliffordAlgebra q3, x ∈ cl3Span := by
    intro x
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r =>
        simpa [Algebra.algebraMap_eq_smul_one] using cl3Span.smul_mem r one_mem_cl3Span
    | add a b ha hb => exact cl3Span.add_mem ha hb
    | ι_mul x v hx => exact iota_mul_span_mem v hx
  exact top_unique fun x _ => h_all x

lemma finrank_cl3_le_eight : Module.finrank ℂ (CliffordAlgebra q3) ≤ 8 := by
  simpa [cl3Span, Fintype.card_fin] using
    (finrank_le_of_span_eq_top (R := ℂ) (M := CliffordAlgebra q3)
      (v := cl3BasisWord) span_cl3BasisWord_top)

lemma finiteDimensional_cl3 : FiniteDimensional ℂ (CliffordAlgebra q3) := by
  have hsurj : Function.Surjective (Fintype.linearCombination ℂ cl3BasisWord) :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination
      (R := ℂ) (v := cl3BasisWord)).mp span_cl3BasisWord_top
  exact Module.Finite.of_surjective (Fintype.linearCombination ℂ cl3BasisWord) hsurj

lemma finrank_prodMat2C : Module.finrank ℂ ProdMat2C = 8 := by
  simp [ProdMat2C, Mat2C, Module.finrank_prod, Module.finrank_matrix, Fintype.card_fin]

lemma finrank_prod_le_finrank_cl3 :
    Module.finrank ℂ ProdMat2C ≤ Module.finrank ℂ (CliffordAlgebra q3) := by
  haveI : FiniteDimensional ℂ (CliffordAlgebra q3) := finiteDimensional_cl3
  have h_range : LinearMap.range cl3ToProd.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr cl3ToProd_surjective
  calc
    Module.finrank ℂ ProdMat2C = Module.finrank ℂ (⊤ : Submodule ℂ ProdMat2C) := by
      simp
    _ = Module.finrank ℂ (LinearMap.range cl3ToProd.toLinearMap) := by
      rw [h_range]
    _ ≤ Module.finrank ℂ (CliffordAlgebra q3) :=
      LinearMap.finrank_range_le cl3ToProd.toLinearMap

lemma finrank_cl3 : Module.finrank ℂ (CliffordAlgebra q3) = 8 := by
  refine le_antisymm finrank_cl3_le_eight ?_
  have h := finrank_prod_le_finrank_cl3
  rw [finrank_prodMat2C] at h
  exact h

lemma cl3ToProd_injective : Function.Injective cl3ToProd := by
  haveI : FiniteDimensional ℂ (CliffordAlgebra q3) := finiteDimensional_cl3
  have h_rank :
      Module.finrank ℂ (CliffordAlgebra q3) = Module.finrank ℂ ProdMat2C := by
    rw [finrank_cl3, finrank_prodMat2C]
  have h_surj : Function.Surjective cl3ToProd.toLinearMap := cl3ToProd_surjective
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_rank).mpr h_surj

noncomputable def cl3EquivProdMat2C : CliffordAlgebra q3 ≃ₐ[ℂ] ProdMat2C :=
  AlgEquiv.ofBijective cl3ToProd ⟨cl3ToProd_injective, cl3ToProd_surjective⟩

end InfoGeometry.Clifford.Cl3ComplexMatrixProduct
