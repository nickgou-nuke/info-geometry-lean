/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.FreedCliffordSuspension
import InfoGeometry.OperatorAlgebra.PeirceHadamardNative
import InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita
import InfoGeometry.OperatorAlgebra.GradedMatrixMorita

/-!
# The canonical graded Morita reduction of the split Clifford atom

The existing faithful `Cl(1,1)` matrix equivalence sends its Clifford grading
element to the swap matrix. Conjugation by the existing Walsh unit changes
this to the standard `diag(1,-1)` grading. We prove the grading equation on
every Clifford element, then construct the actual graded module equivalence.

The final specialization computes Freed's ordered generator map on the
positive real line. Its image is the target parity matrix. The suspension
maps source vectors to ambient even elements; it is not asserted to preserve
the source and ambient canonical Clifford gradings.
-/

noncomputable section

open CategoryTheory
open scoped Matrix Matrix.Module

namespace InfoGeometry.Clifford.Cl11GradedMorita

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.OperatorAlgebra.PeirceHadamardNative
open InfoGeometry.OperatorAlgebra.PeirceSpine.InnerGradedMorita
open InfoGeometry.OperatorAlgebra.GradedMatrixMorita

local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- Similarity by the existing Walsh unit, as an actual algebra equivalence. -/
def walshConjugation : Mat2 ≃ₐ[ℝ] Mat2 where
  toFun M := (walshUnit : Mat2ˣ).val * M * (walshUnit⁻¹).val
  invFun M := (walshUnit⁻¹ : Mat2ˣ).val * M * walshUnit.val
  left_inv M := by simp [mul_assoc]
  right_inv M := by simp [mul_assoc]
  map_mul' M N := by simp [mul_assoc]
  map_add' M N := by simp [mul_add, add_mul]
  commutes' r := by
    rw [← Algebra.commutes r (walshUnit : Mat2ˣ).val, mul_assoc]
    simp

@[simp] theorem walshConjugation_apply (M : Mat2) :
    walshConjugation M =
      (walshUnit : Mat2ˣ).val * M * (walshUnit⁻¹).val := rfl

theorem walshConjugation_Eplus : walshConjugation Eplus = J1 := by
  rw [walshConjugation_apply, walshUnit_similarity]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Eplus, J1, invOf_eq_inv]

theorem walshConjugation_Eminus : walshConjugation Eminus = -Eminus := by
  rw [walshConjugation_apply, walshUnit_similarity]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Eminus, invOf_eq_inv]

theorem walshConjugation_J1 : walshConjugation J1 = Eplus := by
  rw [walshConjugation_apply, walshUnit_similarity]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Eplus, J1, invOf_eq_inv]

/-- The faithful split-Clifford representation in the standard `1|1` basis. -/
def cl11StandardEquiv : CliffordAlgebra q11 ≃ₐ[ℝ] Mat2 :=
  cl11EquivMat.trans walshConjugation

@[simp] theorem cl11StandardEquiv_iota_pos :
    cl11StandardEquiv (CliffordAlgebra.ι q11 (1, 0)) = J1 := by
  change walshConjugation (cl11EquivMat (CliffordAlgebra.ι q11 (1, 0))) = J1
  rw [cl11EquivMat_iota_pos, walshConjugation_Eplus]

@[simp] theorem cl11StandardEquiv_iota_neg :
    cl11StandardEquiv (CliffordAlgebra.ι q11 (0, 1)) = -Eminus := by
  change walshConjugation (cl11EquivMat (CliffordAlgebra.ι q11 (0, 1))) = -Eminus
  rw [cl11EquivMat_iota_neg, walshConjugation_Eminus]

@[simp] theorem cl11StandardEquiv_J1_cl : cl11StandardEquiv J1_cl = Eplus := by
  change walshConjugation (cl11EquivMat
    (CliffordAlgebra.ι q11 (1, 0) * CliffordAlgebra.ι q11 (0, 1))) = Eplus
  rw [map_mul, cl11EquivMat_iota_pos, cl11EquivMat_iota_neg,
    Eplus_mul_Eminus, walshConjugation_J1]

/-- The canonical Clifford grading is implemented by the ordered split
volume, whose square is one. -/
theorem J1_cl_sq : J1_cl * J1_cl = 1 := by
  apply cl11StandardEquiv.injective
  rw [map_mul, cl11StandardEquiv_J1_cl, map_one, Eplus_sq]

theorem cl11StandardEquiv_ι (v : Vec11) :
    cl11StandardEquiv (CliffordAlgebra.ι q11 v) = v.1 • J1 - v.2 • Eminus := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  have hι : CliffordAlgebra.ι q11 v =
      v.1 • CliffordAlgebra.ι q11 (1, 0) +
        v.2 • CliffordAlgebra.ι q11 (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add, ← hv]
  rw [hι, map_add, map_smul, map_smul,
    cl11StandardEquiv_iota_pos, cl11StandardEquiv_iota_neg]
  simp only [smul_neg, sub_eq_add_neg]

private theorem standard_parity_generator (v : Vec11) :
    Eplus * cl11StandardEquiv (CliffordAlgebra.ι q11 v) * Eplus =
      -cl11StandardEquiv (CliffordAlgebra.ι q11 v) := by
  rw [cl11StandardEquiv_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, Eminus, J1, Matrix.mul_apply, Fin.sum_univ_two]

/-- The standard representation intertwines canonical Clifford involution
with standard matrix parity, on every algebra element. -/
theorem cl11StandardEquiv_involute (x : CliffordAlgebra q11) :
    cl11StandardEquiv (CliffordAlgebra.involute x) =
      Eplus * cl11StandardEquiv x * Eplus := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, Eplus_sq]
  | ι v =>
      simpa only [CliffordAlgebra.involute_ι, map_neg] using
        (standard_parity_generator v).symm
  | mul x y hx hy =>
      rw [map_mul, map_mul, hx, hy, map_mul]
      calc
        (Eplus * cl11StandardEquiv x * Eplus) *
            (Eplus * cl11StandardEquiv y * Eplus) =
          Eplus * cl11StandardEquiv x * (Eplus * Eplus) *
            cl11StandardEquiv y * Eplus := by noncomm_ring
        _ = Eplus * (cl11StandardEquiv x * cl11StandardEquiv y) * Eplus := by
          rw [Eplus_sq]
          simp only [mul_one, mul_assoc]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, mul_add, add_mul]

/-- Inner conjugation by the native ordered Clifford volume is exactly the
canonical grading, rather than an arbitrary chosen involution. -/
theorem involute_eq_J1_cl_conj (x : CliffordAlgebra q11) :
    CliffordAlgebra.involute x = J1_cl * x * J1_cl := by
  apply cl11StandardEquiv.injective
  rw [cl11StandardEquiv_involute, map_mul, map_mul, cl11StandardEquiv_J1_cl]

/-- The exact grading equation consumed by graded change of rings. -/
theorem cl11StandardEquiv_grade (x : CliffordAlgebra q11) :
    cl11StandardEquiv ((CliffordAlgebra.involuteEquiv (Q := q11)).toRingEquiv x) =
      matrixGrade (RingEquiv.refl ℝ) (cl11StandardEquiv x) := by
  rw [matrixGrade_eq_parity_conj]
  simpa only [RingEquiv.refl_apply, Matrix.map_id, Eplus] using
    cl11StandardEquiv_involute x

/-- Homogeneous even Clifford elements have zero off-diagonal entries in
the standard graded representation. -/
theorem cl11StandardEquiv_even_offDiagonal {x : CliffordAlgebra q11}
    (hx : x ∈ CliffordAlgebra.evenOdd q11 0) :
    cl11StandardEquiv x 0 1 = 0 ∧ cl11StandardEquiv x 1 0 = 0 := by
  have h := cl11StandardEquiv_grade x
  change cl11StandardEquiv (CliffordAlgebra.involute x) = _ at h
  rw [CliffordAlgebra.involute_eq_of_mem_even hx] at h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  have h10 := congrArg (fun M : Mat2 => M 1 0) h
  change cl11StandardEquiv x 0 1 = -cl11StandardEquiv x 0 1 at h01
  change cl11StandardEquiv x 1 0 = -cl11StandardEquiv x 1 0 at h10
  constructor <;> linarith

/-- Homogeneous odd Clifford elements have zero diagonal entries. -/
theorem cl11StandardEquiv_odd_diagonal {x : CliffordAlgebra q11}
    (hx : x ∈ CliffordAlgebra.evenOdd q11 1) :
    cl11StandardEquiv x 0 0 = 0 ∧ cl11StandardEquiv x 1 1 = 0 := by
  have h := cl11StandardEquiv_grade x
  change cl11StandardEquiv (CliffordAlgebra.involute x) = _ at h
  rw [CliffordAlgebra.involute_eq_of_mem_odd hx, map_neg] at h
  have h00 := congrArg (fun M : Mat2 => M 0 0) h
  have h11 := congrArg (fun M : Mat2 => M 1 1) h
  change -cl11StandardEquiv x 0 0 = cl11StandardEquiv x 0 0 at h00
  change -cl11StandardEquiv x 1 1 = cl11StandardEquiv x 1 1 at h11
  constructor <;> linarith

/-- A native ordinary Morita equivalence built from the faithful matrix
presentation and Mathlib's actual matrix Morita functors. -/
def cl11MoritaEquivalence : MoritaEquivalence ℝ (CliffordAlgebra q11) ℝ :=
  (MoritaEquivalence.ofAlgEquiv cl11StandardEquiv).trans ℝ
    ((moritaEquivalenceMatrix ℝ ℝ (0 : Fin 2)).symm ℝ)

/-- The inner-grading encoding supplied by the existing owner, now attached
to the actual canonical split-Clifford grading. -/
def cl11InnerGradedEquivalence :
    Action (ModuleCat (CliffordAlgebra q11)) C2 ≌ Action (ModuleCat ℝ) C2 :=
  gradedEquivalence cl11MoritaEquivalence.eqv

theorem cl11Module_grading_action
    (X : Action (ModuleCat (CliffordAlgebra q11)) C2)
    (a : CliffordAlgebra q11) (x : X.V) :
    grading J1_cl X (a • x) = CliffordAlgebra.involute a • grading J1_cl X x := by
  rw [grading_smul J1_cl J1_cl_sq, involute_eq_J1_cl_conj]

/-- The canonical graded Clifford category is equivalent to real graded
modules, with the equivalence constructed through the explicit representation. -/
def cl11GradedEquivalence :
    GradedModuleCat (CliffordAlgebra.involuteEquiv (Q := q11)).toRingEquiv ≌
      GradedModuleCat (RingEquiv.refl ℝ) :=
  (ofRingEquiv (CliffordAlgebra.involuteEquiv (Q := q11)).toRingEquiv
    (matrixGrade (RingEquiv.refl ℝ)) cl11StandardEquiv.toRingEquiv
    cl11StandardEquiv_grade).trans (matrixEquivalence (RingEquiv.refl ℝ)).symm

section FreedLine

open InfoGeometry.Clifford.FreedCliffordSuspension

/-- The positive suspension of the positive real line is the existing
split quadratic form; the identity vector map gives the native isometry. -/
def positiveLineIsometry :
    (positiveForm (QuadraticMap.sq (R := ℝ))).IsometryEquiv q11 where
  toLinearEquiv := LinearEquiv.refl ℝ (ℝ × ℝ)
  map_app' v := by
    rw [q11_apply, positiveForm_apply]
    change v.1 ^ 2 - v.2 ^ 2 = v.1 * v.1 - v.2 * v.2
    ring

def positiveLineToCl11 :
    CliffordAlgebra (positiveForm (QuadraticMap.sq (R := ℝ))) ≃ₐ[ℝ]
      CliffordAlgebra q11 :=
  CliffordAlgebra.equivOfIsometry positiveLineIsometry

@[simp] theorem positiveLineToCl11_ι (v : ℝ × ℝ) :
    positiveLineToCl11
        (CliffordAlgebra.ι (positiveForm (QuadraticMap.sq (R := ℝ))) v) =
      CliffordAlgebra.ι q11 v := by
  simp [positiveLineToCl11, positiveLineIsometry]
  rfl

/-- Freed's ordered suspension represented in the standard graded matrix
basis. This is a representation of the whole source Clifford algebra. -/
def freedPositiveLineRepresentation :
    CliffordAlgebra (QuadraticMap.sq (R := ℝ)) →ₐ[ℝ] Mat2 :=
  cl11StandardEquiv.toAlgHom.comp
    (positiveLineToCl11.toAlgHom.comp (positiveMap (QuadraticMap.sq (R := ℝ))))

/-- The source vector maps to `positive * negative`, with precisely that
order; its represented value is the standard parity matrix times the vector. -/
theorem freedPositiveLineRepresentation_ι (t : ℝ) :
    freedPositiveLineRepresentation (CliffordAlgebra.ι (QuadraticMap.sq (R := ℝ)) t) =
      t • Eplus := by
  change cl11StandardEquiv (positiveLineToCl11
    (positiveMap (QuadraticMap.sq (R := ℝ))
      (CliffordAlgebra.ι (QuadraticMap.sq (R := ℝ)) t))) = t • Eplus
  rw [positiveMap_ι, map_mul, positiveLineToCl11_ι, positiveLineToCl11_ι]
  have ht : (t, (0 : ℝ)) = t • ((1 : ℝ), 0) := by ext <;> simp
  rw [ht, map_smul, smul_mul_assoc, map_smul]
  exact congrArg (fun x : Mat2 => t • x) cl11StandardEquiv_J1_cl

/-- The represented source generator is ambient even, matching the exact
even-subalgebra target of the ordered suspension. -/
theorem freedPositiveLineRepresentation_ι_even (t : ℝ) :
    matrixGrade (RingEquiv.refl ℝ)
        (freedPositiveLineRepresentation (CliffordAlgebra.ι (QuadraticMap.sq (R := ℝ)) t)) =
      freedPositiveLineRepresentation (CliffordAlgebra.ι (QuadraticMap.sq (R := ℝ)) t) := by
  rw [freedPositiveLineRepresentation_ι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Eplus]

end FreedLine
end InfoGeometry.Clifford.Cl11GradedMorita
