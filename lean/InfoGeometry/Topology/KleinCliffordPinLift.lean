/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Topology.KleinDeckRepresentation
import InfoGeometry.Twistor.TwistorKinematicTensor
import InfoGeometry.Algebra.DeWittPeirceChiralBridge
import Mathlib

/-!
# Explicit Clifford lifts of the Klein reflection

Both quadratic signatures are realized by native CliffordAlgebra homomorphisms.
The reflected tangent vector and the affine glide are separate. A lift's square
is additional data: +1 and -1 have the same reflected tangent action. This does
not claim a classification of Pin bundles or turn a nonorientable base into Spin.
-/
noncomputable section
namespace InfoGeometry.Topology.KleinCliffordPinLift
open KleinQuotientDeckInvariants KleinDeckRepresentation
open scoped KleinDeckRepresentation Matrix

abbrev Tangent := Fin 2 → ℝ
abbrev Spinor := Fin 2 → ℂ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def positiveForm : QuadraticForm ℝ Tangent :=
  QuadraticMap.sq.comp (LinearMap.proj 0) + QuadraticMap.sq.comp (LinearMap.proj 1)

def negativeForm : QuadraticForm ℝ Tangent := -positiveForm

@[simp] theorem positiveForm_apply (v : Tangent) : positiveForm v=v 0*v 0+v 1*v 1 := rfl
@[simp] theorem negativeForm_apply (v : Tangent) : negativeForm v=-(v 0*v 0+v 1*v 1) := rfl

def vectorPlus : Tangent →ₗ[ℝ] Mat where
  toFun v := !![(v 1:ℂ),(v 0:ℂ); (v 0:ℂ),-(v 1:ℂ)]
  map_add' v w := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' r v := by ext i j; fin_cases i <;> fin_cases j <;> simp [smul_eq_mul]

def vectorMinus : Tangent →ₗ[ℝ] Mat := Complex.I • vectorPlus

theorem vectorPlus_square (v : Tangent) :
    vectorPlus v * vectorPlus v=algebraMap ℝ Mat (positiveForm v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vectorPlus,Matrix.mul_apply,Fin.sum_univ_two,Matrix.algebraMap_matrix_apply,
      positiveForm] <;> ring

theorem vectorMinus_square (v : Tangent) :
    vectorMinus v * vectorMinus v=algebraMap ℝ Mat (negativeForm v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vectorMinus,vectorPlus,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.algebraMap_matrix_apply,positiveForm,negativeForm,smul_eq_mul,Complex.I_sq]
      <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def positiveRepresentation : CliffordAlgebra positiveForm →ₐ[ℝ] Mat :=
  CliffordAlgebra.lift positiveForm ⟨vectorPlus,vectorPlus_square⟩

def negativeRepresentation : CliffordAlgebra negativeForm →ₐ[ℝ] Mat :=
  CliffordAlgebra.lift negativeForm ⟨vectorMinus,vectorMinus_square⟩

@[simp] theorem positiveRepresentation_vector (v : Tangent) :
    positiveRepresentation (CliffordAlgebra.ι positiveForm v)=vectorPlus v :=
  CliffordAlgebra.lift_ι_apply _ _ _

@[simp] theorem negativeRepresentation_vector (v : Tangent) :
    negativeRepresentation (CliffordAlgebra.ι negativeForm v)=vectorMinus v :=
  CliffordAlgebra.lift_ι_apply _ _ _

def reflectionPlus : Mat := !![0,1;1,0]
def reflectionMinus : Mat := Complex.I • reflectionPlus

theorem reflectionPlus_square : reflectionPlus*reflectionPlus=1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [reflectionPlus,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]

theorem reflectionMinus_square : reflectionMinus*reflectionMinus=-1 := by
  simp [reflectionMinus,smul_mul_assoc,mul_smul_comm,smul_smul,
    reflectionPlus_square,Complex.I_sq]

def plusUnit : Matˣ := ⟨reflectionPlus,reflectionPlus,reflectionPlus_square,reflectionPlus_square⟩
def minusUnit : Matˣ := ⟨reflectionMinus,-reflectionMinus,
  by rw [mul_neg,reflectionMinus_square,neg_neg],
  by rw [neg_mul,reflectionMinus_square,neg_neg]⟩

def reflected (v : Tangent) : Tangent := ![-v 0,v 1]

/-- Twisted adjoint, not ordinary conjugation, gives the vector reflection. -/
theorem plus_twisted_adjoint (v : Tangent) :
    -(plusUnit.val * vectorPlus v * plusUnit.inv)=vectorPlus (reflected v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusUnit,reflectionPlus,vectorPlus,reflected,Matrix.mul_apply,Fin.sum_univ_two]

/-- The negative Clifford lift has the same geometric reflection but different square. -/
theorem minus_twisted_adjoint (v : Tangent) :
    -(minusUnit.val * vectorMinus v * minusUnit.inv)=vectorMinus (reflected v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusUnit,reflectionMinus,reflectionPlus,vectorMinus,vectorPlus,reflected,
      Matrix.mul_apply,Fin.sum_univ_two,smul_eq_mul] <;> ring_nf <;> simp [Complex.I_sq]

/-- This is precisely the existing deck derivative, not an unrelated reflection. -/
theorem reflected_eq_deck_linear (v : Tangent) :
    reflected v=deckB_diff.mulVec v := by
  ext i
  fin_cases i <;> simp [reflected,deckB_diff,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

def signUnit (s : Bool) : Matˣ := if s then -1 else 1

theorem signUnit_square (s : Bool) : signUnit s * signUnit s=1 := by cases s <;> simp [signUnit]

theorem signUnit_commute (s : Bool) (U : Matˣ) : Commute (signUnit s) U := by
  cases s <;> simp [signUnit,Commute,SemiconjBy]

def plusMonodromy (s t : Bool) : KleinDeckGroup →* Matˣ :=
  flatRepresentation (signUnit s) (signUnit t*plusUnit)
    (signUnit_square s) (signUnit_commute _ _)

def minusMonodromy (s t : Bool) : KleinDeckGroup →* Matˣ :=
  flatRepresentation (signUnit s) (signUnit t*minusUnit)
    (signUnit_square s) (signUnit_commute _ _)

theorem plus_double_glide (s t : Bool) :
    ((plusMonodromy s t (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b)).val)=1 := by
  rw [plusMonodromy,flatRepresentation_double_glide]
  cases t <;> simp [signUnit,plusUnit,reflectionPlus_square]

theorem minus_double_glide (s t : Bool) :
    ((minusMonodromy s t (KleinDeckGroup.mul KleinDeckGroup.b KleinDeckGroup.b)).val)=-1 := by
  rw [minusMonodromy,flatRepresentation_double_glide]
  cases t <;> simp [signUnit,minusUnit,reflectionMinus_square]

/-- A spatial boundary condition yields a translation sign, not pointwise invariance. -/
theorem equivariant_double_glide (R : Mat) (ψ : PlanePoint → Spinor)
    (hψ : ∀ p, ψ (deckB p)=R.mulVec (ψ p)) (p : PlanePoint) :
    ψ (p.1,p.2+2)=(R*R).mulVec (ψ p) := by
  rw [← deckB_sq p,hψ,hψ,Matrix.mulVec_mulVec]

theorem minus_equivariant_antiperiodic (ψ : PlanePoint → Spinor)
    (hψ : ∀ p, ψ (deckB p)=reflectionMinus.mulVec (ψ p)) (p : PlanePoint) :
    ψ (p.1,p.2+2)=-ψ p := by
  rw [equivariant_double_glide _ ψ hψ,reflectionMinus_square]
  ext i
  fin_cases i <;> simp

/-- A negative lift cannot define an ordinary involution on a nonzero periodic field. -/
theorem negative_lift_periodic_obstruction (ψ : PlanePoint → Spinor)
    (hψ : ∀ p, ψ (deckB p)=reflectionMinus.mulVec (ψ p))
    (hper : ∀ p, ψ (p.1,p.2+2)=ψ p) : ψ=0 := by
  funext p
  have h := minus_equivariant_antiperiodic ψ hψ p
  rw [hper] at h
  ext i
  have hi := congrFun h i
  have hi' : ψ p i = -(ψ p i) := by simpa using hi
  have : (2:ℂ)*(ψ p i)=0 := by linear_combination hi'
  exact (mul_eq_zero.mp this).resolve_left (by norm_num)

section PeirceDeWittPinBridge

open InfoGeometry.Algebra.DeWittPeirceSuperalgebra
open InfoGeometry.Algebra.DeWittPeirceChiralBridge

/-- Left Peirce sheet projector on the `2 × 2` spinor carrier `Mat`. -/
def peircePL : Mat := !![(1 : ℂ), 0; 0, 0]

/-- Right Peirce sheet projector on the `2 × 2` spinor carrier `Mat`. -/
def peircePR : Mat := !![(0 : ℂ), 0; 0, 1]

/-- Canonical two-sheeted `ChiralPeirceSystem` structure on `Mat`. -/
instance matChiralPeirceSystem : ChiralPeirceSystem Mat where
  PL := peircePL
  PR := peircePR
  h_PL_sq := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [peircePL, Matrix.mul_apply, Fin.sum_univ_two]
  h_PR_sq := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [peircePR, Matrix.mul_apply, Fin.sum_univ_two]
  h_sum := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [peircePL, peircePR]
  h_PL_PR := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [peircePL, peircePR, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `Pin⁺` reflection unit conjugates `peircePL` to `peircePR`. -/
theorem reflectionPlus_swaps_peirce_sheets :
    plusUnit.val * peircePL * plusUnit.inv = peircePR := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [plusUnit, reflectionPlus, peircePL, peircePR, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `Pin⁻` reflection unit induces the exact same Peirce sheet swap on `peircePL ↔ peircePR`. -/
theorem reflectionMinus_swaps_peirce_sheets :
    minusUnit.val * peircePL * minusUnit.inv = peircePR := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [minusUnit, reflectionMinus, reflectionPlus, peircePL, peircePR,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

/-- Both `Pin⁺` and `Pin⁻` double-glide lifts induce the identical adjoint sheet swap on `Mat`. -/
theorem plus_and_minus_agree_on_peirce_adjoint (X : Mat) :
    sheetSwapAd plusUnit.val plusUnit.inv X = sheetSwapAd minusUnit.val minusUnit.inv X := by
  change reflectionPlus * X * reflectionPlus =
    (Complex.I • reflectionPlus) * X * (-(Complex.I • reflectionPlus))
  simp only [mul_neg, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
    neg_smul, neg_neg, one_smul]

/-- Explicit non-commutativity witness between the Klein reflection and Peirce chiral grading `G`. -/
theorem reflectionPlus_noncomm_chiralGrading :
    reflectionPlus * (G (A := Mat)) ≠ (G (A := Mat)) * reflectionPlus := by
  intro h
  have hG : (G (A := Mat)) = peircePL - peircePR := rfl
  rw [hG] at h
  have h01 := congrArg (fun M : Mat => M 0 1) h
  simp [reflectionPlus, peircePL, peircePR, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- Explicit matrix non-commutativity witness on `Mat`: the `Pin⁺` reflection unit does not
commute with the left Peirce sheet projector `peircePL`. -/
theorem reflectionPlus_peircePL_noncommutative :
    reflectionPlus * peircePL ≠ peircePL * reflectionPlus := by
  intro hComm
  apply reflectionPlus_noncomm_chiralGrading
  have hG : (G (A := Mat)) = peircePL - peircePR := rfl
  have hSum : peircePL + peircePR = 1 := matChiralPeirceSystem.h_sum
  have hPR : peircePR = 1 - peircePL := by
    calc peircePR = (peircePL + peircePR) - peircePL := by abel
      _ = 1 - peircePL := by rw [hSum]
  rw [hG, hPR]
  calc reflectionPlus * (peircePL - (1 - peircePL))
      = reflectionPlus * peircePL - (reflectionPlus * 1 - reflectionPlus * peircePL) := by
          rw [mul_sub, mul_sub, mul_one]
    _ = peircePL * reflectionPlus - (1 * reflectionPlus - peircePL * reflectionPlus) := by
          rw [hComm, mul_one, one_mul]
    _ = (peircePL - (1 - peircePL)) * reflectionPlus := by
          rw [sub_mul, sub_mul, one_mul]

/-- Under the `Pin⁻` Klein glide, matrix-valued spinor bimodules `U, V` are double-glide
antiperiodic (`-1`), while the coupled bilinear `U * V` swaps Peirce sheets and stays periodic (`+1`). -/
theorem klein_pin_minus_soul_antiperiodic_body_periodic (U V : PlanePoint → Mat)
    (hU : ∀ p, U (deckB p) = reflectionMinus * U p)
    (hV : ∀ p, V (deckB p) = V p * minusUnit.inv) (p : PlanePoint) :
    U (p.1, p.2 + 2) = -U p ∧
    V (p.1, p.2 + 2) = -V p ∧
    (U (deckB p) * V (deckB p) = sheetSwapAd minusUnit.val minusUnit.inv (U p * V p)) ∧
    (U (p.1, p.2 + 2) * V (p.1, p.2 + 2) = U p * V p) := by
  have h := pin_minus_left_antiperiodic_and_bilinear_body_periodic
    deckB minusUnit.val minusUnit.inv
    minusUnit.inv_val reflectionMinus_square U V hU hV p
  simpa [deckB_sq p] using h

/-- A `Pin⁻` Klein-equivariant matrix field cannot be periodic along the longitudinal glide unless zero. -/
theorem klein_pin_minus_periodic_matrix_obstruction (U : PlanePoint → Mat)
    (hU : ∀ p, U (deckB p) = reflectionMinus * U p)
    (hper : ∀ p, U (p.1, p.2 + 2) = U p) :
    U = 0 := by
  have hper' : ∀ p, U (deckB (deckB p)) = U p := fun p => by
    rw [deckB_sq p, hper p]
  refine pin_minus_periodic_obstruction deckB reflectionMinus reflectionMinus_square ?_ U hU hper'
  intro M hM
  ext i j
  have hij := congrFun (congrFun hM i) j
  have hij' : M i j + M i j = 0 := by simpa using hij
  have h2 : (2 : ℂ) * M i j = 0 := by
    calc
      (2 : ℂ) * M i j = M i j + M i j := two_mul _
      _ = 0 := hij'
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

end PeirceDeWittPinBridge

end InfoGeometry.Topology.KleinCliffordPinLift
