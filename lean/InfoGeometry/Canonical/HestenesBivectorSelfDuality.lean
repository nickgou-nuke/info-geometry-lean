import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import InfoGeometry.Canonical.CliffordParityBridge
import InfoGeometry.Canonical.HestenesBivectorCarrier

namespace InfoGeometry.Canonical.HestenesBivectorSelfDuality

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement
open InfoGeometry.Canonical.HestenesBivectorCarrier
open TensorProduct

variable {M : Type*} [AddCommGroup M] [Module ℝ M]
variable (Q : QuadraticForm ℝ M) [HasVolumeElement ℝ M Q] [HasSpacetimeBasis Q]

abbrev ComplexBivector (Q : QuadraticForm ℝ M) [HasVolumeElement ℝ M Q] [HasSpacetimeBasis Q] := TensorProduct ℝ ℂ (Bivector13 Q)

noncomputable def complexHodgeStar : ComplexBivector Q →ₗ[ℂ] ComplexBivector Q :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id) (hodgeBivector Q)

theorem complexHodgeStar_sq (B : ComplexBivector Q) :
    complexHodgeStar Q (complexHodgeStar Q B) = -B := by
  refine TensorProduct.induction_on B ?_ ?_ ?_
  · simp
  · intro c x
    simp only [complexHodgeStar, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq]
    have h1 : hodgeBivector Q (hodgeBivector Q x) = -x := by
      ext
      simp [hodgeBivector, hodge_sq_bivector]
    rw [h1, TensorProduct.tmul_neg]
  · intro x y hx hy
    simp only [map_add, hx, hy, neg_add]

noncomputable def selfDualProj : ComplexBivector Q →ₗ[ℂ] ComplexBivector Q :=
  (2⁻¹ : ℂ) • (LinearMap.id - Complex.I • complexHodgeStar Q)

noncomputable def antiSelfDualProj : ComplexBivector Q →ₗ[ℂ] ComplexBivector Q :=
  (2⁻¹ : ℂ) • (LinearMap.id + Complex.I • complexHodgeStar Q)

@[simp]
lemma selfDualProj_apply (B : ComplexBivector Q) :
    selfDualProj Q B = (2⁻¹ : ℂ) • B - (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B := by
  dsimp [selfDualProj]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq, smul_sub, smul_smul]

@[simp]
lemma antiSelfDualProj_apply (B : ComplexBivector Q) :
    antiSelfDualProj Q B = (2⁻¹ : ℂ) • B + (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B := by
  dsimp [antiSelfDualProj]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_coe, id_eq, smul_add, smul_smul]

@[simp]
lemma star_selfDualProj (B : ComplexBivector Q) :
    complexHodgeStar Q (selfDualProj Q B) = (2⁻¹ : ℂ) • complexHodgeStar Q B + (2⁻¹ * Complex.I : ℂ) • B := by
  rw [selfDualProj_apply Q B, map_sub, map_smul, map_smul, complexHodgeStar_sq Q B]
  simp only [smul_neg, sub_neg_eq_add]

@[simp]
lemma star_antiSelfDualProj (B : ComplexBivector Q) :
    complexHodgeStar Q (antiSelfDualProj Q B) = (2⁻¹ : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I : ℂ) • B := by
  rw [antiSelfDualProj_apply Q B, map_add, map_smul, map_smul, complexHodgeStar_sq Q B]
  simp only [smul_neg, sub_eq_add_neg, add_comm]

lemma rearrange_terms_proj {G : Type*} [AddCommGroup G] (A B C D : G) :
    A - B - (C + D) = (A - D) - (B + C) := by abel

theorem selfDualProj_idempotent (B : ComplexBivector Q) :
    selfDualProj Q (selfDualProj Q B) = selfDualProj Q B := by
  have i_sq : Complex.I * Complex.I = -1 := by norm_num
  have h_B : (2⁻¹ * 2⁻¹ : ℂ) • B - (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B = (2⁻¹ : ℂ) • B := by
    rw [← sub_smul]
    congr 1
    calc 2⁻¹ * 2⁻¹ - 2⁻¹ * Complex.I * (2⁻¹ * Complex.I) = 2⁻¹ * 2⁻¹ - (2⁻¹ * 2⁻¹) * (Complex.I * Complex.I) := by ring
      _ = 2⁻¹ * 2⁻¹ - (2⁻¹ * 2⁻¹) * (-1) := by rw [i_sq]
      _ = 2⁻¹ := by ring
  have h_star : (2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B + (2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B = (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B := by
    rw [← add_smul]
    congr 1
    ring
  calc selfDualProj Q (selfDualProj Q B)
    _ = (2⁻¹ : ℂ) • (selfDualProj Q B) - (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q (selfDualProj Q B) := by rw [selfDualProj_apply Q (selfDualProj Q B)]
    _ = (2⁻¹ : ℂ) • (selfDualProj Q B) - (2⁻¹ * Complex.I : ℂ) • ((2⁻¹ : ℂ) • complexHodgeStar Q B + (2⁻¹ * Complex.I : ℂ) • B) := by rw [star_selfDualProj Q B]
    _ = (2⁻¹ : ℂ) • ((2⁻¹ : ℂ) • B - (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B) - (2⁻¹ * Complex.I : ℂ) • ((2⁻¹ : ℂ) • complexHodgeStar Q B + (2⁻¹ * Complex.I : ℂ) • B) := by rw [selfDualProj_apply Q B]
    _ = (2⁻¹ * 2⁻¹ : ℂ) • B - (2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B - ((2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B + (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B) := by simp only [smul_sub, smul_add, smul_smul]
    _ = ((2⁻¹ * 2⁻¹ : ℂ) • B - (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B) - ((2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B + (2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B) := by rw [rearrange_terms_proj]
    _ = (2⁻¹ : ℂ) • B - (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B := by rw [h_B, h_star]
    _ = selfDualProj Q B := by rw [← selfDualProj_apply Q B]

lemma rearrange_terms_proj_anti {G : Type*} [AddCommGroup G] (A B C D : G) :
    A + B + (C - D) = (A - D) + (B + C) := by abel

theorem antiSelfDualProj_idempotent (B : ComplexBivector Q) :
    antiSelfDualProj Q (antiSelfDualProj Q B) = antiSelfDualProj Q B := by
  have i_sq : Complex.I * Complex.I = -1 := by norm_num
  have h_B : (2⁻¹ * 2⁻¹ : ℂ) • B - (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B = (2⁻¹ : ℂ) • B := by
    rw [← sub_smul]
    congr 1
    calc 2⁻¹ * 2⁻¹ - 2⁻¹ * Complex.I * (2⁻¹ * Complex.I) = 2⁻¹ * 2⁻¹ - (2⁻¹ * 2⁻¹) * (Complex.I * Complex.I) := by ring
      _ = 2⁻¹ * 2⁻¹ - (2⁻¹ * 2⁻¹) * (-1) := by rw [i_sq]
      _ = 2⁻¹ := by ring
  have h_star : (2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B + (2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B = (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B := by
    rw [← add_smul]
    congr 1
    ring
  calc antiSelfDualProj Q (antiSelfDualProj Q B)
    _ = (2⁻¹ : ℂ) • (antiSelfDualProj Q B) + (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q (antiSelfDualProj Q B) := by rw [antiSelfDualProj_apply Q (antiSelfDualProj Q B)]
    _ = (2⁻¹ : ℂ) • (antiSelfDualProj Q B) + (2⁻¹ * Complex.I : ℂ) • ((2⁻¹ : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I : ℂ) • B) := by rw [star_antiSelfDualProj Q B]
    _ = (2⁻¹ : ℂ) • ((2⁻¹ : ℂ) • B + (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B) + (2⁻¹ * Complex.I : ℂ) • ((2⁻¹ : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I : ℂ) • B) := by rw [antiSelfDualProj_apply Q B]
    _ = (2⁻¹ * 2⁻¹ : ℂ) • B + (2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B + ((2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B) := by simp only [smul_add, smul_sub, smul_smul]
    _ = ((2⁻¹ * 2⁻¹ : ℂ) • B - (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B) + ((2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B + (2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B) := by rw [rearrange_terms_proj_anti]
    _ = (2⁻¹ : ℂ) • B + (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B := by rw [h_B, h_star]
    _ = antiSelfDualProj Q B := by rw [← antiSelfDualProj_apply Q B]

lemma rearrange_terms_zero {G : Type*} [AddCommGroup G] (A B C D : G) :
    A + B - (C - D) = (A + D) + (B - C) := by abel

theorem projectors_comp_zero (B : ComplexBivector Q) :
    selfDualProj Q (antiSelfDualProj Q B) = 0 := by
  have i_sq : Complex.I * Complex.I = -1 := by norm_num
  have h_B : (2⁻¹ * 2⁻¹ : ℂ) • B + (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B = 0 := by
    rw [← add_smul]
    have H : 2⁻¹ * 2⁻¹ + 2⁻¹ * Complex.I * (2⁻¹ * Complex.I) = 0 := by
      calc 2⁻¹ * 2⁻¹ + 2⁻¹ * Complex.I * (2⁻¹ * Complex.I) = 2⁻¹ * 2⁻¹ + (2⁻¹ * 2⁻¹) * (Complex.I * Complex.I) := by ring
        _ = 2⁻¹ * 2⁻¹ + (2⁻¹ * 2⁻¹) * (-1) := by rw [i_sq]
        _ = 0 := by ring
    rw [H, zero_smul]
  have h_star : (2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B = 0 := by
    rw [← sub_smul]
    have H : 2⁻¹ * (2⁻¹ * Complex.I) - 2⁻¹ * Complex.I * 2⁻¹ = 0 := by ring
    rw [H, zero_smul]
  calc selfDualProj Q (antiSelfDualProj Q B)
    _ = (2⁻¹ : ℂ) • (antiSelfDualProj Q B) - (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q (antiSelfDualProj Q B) := by rw [selfDualProj_apply Q (antiSelfDualProj Q B)]
    _ = (2⁻¹ : ℂ) • (antiSelfDualProj Q B) - (2⁻¹ * Complex.I : ℂ) • ((2⁻¹ : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I : ℂ) • B) := by rw [star_antiSelfDualProj Q B]
    _ = (2⁻¹ : ℂ) • ((2⁻¹ : ℂ) • B + (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B) - (2⁻¹ * Complex.I : ℂ) • ((2⁻¹ : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I : ℂ) • B) := by rw [antiSelfDualProj_apply Q B]
    _ = (2⁻¹ * 2⁻¹ : ℂ) • B + (2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B - ((2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B) := by simp only [smul_add, smul_sub, smul_smul]
    _ = ((2⁻¹ * 2⁻¹ : ℂ) • B + (2⁻¹ * Complex.I * (2⁻¹ * Complex.I) : ℂ) • B) + ((2⁻¹ * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B - (2⁻¹ * Complex.I * 2⁻¹ : ℂ) • complexHodgeStar Q B) := by rw [rearrange_terms_zero]
    _ = 0 + 0 := by rw [h_B, h_star]
    _ = 0 := by rw [add_zero]

theorem projectors_add_eq_id (B : ComplexBivector Q) :
    selfDualProj Q B + antiSelfDualProj Q B = B := by
  rw [selfDualProj_apply Q B, antiSelfDualProj_apply Q B]
  have H : (2⁻¹ : ℂ) • B - (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B + ((2⁻¹ : ℂ) • B + (2⁻¹ * Complex.I : ℂ) • complexHodgeStar Q B) = (2⁻¹ : ℂ) • B + (2⁻¹ : ℂ) • B := by abel
  rw [H, ← add_smul]
  have H2 : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by ring
  rw [H2, one_smul]

theorem star_on_selfDual (B : ComplexBivector Q) :
    complexHodgeStar Q (selfDualProj Q B) = Complex.I • selfDualProj Q B := by
  rw [star_selfDualProj Q B, selfDualProj_apply Q B, smul_sub, smul_smul, smul_smul]
  have i_sq : Complex.I * Complex.I = -1 := by norm_num
  have h_B : (2⁻¹ * Complex.I : ℂ) • B = (Complex.I * 2⁻¹ : ℂ) • B := by congr 1; ring
  have h_star : (2⁻¹ : ℂ) • complexHodgeStar Q B = - (Complex.I * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B := by
    congr 1
    calc (2⁻¹ : ℂ) = 2⁻¹ * 1 := by ring
      _ = 2⁻¹ * -(-1) := by ring
      _ = 2⁻¹ * -(Complex.I * Complex.I) := by rw [i_sq]
      _ = -(Complex.I * (2⁻¹ * Complex.I)) := by ring
  rw [h_B, h_star]
  simp only [sub_eq_add_neg]; rw [← neg_smul, neg_mul_eq_neg_mul]
  rw [add_comm]

theorem star_on_antiSelfDual (B : ComplexBivector Q) :
    complexHodgeStar Q (antiSelfDualProj Q B) = -Complex.I • antiSelfDualProj Q B := by
  rw [star_antiSelfDualProj Q B, antiSelfDualProj_apply Q B, smul_add, smul_smul, smul_smul]
  have i_sq : Complex.I * Complex.I = -1 := by norm_num
  have h_B : (2⁻¹ * Complex.I : ℂ) • B = (Complex.I * 2⁻¹ : ℂ) • B := by congr 1; ring
  have h_star : (2⁻¹ : ℂ) • complexHodgeStar Q B = (-Complex.I * (2⁻¹ * Complex.I) : ℂ) • complexHodgeStar Q B := by
    congr 1
    calc (2⁻¹ : ℂ) = 2⁻¹ * 1 := by ring
      _ = 2⁻¹ * -(-1) := by ring
      _ = 2⁻¹ * -(Complex.I * Complex.I) := by rw [i_sq]
      _ = -Complex.I * (2⁻¹ * Complex.I) := by ring
  rw [h_B, h_star]
  simp only [sub_eq_add_neg]; rw [← neg_smul, neg_mul_eq_neg_mul]
  rw [add_comm]

end InfoGeometry.Canonical.HestenesBivectorSelfDuality
