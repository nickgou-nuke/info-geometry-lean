/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveNilpotentFlows

/-! # Algebraic rotor action on a reflexive square-zero pair

No differential, topological, or De Bruijn syntax structure is asserted.
The circle equation is needed for invertibility, not for the expansion formula.
-/
namespace InfoGeometry.Canonical.PeirceRotorAction
open ReflexiveNilpotentFlows
variable {A : Type*} [Ring A]

theorem bracket_plus {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    (d-B)*(d*B)-(d*B)*(d-B)= -(d+B) := by
  calc
    _ = (d*d)*B-B*d*B-d*B*d+d*(B*B) := by noncomm_ring
    _ = _ := by rw [hd,hB,hr,hs]; simp; abel

theorem bracket_minus {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    (d-B)*(B*d)-(B*d)*(d-B)=d+B := by
  calc
    _ = d*B*d-(B*B)*d-B*(d*d)+B*d*B := by noncomm_ring
    _ = _ := by rw [hd,hB,hr,hs]; simp

theorem bracket_polarization {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    (d-B)*(d*B-B*d)-(d*B-B*d)*(d-B)= -(2 • (d+B)) := by
  have hp := bracket_plus hd hB hr hs
  have hm := bracket_minus hd hB hr hs
  calc
    _ = ((d-B)*(d*B)-(d*B)*(d-B))-((d-B)*(B*d)-(B*d)*(d-B)) := by noncomm_ring
    _ = _ := by rw [hp,hm,two_nsmul]; abel

theorem double_bracket {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    (d-B)*((d-B)*(d*B-B*d)-(d*B-B*d)*(d-B)) -
      ((d-B)*(d*B-B*d)-(d*B-B*d)*(d-B))*(d-B) = -(4 • (d*B-B*d)) := by
  rw [bracket_polarization hd hB hr hs]
  simp only [two_nsmul,show (4 : ℕ)=2+2 by decide,add_nsmul]
  noncomm_ring

theorem stationary_iff {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) :
    (d-B)*(d*B)-(d*B)*(d-B)=0 ↔ d=0 ∧ B=0 := by
  rw [bracket_plus hd hB hr hs,neg_eq_zero]
  constructor
  · intro h
    have hz := congrArg (fun x : A => (d*B)*x) h
    have hb : (d*B)*B=0 := by rw [mul_assoc,hB,mul_zero]
    simp only [mul_add,hr,hb,add_zero,mul_zero] at hz
    exact ⟨hz, by simpa [hz] using h⟩
  · rintro ⟨rfl,rfl⟩; simp

section Scalar
variable {R : Type*} [CommRing R] [Algebra R A]

/-- Conjugation expression, defined even before imposing the circle equation. -/
def movingPlus (c s : R) (d B : A) : A := rotor c s d B*(d*B)*rotor c (-s) d B

theorem movingPlus_expansion {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) (c s : R) :
    movingPlus c s d B=(c*c) • (d*B)+(s*s) • (B*d)-(c*s) • (d+B) := by
  obtain ⟨hpp,_,hpq,hqp,hpH,_,hHp,_,_⟩ := support_table hd hB hr hs
  obtain ⟨_,_,_,hBH⟩ := complement_annihilates hd hB hr hs
  have hdp : d*(d*B)=0 := by rw [← mul_assoc,hd,zero_mul]
  have hBp : B*(d*B)=B := by rw [← mul_assoc,hs]
  have hpB : (d*B)*B=0 := by rw [mul_assoc,hB,mul_zero]
  have hBq : B*(B*d)=0 := by rw [← mul_assoc,hB,zero_mul]
  have hl : rotor c s d B*(d*B)=c • (d*B)-s • B := by
    simp only [rotor,support,add_mul,smul_mul_assoc,sub_mul,hHp,hpp,hqp,
      hdp,hBp,add_zero,zero_add,zero_sub,smul_neg]; abel
  have hrp : (d*B)*rotor c (-s) d B=c • (d*B)-s • d := by
    simp only [rotor,support,mul_add,mul_smul_comm,mul_sub,hpH,hpp,hpq,
      hr,hpB,add_zero,zero_add,sub_zero,neg_smul,mul_neg]; abel
  have hrB : B*rotor c (-s) d B=c • B-s • (B*d) := by
    simp only [rotor,support,mul_add,mul_smul_comm,mul_sub,hBH,hBp,hBq,
      hB,add_zero,zero_add,sub_zero,neg_smul,mul_neg]; abel
  rw [movingPlus,hl,sub_mul,smul_mul_assoc,smul_mul_assoc,hrp,hrB]
  simp only [smul_sub,smul_smul,smul_add,mul_comm s c]
  abel

theorem movingPlus_quarter_turn {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) : movingPlus (0 : R) 1 d B=B*d := by
  rw [movingPlus_expansion hd hB hr hs]
  simp

theorem movingPlus_idempotent {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) (c s : R) (hc : c*c+s*s=1) :
    IsIdempotentElem (movingPlus c s d B) := by
  apply GrassmannianBundleCyclotomicOrientability.isIdempotentElem_homogeneousProj
  · exact (support_table hd hB hr hs).1
  · simpa only [neg_neg] using rotor_inverse hd hB hr hs c (-s) (by simpa using hc)
/-- The opposite directed projection under the same rotor. -/
def movingMinus (c s : R) (d B : A) : A :=
  rotor c s d B*(B*d)*rotor c (-s) d B

 theorem rotor_swap (c s : R) (d B : A) :
    rotor c s B d=rotor c (-s) d B := by
  simp only [rotor,complement,support,smul_sub,neg_smul,smul_add]
  abel

 theorem movingMinus_eq_swapped (c s : R) (d B : A) :
    movingMinus c s d B=movingPlus c (-s) B d := by
  simp only [movingPlus, movingMinus, rotor_swap c (-s) d B,
    rotor_swap c s d B, neg_neg]

 theorem movingMinus_expansion {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) (c s : R) :
    movingMinus c s d B=(s*s) • (d*B)+(c*c) • (B*d)+(c*s) • (d+B) := by
  rw [movingMinus_eq_swapped,movingPlus_expansion hB hd hs hr]
  simp only [mul_neg,neg_mul,neg_neg,neg_smul,smul_add]
  abel

 theorem movingMinus_idempotent {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) (c s : R) (hc : c*c+s*s=1) :
    IsIdempotentElem (movingMinus c s d B) := by
  rw [movingMinus_eq_swapped]
  exact movingPlus_idempotent hB hd hs hr c (-s) (by simpa using hc)

 theorem movingMinus_quarter_turn {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) : movingMinus (0 : R) 1 d B=d*B := by
  rw [movingMinus_expansion hd hB hr hs]
  simp

 theorem moving_sum {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) (c s : R) (hc : c*c+s*s=1) :
    movingPlus c s d B+movingMinus c s d B=support d B := by
  rw [movingPlus_expansion hd hB hr hs,movingMinus_expansion hd hB hr hs]
  calc
    _ = (c*c+s*s) • support d B := by simp only [support,add_smul,smul_add]; abel
    _ = _ := by rw [hc,one_smul]

private theorem conjugate_zero_product (r t p q : A) (hi : t*r=1) (hpq : p*q=0) :
    (r*p*t)*(r*q*t)=0 := by
  calc
    _ = r*(p*(t*r)*q)*t := by noncomm_ring
    _ = 0 := by rw [hi,mul_one,hpq,mul_zero,zero_mul]

 theorem moving_orthogonal {d B : A} (hd : d*d=0) (hB : B*B=0)
    (hr : d*B*d=d) (hs : B*d*B=B) (c s : R) (hc : c*c+s*s=1) :
    movingPlus c s d B*movingMinus c s d B=0 ∧
    movingMinus c s d B*movingPlus c s d B=0 := by
  have hi : rotor c (-s) d B*rotor c s d B=1 := by
    simpa only [neg_neg] using rotor_inverse hd hB hr hs c (-s) (by simpa using hc)
  obtain ⟨_,_,hpq,hqp,_⟩ := support_table hd hB hr hs
  exact ⟨conjugate_zero_product _ _ _ _ hi hpq,conjugate_zero_product _ _ _ _ hi hqp⟩
end Scalar
end InfoGeometry.Canonical.PeirceRotorAction
