/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
import InfoGeometry.Canonical.ReflexiveNilpotentFlows
import InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance

/-! # Complement-preserving hyperbolic pole motion

Central algebraic coefficients only. The active support need not be one.
No metric, positivity, analytic exponential, or KMS state is asserted.
-/
namespace InfoGeometry.Canonical.ComplementHyperbolicOrbit
open DeBruijnRotorAlternationCycle
open ReflexiveNilpotentFlows
open GrassmannianBundleCyclotomicOrientability
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Hyperbolic polynomial fixing the complement of the native active support. -/
def hyperbolicRotor (u v : R) (d B : A) : A :=
  complement d B + u • support d B + v • (d + B)

/-- The plus pole transported by the forward and reverse polynomials. -/
def hyperbolicPlus (u v : R) (d B : A) : A :=
  hyperbolicRotor u v d B * (d*B) * hyperbolicRotor u (-v) d B

/-- The minus pole transported by the same polynomials. -/
def hyperbolicMinus (u v : R) (d B : A) : A :=
  hyperbolicRotor u v d B * (B*d) * hyperbolicRotor u (-v) d B

variable {d B : A} (h : IsDualSeedPair d B)
include h

/-- Multiplication keeps the complementary support fixed. -/
theorem hyperbolicRotor_mul (u v a b : R) :
    hyperbolicRotor u v d B * hyperbolicRotor a b d B =
      hyperbolicRotor (u*a+v*b) (u*b+v*a) d B := by
  let S := support d B
  let C := complement d B
  let Q := d+B
  have hSS : S*S=S := support_sq h.d_sq h.B_sq h.dBd h.BdB
  have hCC : C*C=C := (support_table h.d_sq h.B_sq h.dBd h.BdB).2.2.2.2.2.2.2.2
  have hCS : C*S=0 := by dsimp [C, complement]; rw [sub_mul, one_mul, hSS, sub_self]
  have hSC : S*C=0 := by dsimp [C, complement]; rw [mul_sub, mul_one, hSS, sub_self]
  obtain ⟨hdL, hdR, hBL, hBR⟩ := active_support_absorbs h.d_sq h.B_sq h.dBd h.BdB
  have hSQ : S*Q=Q := by dsimp [S, Q, support]; rw [mul_add, hdL, hBL]
  have hQS : Q*S=Q := by dsimp [S, Q, support]; rw [add_mul, hdR, hBR]
  have hCQ : C*Q=0 := by dsimp [C, complement]; rw [sub_mul, one_mul, hSQ, sub_self]
  have hQC : Q*C=0 := by dsimp [C, complement]; rw [mul_sub, mul_one, hQS, sub_self]
  have hQQ : Q*Q=S := transitionVelocity_sq h
  change (C+u • S+v • Q)*(C+a • S+b • Q)=C+(u*a+v*b) • S+(u*b+v*a) • Q
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hSS, hCC,
    hCS, hSC, hSQ, hQS, hCQ, hQC, hQQ, smul_zero, zero_add, add_zero,
    smul_smul, add_smul]
  rw [mul_comm a u, mul_comm b v, mul_comm b u, mul_comm a v]
  abel

/-- The reverse polynomial is a right inverse on the hyperbola. -/
theorem hyperbolicRotor_inverse (u v : R) (huv : u*u-v*v=1) :
    hyperbolicRotor u v d B * hyperbolicRotor u (-v) d B = 1 := by
  rw [hyperbolicRotor_mul h]
  have ha : u*u+v*(-v)=1 := by simpa only [mul_neg, ← sub_eq_add_neg] using huv
  have hb : u*(-v)+v*u=0 := by ring
  rw [ha, hb]
  simp only [hyperbolicRotor, one_smul, zero_smul, add_zero, complement]
  abel

/-- The reverse polynomial is also a left inverse. -/
theorem hyperbolicRotor_reverse_inverse (u v : R) (huv : u*u-v*v=1) :
    hyperbolicRotor u (-v) d B * hyperbolicRotor u v d B = 1 := by
  have hn : u*u-(-v)*(-v)=1 := by simpa only [neg_mul_neg] using huv
  simpa only [neg_neg] using hyperbolicRotor_inverse h u (-v) hn

/-- The plus column of the hyperbolic polynomial. -/
theorem hyperbolicRotor_mul_plus (u v : R) :
    hyperbolicRotor u v d B*(d*B)=u • (d*B)+v • B := by
  obtain ⟨hpp, _, _, hmp, _, _, hcp, _, _⟩ := support_table h.d_sq h.B_sq h.dBd h.BdB
  have hsp : support d B*(d*B)=d*B := by simp only [support, add_mul, hpp, hmp, add_zero]
  have hqp : (d+B)*(d*B)=B := velocity_mul_polePlus h
  simp only [hyperbolicRotor, add_mul, smul_mul_assoc, hcp, hsp, hqp, zero_add]

/-- The plus row of the hyperbolic polynomial. -/
theorem plus_mul_hyperbolicRotor (u v : R) :
    (d*B)*hyperbolicRotor u v d B=u • (d*B)+v • d := by
  obtain ⟨hpp, _, hpm, _, hpc, _, _, _, _⟩ := support_table h.d_sq h.B_sq h.dBd h.BdB
  have hps : (d*B)*support d B=d*B := by simp only [support, mul_add, hpp, hpm, add_zero]
  have hpq : (d*B)*(d+B)=d := polePlus_mul_velocity h
  simp only [hyperbolicRotor, mul_add, mul_smul_comm, hpc, hps, hpq, zero_add]

/-- The creator row uses the same native support absorption. -/
theorem creator_mul_hyperbolicRotor (u v : R) :
    B*hyperbolicRotor u v d B=u • B+v • (B*d) := by
  have hbc := (complement_annihilates h.d_sq h.B_sq h.dBd h.BdB).2.2.2
  have hbs : B*support d B=B := (active_support_absorbs h.d_sq h.B_sq h.dBd h.BdB).2.2.2
  have hbq : B*(d+B)=B*d := by rw [mul_add, h.B_sq, add_zero]
  simp only [hyperbolicRotor, mul_add, mul_smul_comm, hbc, hbs, hbq, zero_add]

/-- The exact plus-pole expansion, without a hyperbola hypothesis. -/
theorem hyperbolicPlus_expansion (u v : R) :
    hyperbolicPlus u v d B =
      (u*u) • (d*B)-(v*v) • (B*d)-(u*v) • (d-B) := by
  unfold hyperbolicPlus
  rw [hyperbolicRotor_mul_plus h, add_mul, smul_mul_assoc, smul_mul_assoc,
    plus_mul_hyperbolicRotor h, creator_mul_hyperbolicRotor h]
  simp only [smul_add, smul_smul, mul_neg, neg_smul, smul_sub, mul_comm v u]
  abel

/-- The reverse pole has the opposite cross term. -/
theorem hyperbolicMinus_expansion (u v : R) :
    hyperbolicMinus u v d B =
      (u*u) • (B*d)-(v*v) • (d*B)+(u*v) • (d-B) := by
  have hs : IsDualSeedPair B d := ⟨h.B_sq, h.d_sq, h.BdB, h.dBd⟩
  have he : ∀ a b : R, hyperbolicRotor a b B d = hyperbolicRotor a b d B := by
    intro a b
    simp only [hyperbolicRotor, complement, support, add_comm]
  have hx := hyperbolicPlus_expansion hs u v
  simp only [hyperbolicPlus, he] at hx
  change hyperbolicRotor u v d B*(B*d)*hyperbolicRotor u (-v) d B = _
  rw [hx]
  simp only [smul_sub]
  abel

/-- Genuine idempotence follows by cancellation, not an assumed orbit law. -/
theorem hyperbolicPlus_idempotent (u v : R) (huv : u*u-v*v=1) :
    hyperbolicPlus u v d B*hyperbolicPlus u v d B=hyperbolicPlus u v d B := by
  have hp : (d*B)*(d*B)=d*B := (support_table h.d_sq h.B_sq h.dBd h.BdB).1
  unfold hyperbolicPlus
  calc
    _ = hyperbolicRotor u v d B*((d*B)*(hyperbolicRotor u (-v) d B*
        hyperbolicRotor u v d B)*(d*B))*hyperbolicRotor u (-v) d B := by noncomm_ring
    _ = _ := by rw [hyperbolicRotor_reverse_inverse h u v huv, mul_one, hp]

/-- The transported opposite pole is idempotent as well. -/
theorem hyperbolicMinus_idempotent (u v : R) (huv : u*u-v*v=1) :
    hyperbolicMinus u v d B*hyperbolicMinus u v d B=hyperbolicMinus u v d B := by
  have hp : (B*d)*(B*d)=B*d := (support_table h.d_sq h.B_sq h.dBd h.BdB).2.1
  unfold hyperbolicMinus
  calc
    _ = hyperbolicRotor u v d B*((B*d)*(hyperbolicRotor u (-v) d B*
        hyperbolicRotor u v d B)*(B*d))*hyperbolicRotor u (-v) d B := by noncomm_ring
    _ = _ := by rw [hyperbolicRotor_reverse_inverse h u v huv, mul_one, hp]

/-- The plus pole annihilates the minus pole after transport. -/
theorem hyperbolicPlus_mul_minus (u v : R) (huv : u*u-v*v=1) :
    hyperbolicPlus u v d B*hyperbolicMinus u v d B=0 := by
  have hp : (d*B)*(B*d)=0 := (support_table h.d_sq h.B_sq h.dBd h.BdB).2.2.1
  unfold hyperbolicPlus hyperbolicMinus
  calc
    _ = hyperbolicRotor u v d B*((d*B)*(hyperbolicRotor u (-v) d B*
        hyperbolicRotor u v d B)*(B*d))*hyperbolicRotor u (-v) d B := by noncomm_ring
    _ = 0 := by rw [hyperbolicRotor_reverse_inverse h u v huv, mul_one, hp, mul_zero, zero_mul]

/-- Orthogonality also holds in the other order. -/
theorem hyperbolicMinus_mul_plus (u v : R) (huv : u*u-v*v=1) :
    hyperbolicMinus u v d B*hyperbolicPlus u v d B=0 := by
  have hp : (B*d)*(d*B)=0 := (support_table h.d_sq h.B_sq h.dBd h.BdB).2.2.2.1
  unfold hyperbolicPlus hyperbolicMinus
  calc
    _ = hyperbolicRotor u v d B*((B*d)*(hyperbolicRotor u (-v) d B*
        hyperbolicRotor u v d B)*(d*B))*hyperbolicRotor u (-v) d B := by noncomm_ring
    _ = 0 := by rw [hyperbolicRotor_reverse_inverse h u v huv, mul_one, hp, mul_zero, zero_mul]

/-- The two moving poles retain exactly their native carrier. -/
theorem hyperbolicPlus_add_minus (u v : R) (huv : u*u-v*v=1) :
    hyperbolicPlus u v d B+hyperbolicMinus u v d B=carrierSupport d B := by
  rw [hyperbolicPlus_expansion h, hyperbolicMinus_expansion h]
  have hu : u*u=1+v*v := (sub_eq_iff_eq_add).mp huv
  rw [hu]
  simp only [add_smul, one_smul, carrierSupport, polePlus, poleMinus]
  abel

/-- Left compression before the final sandwich. -/
theorem plus_mul_hyperbolicPlus (u v : R) :
    (d*B)*hyperbolicPlus u v d B=(u*u) • (d*B)-(u*v) • d := by
  have hp := (support_table h.d_sq h.B_sq h.dBd h.BdB).1
  have hz := (support_table h.d_sq h.B_sq h.dBd h.BdB).2.2.1
  have hpj : (d*B)*(d-B)=d := by rw [mul_sub, h.dBd, mul_assoc, h.B_sq, mul_zero, sub_zero]
  rw [hyperbolicPlus_expansion h]
  simp only [mul_sub, mul_smul_comm, hp, hz, hpj, smul_zero, sub_zero]

/-- Right compression before the final sandwich. -/
theorem hyperbolicPlus_mul_plus (u v : R) :
    hyperbolicPlus u v d B*(d*B)=(u*u) • (d*B)+(u*v) • B := by
  have hp := (support_table h.d_sq h.B_sq h.dBd h.BdB).1
  have hz := (support_table h.d_sq h.B_sq h.dBd h.BdB).2.2.2.1
  have hjp : (d-B)*(d*B)= -B := by
    rw [sub_mul, ← mul_assoc, h.d_sq, zero_mul, ← mul_assoc, h.BdB, zero_sub]
  rw [hyperbolicPlus_expansion h]
  simp only [sub_mul, smul_mul_assoc, hp, hz, hjp, smul_zero, sub_zero, smul_neg, sub_neg_eq_add]

/-- Compression is polynomial and needs no normalization. -/
theorem hyperbolicPlus_compression (u v : R) :
    (d*B)*hyperbolicPlus u v d B*(d*B)=(u*u) • (d*B) := by
  have hp := (support_table h.d_sq h.B_sq h.dBd h.BdB).1
  have hz : d*(d*B)=0 := by rw [← mul_assoc, h.d_sq, zero_mul]
  rw [plus_mul_hyperbolicPlus h]
  simp only [sub_mul, smul_mul_assoc, hp, hz, smul_zero, sub_zero]

/-- The hyperbolic displacement has negative algebraic square on its carrier. -/
theorem hyperbolicPlus_displacement_square (u v : R) (huv : u*u-v*v=1) :
    (hyperbolicPlus u v d B-d*B)*(hyperbolicPlus u v d B-d*B)=
      -((v*v) • carrierSupport d B) := by
  have hp := (support_table h.d_sq h.B_sq h.dBd h.BdB).1
  calc
    _ = hyperbolicPlus u v d B*hyperbolicPlus u v d B -
        hyperbolicPlus u v d B*(d*B) - (d*B)*hyperbolicPlus u v d B +
        (d*B)*(d*B) := by noncomm_ring
    _ = _ := by
      rw [hyperbolicPlus_idempotent h u v huv, hp, hyperbolicPlus_mul_plus h,
        plus_mul_hyperbolicPlus h, hyperbolicPlus_expansion h]
      have hu : u*u=1+v*v := (sub_eq_iff_eq_add).mp huv
      rw [hu]
      simp only [add_smul, one_smul, smul_sub, carrierSupport, polePlus, poleMinus, smul_add]
      abel

end InfoGeometry.Canonical.ComplementHyperbolicOrbit
