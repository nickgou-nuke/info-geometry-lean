/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedCartan
import InfoGeometry.Core.PeirceBilateralAction
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# A constructive retraction onto a dual-seed centralizer

For the existing reflexive square-zero pair `d,b`, put `p = db` and
`r = 1 - db - bd`. The linear map `a ↦ p*a*p + b*a*d + r*a*r` retracts the
entire ambient algebra onto the native joint centralizer. It retains an
arbitrary active corner and an independent harmonic corner.

The ambient algebra need not be commutative. No metric, star, finite dimension,
full-support assumption, or division by two is used. This is a bimodule
projection, and its failure of multiplicativity is proved explicitly.
-/

namespace InfoGeometry.Core.DualSeedPeirce

open InfoGeometry.Core.PeirceRotor InfoGeometry.Core.PeirceBilateralAction
open InfoGeometry.Singular.MoorePenrose InfoGeometry.Core.DiracSuperalgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Copy the positive corner to the negative corner and retain the residual corner. -/
def centralizerProjection (R : Type*) [CommRing R] [Algebra R A] (d b : A) : A →ₗ[R] A :=
  bilateral (polePlus d b) (polePlus d b) + bilateral b d +
    bilateral (zeroModeSupport d b) (zeroModeSupport d b)

@[simp] theorem centralizerProjection_apply (d b a : A) :
    centralizerProjection R d b a = polePlus d b * a * polePlus d b +
      b * a * d + zeroModeSupport d b * a * zeroModeSupport d b := rfl

/-- Polynomial naturality on the full ambient algebra; no seed equations are needed. -/
theorem centralizerProjection_map {B : Type*} [Ring B] [Algebra R B]
    (f : A →ₐ[R] B) (d b a : A) :
    f (centralizerProjection R d b a) =
      centralizerProjection R (f d) (f b) (f a) := by
  simp only [centralizerProjection_apply, polePlus, exactSupport, zeroModeSupport,
    harmonicSupport, coexactSupport, map_add, map_mul, map_sub, map_one]

/-- Reciprocal changes of seed normalization leave the actual projection unchanged. -/
theorem centralizerProjection_rescale (d b a : A) (l m : R) (hlm : l * m = 1) :
    centralizerProjection R (l • d) (m • b) a = centralizerProjection R d b a := by
  have hml : m * l = 1 := by simpa only [mul_comm] using hlm
  have hp : polePlus (l • d) (m • b) = polePlus d b := by
    change (l • d) * (m • b) = d * b
    rw [smul_mul_smul_left, hlm, one_smul]
  have hq : poleMinus (l • d) (m • b) = poleMinus d b := by
    change (m • b) * (l • d) = b * d
    rw [smul_mul_smul_left, hml, one_smul]
  have hr : zeroModeSupport (l • d) (m • b) = zeroModeSupport d b := by
    change 1 - polePlus (l • d) (m • b) - poleMinus (l • d) (m • b) = _
    rw [hp, hq]
    rfl
  rw [centralizerProjection_apply, centralizerProjection_apply, hp, hr]
  rw [smul_mul_assoc, smul_mul_smul_left, hml, one_smul]

/-- Common commutation implies commutation with the Cartan polynomial. -/
theorem commute_phasePolarization_of_commute {a d b : A}
    (hd : Commute a d) (hb : Commute a b) : Commute a (phasePolarization d b) :=
  (hd.mul_right hb).sub_right (hb.mul_right hd)

namespace IsDualSeedPair

variable {d b : A}

private theorem residual_seed (h : IsDualSeedPair d b) :
    zeroModeSupport d b * d = 0 ∧ d * zeroModeSupport d b = 0 := by
  simpa only [peirceBlock, zero_smul, one_smul, zero_add, add_zero] using
    (harmonic_block (R := ℤ) h 0 1 0 0)

private theorem residual_partner (h : IsDualSeedPair d b) :
    zeroModeSupport d b * b = 0 ∧ b * zeroModeSupport d b = 0 := by
  simpa only [peirceBlock, zero_smul, one_smul, zero_add, add_zero] using
    (harmonic_block (R := ℤ) h 0 0 1 0)

theorem centralizerProjection_commute_seed (h : IsDualSeedPair d b) (a : A) :
    Commute (centralizerProjection R d b a) d := by
  change centralizerProjection R d b a * d = d * centralizerProjection R d b a
  calc
    _ = polePlus d b * a * d := by
      simp only [centralizerProjection_apply, add_mul, mul_assoc,
        h.pd, h.d_sq, h.residual_seed.1, mul_zero, add_zero]
    _ = _ := by
      simp only [centralizerProjection_apply, mul_add, ← mul_assoc,
        h.dp, h.residual_seed.2, zero_mul, zero_add, add_zero]
      rfl

theorem centralizerProjection_commute_partner (h : IsDualSeedPair d b) (a : A) :
    Commute (centralizerProjection R d b a) b := by
  change centralizerProjection R d b a * b = b * centralizerProjection R d b a
  calc
    _ = b * a * polePlus d b := by
      simp only [centralizerProjection_apply, add_mul, mul_assoc,
        h.pb, h.residual_partner.1, mul_zero, zero_add, add_zero]
      rfl
    _ = _ := by
      simp only [centralizerProjection_apply, mul_add, ← mul_assoc,
        h.bp, h.b_sq, h.residual_partner.2, zero_mul, add_zero]

/-- The image lies in the whole common commutant, not just in the residual corner. -/
theorem centralizerProjection_mem (h : IsDualSeedPair d b) (a : A) :
    centralizerProjection R d b a ∈ Subalgebra.centralizer R ({d, b} : Set A) := by
  rw [Subalgebra.mem_centralizer_iff]
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact (h.centralizerProjection_commute_seed a).eq.symm
  · have hx' : x = b := Set.mem_singleton_iff.mp hx
    subst x
    exact (h.centralizerProjection_commute_partner a).eq.symm

/-- Every common-commutant element is fixed by the constructed projection. -/
theorem centralizerProjection_eq_self (h : IsDualSeedPair d b) {a : A}
    (hd : Commute a d) (hb : Commute a b) : centralizerProjection R d b a = a := by
  have hp : Commute a (polePlus d b) := hd.mul_right hb
  have hq : Commute a (poleMinus d b) := hb.mul_right hd
  have hr : Commute a (zeroModeSupport d b) :=
    ((Commute.one_right a).sub_right hp).sub_right hq
  have hpap : polePlus d b * a * polePlus d b = a * polePlus d b := by
    rw [← hp.eq, mul_assoc, h.pp]
  have hbad : b * a * d = a * poleMinus d b := by
    rw [← hb.eq, mul_assoc]
    rfl
  have hrar : zeroModeSupport d b * a * zeroModeSupport d b =
      a * zeroModeSupport d b := by
    rw [← hr.eq, mul_assoc, harmonic_idempotent h]
  rw [centralizerProjection_apply, hpap, hbad, hrar, ← mul_add, ← mul_add]
  have hsum : polePlus d b + poleMinus d b + zeroModeSupport d b = 1 := by
    change polePlus d b + poleMinus d b + (1 - polePlus d b - poleMinus d b) = 1
    abel
  rw [hsum, mul_one]

/-- Fixed points are exactly the native joint centralizer. -/
theorem centralizerProjection_eq_self_iff (h : IsDualSeedPair d b) (a : A) :
    centralizerProjection R d b a = a ↔ a ∈ Subalgebra.centralizer R ({d, b} : Set A) := by
  constructor
  · intro ha
    rw [← ha]
    exact h.centralizerProjection_mem a
  · intro ha
    have hc := (Subalgebra.mem_centralizer_iff R).mp ha
    exact h.centralizerProjection_eq_self
      (hc d (Set.mem_insert d {b})).symm
      (hc b (Set.mem_insert_of_mem d (Set.mem_singleton b))).symm

/-- An idempotent native linear endomorphism, derived from the fixed-point theorem. -/
theorem centralizerProjection_idempotent (h : IsDualSeedPair d b) :
    (centralizerProjection R d b).comp (centralizerProjection R d b) =
      centralizerProjection R d b := by
  ext a
  exact h.centralizerProjection_eq_self
    (h.centralizerProjection_commute_seed a) (h.centralizerProjection_commute_partner a)

/-- Surjectivity onto the native common-commutant submodule is constructive. -/
theorem centralizerProjection_range (h : IsDualSeedPair d b) :
    LinearMap.range (centralizerProjection R d b) =
      (Subalgebra.centralizer R ({d, b} : Set A)).toSubmodule := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact h.centralizerProjection_mem x
  · intro ha
    exact ⟨a, (h.centralizerProjection_eq_self_iff a).mpr ha⟩

@[simp] theorem centralizerProjection_one (h : IsDualSeedPair d b) :
    centralizerProjection R d b 1 = 1 :=
  h.centralizerProjection_eq_self (Commute.one_left d) (Commute.one_left b)

@[simp] theorem centralizerProjection_seed (h : IsDualSeedPair d b) :
    centralizerProjection R d b d = 0 := by
  rw [centralizerProjection_apply, h.pd, h.dp, mul_assoc, h.d_sq,
    mul_zero, h.residual_seed.1, zero_mul, add_zero, add_zero]

@[simp] theorem centralizerProjection_partner (h : IsDualSeedPair d b) :
    centralizerProjection R d b b = 0 := by
  rw [centralizerProjection_apply, h.pb, zero_mul, h.b_sq, zero_mul,
    h.residual_partner.1, zero_mul, add_zero, add_zero]

theorem centralizerProjection_polePlus (h : IsDualSeedPair d b) :
    centralizerProjection R d b (polePlus d b) = carrierSupport d b := by
  have hrp : zeroModeSupport d b * polePlus d b = 0 := by
    change zeroModeSupport d b * (d * b) = 0
    rw [← mul_assoc, h.residual_seed.1, zero_mul]
  rw [centralizerProjection_apply, h.pp, h.pp, h.bp, hrp, zero_mul, add_zero]
  rfl

theorem centralizerProjection_poleMinus (h : IsDualSeedPair d b) :
    centralizerProjection R d b (poleMinus d b) = 0 := by
  have hrq : zeroModeSupport d b * poleMinus d b = 0 := by
    change zeroModeSupport d b * (b * d) = 0
    rw [← mul_assoc, h.residual_partner.1, zero_mul]
  rw [centralizerProjection_apply, h.pq, zero_mul, h.bq, zero_mul,
    hrq, zero_mul, add_zero, add_zero]

theorem centralizerProjection_phase (h : IsDualSeedPair d b) :
    centralizerProjection R d b (phasePolarization d b) = carrierSupport d b := by
  change centralizerProjection R d b (polePlus d b - poleMinus d b) = _
  rw [map_sub, h.centralizerProjection_polePlus, h.centralizerProjection_poleMinus,
    sub_zero]

/-- The directional projection is not invariant under arbitrary parabolic shear. -/
theorem centralizerProjection_unipotent_partner (h : IsDualSeedPair d b) (s : R) :
    centralizerProjection R d b ((1 + s • d) * b * (1 - s • d)) =
      s • carrierSupport d b := by
  have hs : (1 + s • d) * b * (1 - s • d) =
      b + s • phasePolarization d b - (s * s) • d := by
    change _ = b + s • (d * b - b * d) - (s * s) • d
    simp only [add_mul, mul_sub, mul_one, one_mul, mul_smul_comm,
      smul_mul_assoc, smul_add, smul_smul, h.inner, smul_sub]
    abel
  rw [hs, map_sub, map_add, map_smul, map_smul, h.centralizerProjection_partner,
    h.centralizerProjection_phase, h.centralizerProjection_seed,
    smul_zero, zero_add, sub_zero]

/-- A simultaneous odd commutation rule is converted to an ordinary common
commutant by the existing global parity involution, including the residual corner. -/
theorem centralizerProjection_of_anticommute (h : IsDualSeedPair d b) (a : A)
    (hd : a * d = -(d * a)) (hb : a * b = -(b * a)) :
    centralizerProjection R d b a = a * superInvolution d b := by
  have hc (x y : A) (hx : a * x = -(x * a)) (hy : a * y = -(y * a)) :
      Commute a (x * y) := by
    change a * (x * y) = (x * y) * a
    rw [← mul_assoc, hx, neg_mul, mul_assoc, hy, mul_neg, neg_neg, ← mul_assoc]
  have hp : Commute a (polePlus d b) := hc d b hd hb
  have hq : Commute a (poleMinus d b) := hc b d hb hd
  have hr : Commute a (zeroModeSupport d b) :=
    ((Commute.one_right a).sub_right hp).sub_right hq
  have hpap : polePlus d b * a * polePlus d b = a * polePlus d b := by
    rw [← hp.eq, mul_assoc, h.pp]
  have hba : b * a = -(a * b) := by
    simpa only [neg_neg] using (congrArg Neg.neg hb).symm
  have hbad : b * a * d = -(a * poleMinus d b) := by
    rw [hba, neg_mul, mul_assoc]
    rfl
  have hrar : zeroModeSupport d b * a * zeroModeSupport d b =
      a * zeroModeSupport d b := by
    rw [← hr.eq, mul_assoc, harmonic_idempotent h]
  rw [centralizerProjection_apply, hpap, hbad, hrar]
  change _ = a * (polePlus d b - poleMinus d b + zeroModeSupport d b)
  noncomm_ring

/-- A nonzero seed forces a concrete multiplicativity failure. -/
theorem centralizerProjection_mul_ne (h : IsDualSeedPair d b) (hd : d ≠ 0) :
    centralizerProjection R d b (d * b) ≠
      centralizerProjection R d b d * centralizerProjection R d b b := by
  change centralizerProjection R d b (polePlus d b) ≠ _
  rw [h.centralizerProjection_polePlus, h.centralizerProjection_seed,
    h.centralizerProjection_partner, zero_mul]
  exact h.support_ne_zero hd

end IsDualSeedPair

/-- A bimodule law over the joint commutant. The seed equations are not needed. -/
theorem centralizerProjection_bimodule (d b a c e : A)
    (hcd : Commute c d) (hcb : Commute c b)
    (hed : Commute e d) (heb : Commute e b) :
    centralizerProjection R d b (c * a * e) = c * centralizerProjection R d b a * e := by
  have hcp : Commute c (polePlus d b) := hcd.mul_right hcb
  have hep : Commute e (polePlus d b) := hed.mul_right heb
  have hcr : Commute c (zeroModeSupport d b) :=
    ((Commute.one_right c).sub_right hcp).sub_right (hcb.mul_right hcd)
  have her : Commute e (zeroModeSupport d b) :=
    ((Commute.one_right e).sub_right hep).sub_right (heb.mul_right hed)
  have hs (u v : A) (hcu : Commute c u) (hev : Commute e v) :
      u * (c * a * e) * v = c * (u * a * v) * e := by
    calc
      _ = (u * c) * a * (e * v) := by noncomm_ring
      _ = (c * u) * a * (v * e) := by rw [← hcu.eq, hev.eq]
      _ = _ := by noncomm_ring
  simp only [centralizerProjection_apply, mul_add, add_mul]
  rw [hs _ _ hcp hep, hs _ _ hcb hed, hs _ _ hcr her]

end InfoGeometry.Core.DualSeedPeirce
