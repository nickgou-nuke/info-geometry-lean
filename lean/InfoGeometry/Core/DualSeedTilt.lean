/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedCentralizer

/-!
# Additive tilt of a dual-seed pair

The perturbation is an element `z` of the common commutant, rather than the
commutant subalgebra itself. The bracket is unchanged, while the squares and
Cartan weights acquire explicit defects. Over a field with `2 ≠ 0`, nonzero
tilt has common commutant exactly `C(d,b) ⊓ C(z)`.

The ambient algebra remains unrestricted and noncommutative. No change of
multiplication, topology, measure, or graded differential is asserted.
-/

namespace InfoGeometry.Core.DualSeedPeirce

attribute [local instance 100] LieRing.ofAssociativeRing

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d b z : A}

/-- Opposite additive perturbations from the common commutant preserve the bracket. -/
theorem phasePolarization_tilt (hzd : Commute z d) (hzb : Commute z b) (ε : R) :
    phasePolarization (d + ε • z) (b - ε • z) = phasePolarization d b := by
  change (d + ε • z) * (b - ε • z) - (b - ε • z) * (d + ε • z) =
    d * b - b * d
  simp only [add_mul, mul_sub, sub_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_sub, smul_add, smul_smul, hzd.eq, hzb.eq]
  abel

namespace IsDualSeedPair

/-- Exact square: common commutation does not remove the mixed term. -/
theorem tilt_seed_sq (h : IsDualSeedPair d b) (hzd : Commute z d) (ε : R) :
    (d + ε • z) * (d + ε • z) =
      (2 : ℕ) • (ε • (z * d)) + (ε * ε) • (z * z) := by
  simp only [add_mul, mul_add, h.d_sq, zero_add, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_smul, hzd.eq, two_nsmul]
  abel

/-- The partner has the opposite linear term and the same quadratic term. -/
theorem tilt_partner_sq (h : IsDualSeedPair d b) (hzb : Commute z b) (ε : R) :
    (b - ε • z) * (b - ε • z) =
      -((2 : ℕ) • (ε • (z * b))) + (ε * ε) • (z * z) := by
  simp only [sub_mul, mul_sub, h.b_sq, zero_sub, smul_mul_assoc,
    mul_smul_comm, smul_sub, smul_smul, hzb.eq, two_nsmul]
  abel

/-- The Clifford anticommutator retains both the mixed and quadratic defects. -/
theorem tilt_anticommutator (d b z : A) (hzd : Commute z d)
    (hzb : Commute z b) (ε : R) :
    (d + ε • z) * (b - ε • z) + (b - ε • z) * (d + ε • z) =
      carrierSupport d b + (2 : ℕ) • (ε • (z * (b - d))) -
        (2 : ℕ) • ((ε * ε) • (z * z)) := by
  change _ = d * b + b * d + _ - _
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, smul_smul, smul_sub, smul_add, hzd.eq, hzb.eq, two_nsmul]
  abel

/-- The old Cartan element sees only the original seed component. -/
theorem lie_phase_tilt_seed (h : IsDualSeedPair d b) (hzd : Commute z d)
    (hzb : Commute z b) (ε : R) :
    ⁅phasePolarization d b, d + ε • z⁆ = (2 : ℕ) • d := by
  have hzH := (commute_phasePolarization_of_commute hzd hzb).symm.smul_right ε
  change phasePolarization d b * (d + ε • z) -
    (d + ε • z) * phasePolarization d b = _
  rw [mul_add, add_mul, hzH.eq, h.phase_mul_seed, h.seed_mul_phase, two_nsmul]
  abel

/-- The partner has the opposite weight; its perturbation has weight zero. -/
theorem lie_phase_tilt_partner (h : IsDualSeedPair d b) (hzd : Commute z d)
    (hzb : Commute z b) (ε : R) :
    ⁅phasePolarization d b, b - ε • z⁆ = -((2 : ℕ) • b) := by
  have hzH := (commute_phasePolarization_of_commute hzd hzb).symm.smul_right ε
  change phasePolarization d b * (b - ε • z) -
    (b - ε • z) * phasePolarization d b = _
  rw [mul_sub, sub_mul, hzH.eq, h.phase_mul_partner, h.partner_mul_phase, two_nsmul]
  abel

end IsDualSeedPair
end Ring

section Field

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
variable {d b z : A} {ε : K}

private theorem commute_of_smul_right {a x : A} {c : K}
    (hc : c ≠ 0) (h : Commute a (c • x)) : Commute a x := by
  have he := h.smul_right c⁻¹
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using he

namespace IsDualSeedPair

/-- Nonzero tilt recovers the original seeds and the perturbation from commutation. -/
theorem commute_tilt_iff (h : IsDualSeedPair d b) (hzd : Commute z d)
    (hzb : Commute z b) (hε : ε ≠ 0) (h2 : (2 : K) ≠ 0) (a : A) :
    (Commute a (d + ε • z) ∧ Commute a (b - ε • z)) ↔
      (Commute a d ∧ Commute a b ∧ Commute a z) := by
  constructor
  · rintro ⟨had, hab⟩
    have haH := commute_phasePolarization_of_commute had hab
    rw [phasePolarization_tilt hzd hzb ε] at haH
    have hd := (haH.mul_right had).sub_right (had.mul_right haH)
    have hb := (haH.mul_right hab).sub_right (hab.mul_right haH)
    change Commute a ⁅phasePolarization d b, d + ε • z⁆ at hd
    change Commute a ⁅phasePolarization d b, b - ε • z⁆ at hb
    rw [h.lie_phase_tilt_seed hzd hzb ε] at hd
    rw [h.lie_phase_tilt_partner hzd hzb ε] at hb
    have had' : Commute a d := commute_of_smul_right h2 (by
      simpa only [two_smul K, two_nsmul] using hd)
    have hab' : Commute a b := commute_of_smul_right h2 (by
      simpa only [two_smul K, two_nsmul, neg_neg] using hb.neg_right)
    have haz : Commute a (ε • z) := by
      simpa only [add_sub_cancel_left] using had.sub_right had'
    exact ⟨had', hab', commute_of_smul_right hε haz⟩
  · rintro ⟨had, hab, haz⟩
    exact ⟨had.add_right (haz.smul_right ε), hab.sub_right (haz.smul_right ε)⟩

/-- Exact native subalgebra intersection; the ambient algebra need not commute. -/
theorem centralizer_tilt (h : IsDualSeedPair d b) (hzd : Commute z d)
    (hzb : Commute z b) (hε : ε ≠ 0) (h2 : (2 : K) ≠ 0) :
    Subalgebra.centralizer K ({d + ε • z, b - ε • z} : Set A) =
      Subalgebra.centralizer K ({d, b} : Set A) ⊓
        Subalgebra.centralizer K ({z} : Set A) := by
  ext a
  have pair (x y : A) :
      a ∈ Subalgebra.centralizer K ({x, y} : Set A) ↔
        Commute a x ∧ Commute a y := by
    simp only [Subalgebra.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact and_congr eq_comm eq_comm
  have single : a ∈ Subalgebra.centralizer K ({z} : Set A) ↔ Commute a z := by
    simp only [Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact eq_comm
  change a ∈ Subalgebra.centralizer K ({d + ε • z, b - ε • z} : Set A) ↔
    a ∈ Subalgebra.centralizer K ({d, b} : Set A) ∧
      a ∈ Subalgebra.centralizer K ({z} : Set A)
  rw [pair, pair, single, h.commute_tilt_iff hzd hzb hε h2 a]
  exact and_assoc.symm

/-- Full reflexive square-zero normalization survives exactly the zero perturbation. -/
theorem isDualSeedPair_tilt_iff (h : IsDualSeedPair d b) (hzd : Commute z d)
    (hzb : Commute z b) (h2 : (2 : K) ≠ 0) :
    IsDualSeedPair (d + ε • z) (b - ε • z) ↔ ε • z = 0 := by
  constructor
  · intro ht
    have he := ht.lie_phase_seed
    rw [phasePolarization_tilt hzd hzb ε, h.lie_phase_tilt_seed hzd hzb ε] at he
    have he' : (2 : K) • d = (2 : K) • (d + ε • z) := by
      simpa only [two_smul K, two_nsmul] using he
    have hc := congrArg (fun x : A => (2 : K)⁻¹ • x) he'
    simp only [smul_smul, inv_mul_cancel₀ h2, one_smul] at hc
    exact (add_left_cancel (hc.symm.trans (add_zero d).symm))
  · intro hz
    simpa only [hz, add_zero, sub_zero] using h

end IsDualSeedPair
end Field

end InfoGeometry.Core.DualSeedPeirce
