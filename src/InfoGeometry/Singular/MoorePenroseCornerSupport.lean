/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenrose

/-!
# Adjoint support transfer for Moore–Penrose inverses

An oblique corner need not contain its inverse in the unstarred reverse
corner. The general replacement transfers each absorption identity through
the involution. The cuts need not be self-adjoint or even idempotent.
-/
namespace InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse

variable {R : Type*} [Ring R] [StarRing R] {a b p q : R}

/-- Right absorption of an operator transfers to left adjoint absorption of its inverse. -/
theorem star_left_absorption (h : IsMoorePenroseInverse a b) (hq : a * q = a) :
    star q * b = b := by
  have hs : star q * star a = star a := by
    simpa only [star_mul] using congrArg star hq
  calc
    star q * b = star q * ((b * a) * b) := by rw [h.bab_eq_b]
    _ = star q * ((star a * star b) * b) := by
      rw [← star_mul, h.ba_adj_eq]
    _ = ((star q * star a) * star b) * b := by simp only [mul_assoc]
    _ = (star a * star b) * b := by rw [hs]
    _ = b := by rw [← star_mul, h.ba_adj_eq, h.bab_eq_b]

/-- Left absorption of an operator transfers to right adjoint absorption of its inverse. -/
theorem star_right_absorption (h : IsMoorePenroseInverse a b) (hp : p * a = a) :
    b * star p = b := by
  have hs : star a * star p = star a := by
    simpa only [star_mul] using congrArg star hp
  calc
    b * star p = (b * (a * b)) * star p := by rw [← mul_assoc, h.bab_eq_b]
    _ = (b * (star b * star a)) * star p := by
      rw [← star_mul, h.ab_adj_eq]
    _ = b * (star b * (star a * star p)) := by simp only [mul_assoc]
    _ = b * (star b * star a) := by rw [hs]
    _ = b := by rw [← star_mul, h.ab_adj_eq, ← mul_assoc, h.bab_eq_b]

/-- The universally valid reverse-corner support uses adjoints of the cuts. -/
theorem adjoint_reverse_corner (h : IsMoorePenroseInverse a b)
    (hp : p * a = a) (hq : a * q = a) : star q * b * star p = b := by
  rw [h.star_left_absorption hq, h.star_right_absorption hp]

/-- Adjoint support transfer is an equivalence, for arbitrary right cuts. -/
theorem right_absorption_iff (h : IsMoorePenroseInverse a b) :
    a * q = a ↔ star q * b = b := by
  refine ⟨h.star_left_absorption, fun hb => ?_⟩
  have hrev : IsMoorePenroseInverse b a :=
    ⟨h.bab_eq_b, h.aba_eq_a, h.ba_adj_eq, h.ab_adj_eq⟩
  simpa only [star_star] using hrev.star_right_absorption hb

/-- Adjoint support transfer is an equivalence, for arbitrary left cuts. -/
theorem left_absorption_iff (h : IsMoorePenroseInverse a b) :
    p * a = a ↔ b * star p = b := by
  refine ⟨h.star_right_absorption, fun hb => ?_⟩
  have hrev : IsMoorePenroseInverse b a :=
    ⟨h.bab_eq_b, h.aba_eq_a, h.ba_adj_eq, h.ab_adj_eq⟩
  simpa only [star_star] using hrev.star_left_absorption hb

/-- Exact criterion for the unstarred reverse-corner rule. Self-adjointness
of the cuts is sufficient but is not required: their adjoints need only
absorb the original operator on the indicated sides. -/
theorem reverse_corner_iff (h : IsMoorePenroseInverse a b)
    (hp : p * p = p) (hq : q * q = q) :
    q * b * p = b ↔ star p * a = a ∧ a * star q = a := by
  have hleft : star p * a = a ↔ b * p = b := by
    simpa only [star_star] using (h.left_absorption_iff (p := star p))
  have hright : a * star q = a ↔ q * b = b := by
    simpa only [star_star] using (h.right_absorption_iff (q := star q))
  rw [hleft, hright]
  constructor
  · intro hc
    constructor
    · calc
        b * p = (q * b * p) * p := by rw [hc]
        _ = q * b * (p * p) := mul_assoc _ _ _
        _ = b := by rw [hp, hc]
    · calc
        q * b = q * (q * b * p) := by rw [hc]
        _ = (q * q) * b * p := by simp only [mul_assoc]
        _ = b := by rw [hq, hc]
  · rintro ⟨hbp, hqb⟩
    rw [hqb, hbp]

end InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
