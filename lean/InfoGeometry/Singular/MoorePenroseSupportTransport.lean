/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenroseTransport

/-!
# Separate covariance criteria for the two Penrose supports

For an actual source Penrose pair and an actual target inverse under a ring
homomorphism, each support transports precisely when that mapped support is
self-adjoint. The other support need not transport. No global star compatibility,
injectivity, positivity, or projector transport witness is assumed.
-/

namespace InfoGeometry.Singular.MoorePenrose

variable {R S : Type*} [Ring R] [StarRing R] [Ring S] [StarRing S]

private theorem selfAdjoint_eq_of_mutual_absorption {p q : S}
    (hp : star p = p) (hq : star q = q) (hpq : p * q = q) (hqp : q * p = p) :
    p = q := by
  have hs := congrArg star hqp
  rw [star_mul, hp, hq] at hs
  exact hs.symm.trans hpq

theorem IsMoorePenroseInverse.range_support_map_iff {a b : R} {c : S}
    (hab : IsMoorePenroseInverse a b) (f : R →+* S)
    (hc : IsMoorePenroseInverse (f a) c) :
    f a * c = f (a * b) ↔ star (f (a * b)) = f (a * b) := by
  constructor
  · intro h
    rw [← h]
    exact hc.ab_adj_eq
  · intro hs
    have hm : f a * f b * f a = f a := by
      simpa only [map_mul] using congrArg f hab.aba_eq_a
    rw [map_mul] at hs ⊢
    apply selfAdjoint_eq_of_mutual_absorption hc.ab_adj_eq hs
    · calc
        (f a * c) * (f a * f b) = (f a * c * f a) * f b := by simp only [mul_assoc]
        _ = f a * f b := by rw [hc.aba_eq_a]
    · calc
        (f a * f b) * (f a * c) = (f a * f b * f a) * c := by simp only [mul_assoc]
        _ = f a * c := by rw [hm]

theorem IsMoorePenroseInverse.domain_support_map_iff {a b : R} {c : S}
    (hab : IsMoorePenroseInverse a b) (f : R →+* S)
    (hc : IsMoorePenroseInverse (f a) c) :
    c * f a = f (b * a) ↔ star (f (b * a)) = f (b * a) := by
  constructor
  · intro h
    rw [← h]
    exact hc.ba_adj_eq
  · intro hs
    have hm : f a * f b * f a = f a := by
      simpa only [map_mul] using congrArg f hab.aba_eq_a
    rw [map_mul] at hs ⊢
    have hbc : (f b * f a) * (c * f a) = f b * f a := by
      calc
        (f b * f a) * (c * f a) = f b * (f a * c * f a) := by simp only [mul_assoc]
        _ = f b * f a := by rw [hc.aba_eq_a]
    have hce : (c * f a) * (f b * f a) = c * f a := by
      calc
        (c * f a) * (f b * f a) = c * (f a * f b * f a) := by simp only [mul_assoc]
        _ = c * f a := by rw [hm]
    have hstar := congrArg star hce
    rw [star_mul, hs, hc.ba_adj_eq] at hstar
    exact hstar.symm.trans hbc

end InfoGeometry.Singular.MoorePenrose
