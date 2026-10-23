/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Singular.MoorePenrose

/-!
# Transport of the Penrose equations

A change of coordinates transports both multiplication and the involution.
The transported involution below derives all four Penrose equations from the
source pair. No projector-covariance equation is assumed. With a fixed target
involution, a star-preserving ring homomorphism is sufficient instead.
-/

namespace InfoGeometry.Singular.MoorePenrose

variable {R S : Type*} [Ring R] [StarRing R] [Ring S]

/-- The involution induced on the target by a change of coordinates. -/
def transportedStar (e : R ≃+* S) (x : S) : S := e (star (e.symm x))

@[simp] theorem transportedStar_apply (e : R ≃+* S) (x : R) :
    transportedStar e (e x) = e (star x) := by
  simp [transportedStar]

theorem transportedStar_involutive (e : R ≃+* S) (x : S) :
    transportedStar e (transportedStar e x) = x := by
  simp [transportedStar]

theorem transportedStar_mul (e : R ≃+* S) (x y : S) :
    transportedStar e (x * y) = transportedStar e y * transportedStar e x := by
  simp [transportedStar, star_mul]

theorem transportedStar_add (e : R ≃+* S) (x y : S) :
    transportedStar e (x + y) = transportedStar e x + transportedStar e y := by
  simp [transportedStar, star_add]

/-- The four Penrose equations survive arbitrary ring equivalences when the
involution is transported. This includes non-unitary changes of coordinates. -/
theorem IsMoorePenroseInverse.transport {a b : R}
    (h : IsMoorePenroseInverse a b) (e : R ≃+* S) :
    e a * e b * e a = e a ∧
    e b * e a * e b = e b ∧
    transportedStar e (e a * e b) = e a * e b ∧
    transportedStar e (e b * e a) = e b * e a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg e h.aba_eq_a
  · simpa only [map_mul] using congrArg e h.bab_eq_b
  · rw [← map_mul, transportedStar_apply, h.ab_adj_eq]
  · rw [← map_mul, transportedStar_apply, h.ba_adj_eq]

variable [StarRing S]

/-- Exact fixed-involution transport criterion for a particular Penrose pair.
Global preservation of star is unnecessary: the two transported support
idempotents are the only self-adjointness conditions needed. -/
theorem IsMoorePenroseInverse.map_iff {a b : R}
    (h : IsMoorePenroseInverse a b) (f : R →+* S) :
    IsMoorePenroseInverse (f a) (f b) ↔
      star (f (a * b)) = f (a * b) ∧ star (f (b * a)) = f (b * a) := by
  constructor
  · intro hm
    simpa only [map_mul] using And.intro hm.ab_adj_eq hm.ba_adj_eq
  · rintro ⟨hab, hba⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [map_mul] using congrArg f h.aba_eq_a
    · simpa only [map_mul] using congrArg f h.bab_eq_b
    · simpa only [map_mul] using hab
    · simpa only [map_mul] using hba

/-- Given an actual target inverse, covariance is equivalent to local
self-adjointness of the two transported support idempotents. The map need
not be injective, surjective, or star-preserving. -/
theorem IsMoorePenroseInverse.target_eq_map_iff {a b : R} {c : S}
    (h : IsMoorePenroseInverse a b) (f : R →+* S)
    (hc : IsMoorePenroseInverse (f a) c) :
    c = f b ↔
      star (f (a * b)) = f (a * b) ∧ star (f (b * a)) = f (b * a) := by
  constructor
  · intro heq
    subst c
    exact (h.map_iff f).mp hc
  · intro hs
    exact MoorePenrose_unique hc ((h.map_iff f).mpr hs)

/-- Fixed-involution covariance follows from preservation of star, rather
than from assuming the desired projector transport as witness data. -/
theorem IsMoorePenroseInverse.map {a b : R}
    (h : IsMoorePenroseInverse a b) (f : R →+* S)
    (hf : ∀ x : R, f (star x) = star (f x)) :
    IsMoorePenroseInverse (f a) (f b) := by
  apply (h.map_iff f).mpr
  constructor
  · rw [← hf, h.ab_adj_eq]
  · rw [← hf, h.ba_adj_eq]

/-- Uniqueness identifies any target Moore--Penrose inverse with the
transported source inverse under a star-preserving equivalence. -/
theorem IsMoorePenroseInverse.target_eq_map {a b : R} {c : S}
    (h : IsMoorePenroseInverse a b) (e : R ≃+* S)
    (he : ∀ x : R, e (star x) = star (e x))
    (hc : IsMoorePenroseInverse (e a) c) : c = e b := by
  exact MoorePenrose_unique hc (h.map e.toRingHom he)

end InfoGeometry.Singular.MoorePenrose
