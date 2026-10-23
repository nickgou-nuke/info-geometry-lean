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

/-- Similarity preserves self-adjointness of a particular element exactly
when it commutes with the Gram element of the coordinate change. No
idempotence, positivity, or global star-preservation is required. -/
theorem similarity_selfAdjoint_iff_gram_commute {p g h : R}
    (hp : star p = p) (hleft : h * g = 1) (hright : g * h = 1) :
    star (g * p * h) = g * p * h ↔ p * (star g * g) = (star g * g) * p := by
  have hsgsh : star g * star h = 1 := by rw [← star_mul, hleft, star_one]
  have hshsg : star h * star g = 1 := by rw [← star_mul, hright, star_one]
  constructor
  · intro hs
    calc
      p * (star g * g) = star g * (star h * p * star g) * g := by
        simp only [← mul_assoc, hsgsh, one_mul]
      _ = star g * star (g * p * h) * g := by
        simp only [star_mul, hp, mul_assoc]
      _ = star g * (g * p * h) * g := by rw [hs]
      _ = (star g * g) * p := by
        calc
          _ = (star g * g) * p * (h * g) := by simp only [mul_assoc]
          _ = _ := by rw [hleft, mul_one]
  · intro hc
    calc
      star (g * p * h) = star h * p * star g := by
        simp only [star_mul, hp, mul_assoc]
      _ = star h * (p * (star g * g)) * h := by
        calc
          _ = star h * p * star g * (g * h) := by rw [hright, mul_one]
          _ = _ := by simp only [mul_assoc]
      _ = star h * ((star g * g) * p) * h := by rw [hc]
      _ = g * p * h := by simp only [← mul_assoc, hshsg, one_mul]

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

/-- Exact Moore–Penrose covariance criterion for arbitrary invertible
similarity: both source support projections must commute with `star g * g`.
This includes non-unitary similarities whenever these two commutations hold. -/
theorem IsMoorePenroseInverse.similarity_iff {a b g h : R}
    (hab : IsMoorePenroseInverse a b) (hleft : h * g = 1) (hright : g * h = 1) :
    IsMoorePenroseInverse (g * a * h) (g * b * h) ↔
      (a * b) * (star g * g) = (star g * g) * (a * b) ∧
      (b * a) * (star g * g) = (star g * g) * (b * a) := by
  let f : R →+* R :=
    { toFun := fun x => g * x * h
      map_one' := by simpa using hright
      map_zero' := by simp
      map_add' := by intro x y; simp only [mul_add, add_mul]
      map_mul' := by
        intro x y
        calc
          g * (x * y) * h = g * x * (h * g) * y * h := by
            rw [hleft, mul_one]; simp only [mul_assoc]
          _ = (g * x * h) * (g * y * h) := by simp only [mul_assoc] }
  change IsMoorePenroseInverse (f a) (f b) ↔ _
  rw [hab.map_iff f]
  exact and_congr
    (similarity_selfAdjoint_iff_gram_commute hab.ab_adj_eq hleft hright)
    (similarity_selfAdjoint_iff_gram_commute hab.ba_adj_eq hleft hright)

/-- Equality of an actual target inverse with the transported source inverse
is characterized by the two Gram commutation equations. -/
theorem IsMoorePenroseInverse.target_eq_similarity_iff {a b c g h : R}
    (hab : IsMoorePenroseInverse a b) (hc : IsMoorePenroseInverse (g * a * h) c)
    (hleft : h * g = 1) (hright : g * h = 1) :
    c = g * b * h ↔
      (a * b) * (star g * g) = (star g * g) * (a * b) ∧
      (b * a) * (star g * g) = (star g * g) * (b * a) := by
  constructor
  · intro heq
    rw [heq] at hc
    exact (hab.similarity_iff hleft hright).mp hc
  · intro hcomm
    exact MoorePenrose_unique hc ((hab.similarity_iff hleft hright).mpr hcomm)

/-- Fixed-involution similarity fails exactly when at least one support
projection fails to commute with the Gram element. -/
theorem IsMoorePenroseInverse.target_ne_similarity_iff {a b c g h : R}
    (hab : IsMoorePenroseInverse a b) (hc : IsMoorePenroseInverse (g * a * h) c)
    (hleft : h * g = 1) (hright : g * h = 1) :
    c ≠ g * b * h ↔
      (a * b) * (star g * g) ≠ (star g * g) * (a * b) ∨
      (b * a) * (star g * g) ≠ (star g * g) * (b * a) := by
  rw [ne_eq, hab.target_eq_similarity_iff hc hleft hright, not_and_or]

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
