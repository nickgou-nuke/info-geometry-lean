/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Singular.MoorePenroseSectors
import InfoGeometry.Canonical.Drazin

/-!
# Square-zero Moore–Penrose pairs and their Peirce supports

For a square-zero `a`, the Penrose laws force its two supports to annihilate
each other; no additional commuting-support hypothesis is needed. The third
star projection is their harmonic complement. This is an algebraic statement
on any associative star ring, including operator rings, not an isotropic-form
or graph-node classification.

The normalized operator `a + m` below is not the metric Hodge–Dirac operator
`a + star a` unless an additional adjoint/inverse identification is supplied.
Drazin exponents are witnesses, not claims of minimal index. Ordinary
associativity is retained; the distinct Jordan and projected-product defects
remain owned by `InverseKernelSectorAnomalies` and `ProjectedNonassociativeBianchi`.
-/

namespace InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse

variable {R : Type*} [Ring R] [StarRing R] {a m : R}

omit [StarRing R] in
/-- The domain support kills the range support of a square-zero operator. -/
theorem domain_mul_range_eq_zero (ha : a * a = 0) :
    (m * a) * (a * m) = 0 := by
  calc
    _ = m * (a * a) * m := by simp only [mul_assoc]
    _ = 0 := by rw [ha, mul_zero, zero_mul]

/-- Self-adjointness of the supports gives the reverse annihilation law. -/
theorem range_mul_domain_eq_zero (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    (a * m) * (m * a) = 0 := by
  have hs := congrArg star (domain_mul_range_eq_zero (m := m) ha)
  simpa only [star_mul, h.ab_adj_eq, h.ba_adj_eq, star_zero] using hs

/-- The reverse Moore–Penrose arrow is square-zero as well. -/
theorem inverse_sq_eq_zero (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    m * m = 0 := by
  calc
    m * m = (m * a * m) * (m * a * m) := by rw [h.bab_eq_b]
    _ = m * ((a * m) * (m * a)) * m := by simp only [mul_assoc]
    _ = 0 := by rw [h.range_mul_domain_eq_zero ha, mul_zero, zero_mul]

/-- The exact and coexact supports together are a star projection. -/
theorem support_sum_isStarProjection (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) : IsStarProjection (a * m + m * a) := by
  obtain ⟨hp, hq⟩ := ProjectionSectors.mp_supports h
  exact hp.add hq (h.range_mul_domain_eq_zero ha)

/-- The complement of both supports is the algebraic harmonic star projection. -/
theorem harmonic_isStarProjection (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) : IsStarProjection (1 - a * m - m * a) := by
  simpa only [sub_add_eq_sub_sub] using (h.support_sum_isStarProjection ha).one_sub

omit [StarRing R] in
/-- The harmonic complement and the nonharmonic support sum to the identity. -/
theorem harmonic_add_support_eq_one :
    (1 - a * m - m * a) + (a * m + m * a) = 1 := by
  abel

/-- The harmonic complement annihilates the forward differential. -/
theorem harmonic_mul_eq_zero (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    (1 - a * m - m * a) * a = 0 := by
  simp only [sub_mul, one_mul, h.aba_eq_a, mul_assoc, ha, mul_zero, sub_self]

/-- The forward differential annihilates the harmonic complement. -/
theorem mul_harmonic_eq_zero (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    a * (1 - a * m - m * a) = 0 := by
  rw [mul_sub, mul_sub, mul_one, ← mul_assoc, ha, zero_mul, ← mul_assoc, h.aba_eq_a]
  simp

/-- The reverse Moore–Penrose arrow annihilates the harmonic complement. -/
theorem inverse_mul_harmonic_eq_zero (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    m * (1 - a * m - m * a) = 0 := by
  have hm : IsMoorePenroseInverse m a :=
    ⟨h.bab_eq_b, h.aba_eq_a, h.ba_adj_eq, h.ab_adj_eq⟩
  have hh := hm.mul_harmonic_eq_zero (h.inverse_sq_eq_zero ha)
  convert hh using 1; noncomm_ring

/-- The harmonic complement is left-orthogonal to the nonharmonic support. -/
theorem harmonic_mul_support_eq_zero (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    (1 - a * m - m * a) * (a * m + m * a) = 0 := by
  have hha : (1 - a * m - m * a) * a = 0 := h.harmonic_mul_eq_zero ha
  have hhm : (1 - a * m - m * a) * m = 0 := by
    have hmm : m * m = 0 := h.inverse_sq_eq_zero ha
    have hma : m * a * m = m := h.bab_eq_b
    noncomm_ring [hmm, hma]
  rw [mul_add, ← mul_assoc, ← mul_assoc, hha, hhm]
  simp

/-- The nonharmonic support is right-orthogonal to the harmonic complement. -/
theorem support_mul_harmonic_eq_zero (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    (a * m + m * a) * (1 - a * m - m * a) = 0 := by
  have haH : a * (1 - a * m - m * a) = 0 := h.mul_harmonic_eq_zero ha
  have hmH : m * (1 - a * m - m * a) = 0 := h.inverse_mul_harmonic_eq_zero ha
  rw [add_mul, mul_assoc, mul_assoc, haH, hmH]
  simp

/-- An element of the left regular module is harmonic exactly when both arrows
annihilate it. The ring formulation also applies to operator-valued states. -/
theorem harmonic_mul_eq_self_iff (h : IsMoorePenroseInverse a m) (ha : a * a = 0)
    (x : R) : (1 - a * m - m * a) * x = x ↔ a * x = 0 ∧ m * x = 0 := by
  constructor
  · intro hx
    constructor
    · calc
        a * x = a * ((1 - a * m - m * a) * x) := by rw [hx]
        _ = 0 := by rw [← mul_assoc, h.mul_harmonic_eq_zero ha, zero_mul]
    · calc
        m * x = m * ((1 - a * m - m * a) * x) := by rw [hx]
        _ = 0 := by rw [← mul_assoc, h.inverse_mul_harmonic_eq_zero ha, zero_mul]
  · rintro ⟨hax, hmx⟩
    simp [sub_mul, mul_assoc, hax, hmx]

/-- The support difference squares to the nonharmonic support, not necessarily one. -/
theorem chirality_sq (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    (a * m - m * a)^2 = a * m + m * a := by
  obtain ⟨hp, hq⟩ := ProjectionSectors.mp_supports h
  rw [sq, sub_mul, mul_sub, mul_sub, hp.isIdempotentElem.eq,
    hq.isIdempotentElem.eq, h.range_mul_domain_eq_zero ha, domain_mul_range_eq_zero ha]
  abel

/-- The normalized algebraic Dirac square is the nonharmonic support. -/
theorem normalizedDirac_sq (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    (a + m)^2 = a * m + m * a := by
  rw [sq, add_mul, mul_add, mul_add, ha, h.inverse_sq_eq_zero ha]
  simp

/-- The normalized Dirac square and the chirality square coincide: both are the
nonharmonic support. -/
theorem normalizedDirac_sq_eq_chirality_sq (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    (a + m)^2 = (a * m - m * a)^2 := by
  rw [h.normalizedDirac_sq ha, h.chirality_sq ha]

/-- The metric Hodge–Dirac square uses the adjoint `star a`, not the
Moore–Penrose inverse `m`. Recorded here only to keep the two operators
formally distinct. -/
theorem metricDirac_sq (ha : a * a = 0) :
    (a + star a)^2 = a * star a + star a * a := by
  rw [sq, add_mul, mul_add, mul_add, ha]
  have hstar : star a * star a = 0 := by
    rw [← star_mul, ha, star_zero]
  rw [hstar]
  simp

/-- Its inverse on the supported sector is itself; no self-adjointness is asserted. -/
theorem normalizedDirac_drazin (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    InfoGeometry.Canonical.Drazin.IsDrazinInverse (a + m) (a + m) 1 := by
  have hc : (a + m) * (a + m) * (a + m) = a + m := by
    rw [← sq, h.normalizedDirac_sq ha]
    have hm := h.inverse_sq_eq_zero ha
    simp only [add_mul, mul_add, h.aba_eq_a, h.bab_eq_b, mul_assoc, ha, hm, mul_zero,
      zero_add, add_zero]
  exact ⟨rfl, hc, by simpa [pow_two] using hc⟩

end InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse
