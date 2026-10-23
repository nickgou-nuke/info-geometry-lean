/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Singular.MoorePenroseChiralDefects

/-!
# Chiral Hodge--Dirac algebra of a square-zero Moore--Penrose pair

For an element `a` with `a * a = 0` and a Moore--Penrose inverse `m`, the two
supports

`P₊ = a m`,  `P₋ = m a`

are orthogonal idempotents.  Their sum is the nonharmonic support, and

`P₀ = 1 - P₊ - P₋`

is the harmonic complement.  The support difference `Γ = P₊ - P₋` is a
tripotent, squares to the nonharmonic support, and anticommutes with the
normalized operator `a + m`.

This file proves the algebraic identities only.  The normalized operator is not
the metric Hodge--Dirac operator `a + star a`; no identification of `m` with
`star a` is made.  The harmonic projection is an algebraic complement; no
analytical Fredholm or spectral claim is asserted.  The Hilbert-space
adjoint/Moore--Penrose existence theory is owned elsewhere.
-/

namespace InfoGeometry.Singular.MoorePenrose

variable {R : Type*} [Ring R] [StarRing R]

/-- The exact/range support `P₊ = a m`. -/
def exactSupport (a m : R) : R := a * m

/-- The coexact/domain support `P₋ = m a`. -/
def coexactSupport (a m : R) : R := m * a

/-- The algebraic harmonic complement `P₀ = 1 - P₊ - P₋`. -/
def harmonicSupport (a m : R) : R := 1 - exactSupport a m - coexactSupport a m

/-- The chiral support difference `Γ = P₊ - P₋`. -/
def chiralSupport (a m : R) : R := exactSupport a m - coexactSupport a m

/-- The normalized square-zero operator `𝒟 = a + m`. -/
def normalizedDirac (a m : R) : R := a + m

/-- The complete algebraic chiral Hodge--Dirac package for a square-zero
Moore--Penrose pair.  The predicate is stated as a named proposition so that
shell and graph owners can consume the package without restating its long
conjunction. -/
def SquareZeroChiralHodge (a m : R) : Prop :=
  (exactSupport a m + coexactSupport a m + harmonicSupport a m = 1) ∧
  (exactSupport a m * exactSupport a m = exactSupport a m ∧
    coexactSupport a m * coexactSupport a m = coexactSupport a m ∧
    harmonicSupport a m * harmonicSupport a m = harmonicSupport a m) ∧
  (exactSupport a m * coexactSupport a m = 0 ∧
    coexactSupport a m * exactSupport a m = 0 ∧
    exactSupport a m * harmonicSupport a m = 0 ∧
    harmonicSupport a m * exactSupport a m = 0 ∧
    coexactSupport a m * harmonicSupport a m = 0 ∧
    harmonicSupport a m * coexactSupport a m = 0) ∧
  (normalizedDirac a m * normalizedDirac a m =
    exactSupport a m + coexactSupport a m) ∧
  (chiralSupport a m * chiralSupport a m =
    exactSupport a m + coexactSupport a m ∧
    chiralSupport a m * chiralSupport a m * chiralSupport a m =
      chiralSupport a m) ∧
  (chiralSupport a m * exactSupport a m = exactSupport a m ∧
    exactSupport a m * chiralSupport a m = exactSupport a m ∧
    chiralSupport a m * coexactSupport a m = -coexactSupport a m ∧
    coexactSupport a m * chiralSupport a m = -coexactSupport a m) ∧
  (chiralSupport a m * a = a ∧
    a * chiralSupport a m = -a ∧
    chiralSupport a m * m = -m ∧
    m * chiralSupport a m = m) ∧
  (chiralSupport a m * normalizedDirac a m +
    normalizedDirac a m * chiralSupport a m = 0) ∧
  (a * harmonicSupport a m = 0 ∧
    harmonicSupport a m * a = 0 ∧
    m * harmonicSupport a m = 0 ∧
    harmonicSupport a m * m = 0 ∧
    normalizedDirac a m * harmonicSupport a m = 0 ∧
    harmonicSupport a m * normalizedDirac a m = 0)

/-! The involution transports the local Hodge operators to the reversed
pair `(star m, star a)`.  These identities are purely formal and do not
require a Moore--Penrose or square-zero hypothesis. -/

theorem exactSupport_star_transport (a m : R) :
    star (exactSupport a m) = exactSupport (star m) (star a) := by
  unfold exactSupport
  rw [star_mul]

theorem coexactSupport_star_transport (a m : R) :
    star (coexactSupport a m) = coexactSupport (star m) (star a) := by
  unfold coexactSupport
  rw [star_mul]

theorem harmonicSupport_star_transport (a m : R) :
    star (harmonicSupport a m) = harmonicSupport (star m) (star a) := by
  rw [harmonicSupport, star_sub, star_sub, star_one,
    exactSupport_star_transport, coexactSupport_star_transport]
  unfold harmonicSupport exactSupport coexactSupport
  noncomm_ring

theorem chiralSupport_star_transport (a m : R) :
    star (chiralSupport a m) = chiralSupport (star m) (star a) := by
  rw [chiralSupport, star_sub,
    exactSupport_star_transport, coexactSupport_star_transport]
  unfold chiralSupport exactSupport coexactSupport
  noncomm_ring

theorem normalizedDirac_star_transport (a m : R) :
    star (normalizedDirac a m) = normalizedDirac (star m) (star a) := by
  unfold normalizedDirac
  rw [star_add]
  abel

namespace IsMoorePenroseInverse

variable {a m : R}

/-- Moore--Penrose axioms transport to the reversed involutive pair. -/
theorem star_reverse (h : IsMoorePenroseInverse a m) :
    IsMoorePenroseInverse (star m) (star a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [star_mul, star_star, mul_assoc] using congrArg star h.bab_eq_b
  · simpa only [star_mul, star_star, mul_assoc] using congrArg star h.aba_eq_a
  · calc
      star (star m * star a) = a * m := by simp only [star_mul, star_star]
      _ = star (a * m) := h.ab_adj_eq.symm
      _ = star m * star a := by rw [star_mul]
  · calc
      star (star a * star m) = m * a := by simp only [star_mul, star_star]
      _ = star (m * a) := h.ba_adj_eq.symm
      _ = star a * star m := by rw [star_mul]

/-- The exact support is idempotent. -/
theorem exactSupport_idem (h : IsMoorePenroseInverse a m) :
    exactSupport a m * exactSupport a m = exactSupport a m := by
  unfold exactSupport
  calc
    (a * m) * (a * m) = a * (m * a * m) := by noncomm_ring
    _ = a * m := by rw [h.bab_eq_b]

/-- The coexact support is idempotent. -/
theorem coexactSupport_idem (h : IsMoorePenroseInverse a m) :
    coexactSupport a m * coexactSupport a m = coexactSupport a m := by
  unfold coexactSupport
  calc
    (m * a) * (m * a) = m * (a * m * a) := by noncomm_ring
    _ = m * a := by rw [h.aba_eq_a]

/-- Square-zero forces the two supports to annihilate in one order. -/
theorem exactSupport_mul_coexactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    exactSupport a m * coexactSupport a m = 0 := by
  simpa [exactSupport, coexactSupport] using h.range_mul_domain_eq_zero ha

omit [StarRing R] in
/-- The reverse order annihilation law only needs `a * a = 0`. -/
theorem coexactSupport_mul_exactSupport (ha : a * a = 0) :
    coexactSupport a m * exactSupport a m = 0 := by
  simpa [exactSupport, coexactSupport] using
    (domain_mul_range_eq_zero (m := m) ha)

/-- The dual square-zero pair has mutually annihilating supports and a
square-zero Moore--Penrose inverse. -/
theorem dual_square_zero_orthogonality (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    coexactSupport a m * exactSupport a m = 0 ∧
    exactSupport a m * coexactSupport a m = 0 ∧
    m * m = 0 :=
  ⟨coexactSupport_mul_exactSupport ha,
    exactSupport_mul_coexactSupport h ha,
    h.inverse_sq_eq_zero ha⟩

omit [StarRing R] in
/-- The two supports and the harmonic complement form a partition of unity. -/
theorem exactSupport_add_coexactSupport_add_harmonicSupport :
    exactSupport a m + coexactSupport a m + harmonicSupport a m = 1 := by
  unfold harmonicSupport
  abel

/-- The harmonic complement is idempotent. -/
theorem harmonicSupport_idem (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    harmonicSupport a m * harmonicSupport a m = harmonicSupport a m := by
  simpa [harmonicSupport, exactSupport, coexactSupport] using
    (h.harmonic_isStarProjection ha).isIdempotentElem.eq

/-- The harmonic complement annihilates the exact support on the left. -/
theorem harmonicSupport_mul_exactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    harmonicSupport a m * exactSupport a m = 0 := by
  unfold harmonicSupport
  rw [sub_mul, sub_mul, one_mul, exactSupport_idem h,
    coexactSupport_mul_exactSupport ha]
  abel

/-- The harmonic complement annihilates the coexact support on the left. -/
theorem harmonicSupport_mul_coexactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    harmonicSupport a m * coexactSupport a m = 0 := by
  unfold harmonicSupport
  rw [sub_mul, sub_mul, one_mul, exactSupport_mul_coexactSupport h ha,
    coexactSupport_idem h]
  abel

/-- The exact support annihilates the harmonic complement on the right. -/
theorem exactSupport_mul_harmonicSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    exactSupport a m * harmonicSupport a m = 0 := by
  unfold harmonicSupport
  rw [mul_sub, mul_sub, mul_one, exactSupport_idem h,
    exactSupport_mul_coexactSupport h ha]
  abel

/-- The coexact support annihilates the harmonic complement on the right. -/
theorem coexactSupport_mul_harmonicSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    coexactSupport a m * harmonicSupport a m = 0 := by
  unfold harmonicSupport
  rw [mul_sub, mul_sub, mul_one, coexactSupport_mul_exactSupport ha,
    coexactSupport_idem h]
  abel

/-- The harmonic complement annihilates the forward arrow on the left. -/
theorem harmonicSupport_mul_eq_zero (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    harmonicSupport a m * a = 0 := by
  simpa [harmonicSupport, exactSupport, coexactSupport] using
    h.harmonic_mul_eq_zero ha

/-- The forward arrow annihilates the harmonic complement on the right. -/
theorem mul_harmonicSupport_eq_zero (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    a * harmonicSupport a m = 0 := by
  simpa [harmonicSupport, exactSupport, coexactSupport] using
    h.mul_harmonic_eq_zero ha

/-- The reverse arrow annihilates the harmonic complement on the right. -/
theorem inverse_mul_harmonicSupport_eq_zero (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    m * harmonicSupport a m = 0 := by
  simpa [harmonicSupport, exactSupport, coexactSupport] using
    h.inverse_mul_harmonic_eq_zero ha

/-- The harmonic complement annihilates the reverse arrow on the left. -/
theorem harmonicSupport_mul_inverse_eq_zero (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    harmonicSupport a m * m = 0 := by
  unfold harmonicSupport exactSupport coexactSupport
  rw [sub_mul, sub_mul, one_mul, mul_assoc a m m,
    h.inverse_sq_eq_zero ha, mul_zero, h.bab_eq_b]
  abel

/-- The normalized Dirac operator squares to the nonharmonic support. -/
theorem normalizedDirac_sq_support (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    normalizedDirac a m * normalizedDirac a m =
      exactSupport a m + coexactSupport a m := by
  simpa [normalizedDirac, exactSupport, coexactSupport, pow_two] using
    h.normalizedDirac_sq ha

/-- The chiral support squares to the nonharmonic support. -/
theorem chiralSupport_sq_support (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    chiralSupport a m * chiralSupport a m =
      exactSupport a m + coexactSupport a m := by
  unfold chiralSupport
  rw [sub_mul, mul_sub, mul_sub, exactSupport_idem h, coexactSupport_idem h,
    exactSupport_mul_coexactSupport h ha, coexactSupport_mul_exactSupport ha]
  abel

/-- The chiral support acts as `+1` on the exact support. -/
theorem chiralSupport_mul_exactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    chiralSupport a m * exactSupport a m = exactSupport a m := by
  unfold chiralSupport
  rw [sub_mul, exactSupport_idem h, coexactSupport_mul_exactSupport ha,
    sub_zero]

/-- The chiral support acts as `-1` on the coexact support. -/
theorem chiralSupport_mul_coexactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    chiralSupport a m * coexactSupport a m = -coexactSupport a m := by
  unfold chiralSupport
  rw [sub_mul, exactSupport_mul_coexactSupport h ha, coexactSupport_idem h,
    zero_sub]



/-- The chiral support is a tripotent. -/
theorem chiralSupport_cube (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    chiralSupport a m * chiralSupport a m * chiralSupport a m =
      chiralSupport a m := by
  have hsq := chiralSupport_sq_support h ha
  calc
    chiralSupport a m * chiralSupport a m * chiralSupport a m =
        chiralSupport a m * (chiralSupport a m * chiralSupport a m) := by
          rw [mul_assoc]
    _ = chiralSupport a m *
          (exactSupport a m + coexactSupport a m) := by rw [hsq]
    _ = chiralSupport a m * exactSupport a m +
          chiralSupport a m * coexactSupport a m := by rw [mul_add]
    _ = exactSupport a m + (-coexactSupport a m) := by
          rw [chiralSupport_mul_exactSupport h ha,
            chiralSupport_mul_coexactSupport h ha]
    _ = chiralSupport a m := by
          unfold chiralSupport
          abel


/-- The exact support is fixed on the right by the chiral support. -/
theorem exactSupport_mul_chiralSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    exactSupport a m * chiralSupport a m = exactSupport a m := by
  unfold chiralSupport
  rw [mul_sub, exactSupport_idem h, exactSupport_mul_coexactSupport h ha,
    sub_zero]

/-- The coexact support is negated on the right by the chiral support. -/
theorem coexactSupport_mul_chiralSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    coexactSupport a m * chiralSupport a m = -coexactSupport a m := by
  unfold chiralSupport
  rw [mul_sub, coexactSupport_mul_exactSupport ha, coexactSupport_idem h,
    zero_sub]

/-- The chiral support acts as `+1` on the forward arrow. -/
theorem chiralSupport_mul_eq_self (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    chiralSupport a m * a = a := by
  simpa [chiralSupport, exactSupport, coexactSupport] using
    h.chirality_mul_forward ha

/-- The chiral support acts as `-1` on the forward arrow from the right. -/
theorem mul_chiralSupport_eq_neg (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    a * chiralSupport a m = -a := by
  simpa [chiralSupport, exactSupport, coexactSupport] using
    h.forward_mul_chirality ha

/-- The chiral support acts as `-1` on the reverse arrow. -/
theorem chiralSupport_mul_inverse_eq_neg (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    chiralSupport a m * m = -m := by
  simpa [chiralSupport, exactSupport, coexactSupport] using
    h.chirality_mul_inverse ha

/-- The chiral support acts as `+1` on the reverse arrow from the right. -/
theorem inverse_mul_chiralSupport_eq_self (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    m * chiralSupport a m = m := by
  simpa [chiralSupport, exactSupport, coexactSupport] using
    h.inverse_mul_chirality ha

/-- The chiral support anticommutes with the normalized Dirac operator. -/
theorem chiralSupport_anticommute_normalizedDirac
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    chiralSupport a m * normalizedDirac a m +
      normalizedDirac a m * chiralSupport a m = 0 := by
  simpa [chiralSupport, normalizedDirac, exactSupport, coexactSupport] using
    h.chirality_normalizedDirac_anticommute ha

/-- The normalized Dirac operator annihilates the harmonic complement. -/
theorem normalizedDirac_mul_harmonicSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    normalizedDirac a m * harmonicSupport a m = 0 := by
  unfold normalizedDirac
  rw [add_mul, mul_harmonicSupport_eq_zero h ha,
    inverse_mul_harmonicSupport_eq_zero h ha, add_zero]

/-- The harmonic complement annihilates the normalized Dirac operator. -/
theorem harmonicSupport_mul_normalizedDirac (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    harmonicSupport a m * normalizedDirac a m = 0 := by
  unfold normalizedDirac
  rw [mul_add, harmonicSupport_mul_eq_zero h ha,
    harmonicSupport_mul_inverse_eq_zero h ha, add_zero]

/-- **Square-zero chiral Hodge--Dirac decomposition.**
For a square-zero `a` and a Moore--Penrose inverse `m`, the supports `P₊ = a m`
and `P₋ = m a` are orthogonal idempotents, `P₀ = 1 - P₊ - P₋` is their
harmonic complement, `Γ = P₊ - P₋` is a tripotent grading, and the normalized
operator `a + m` anticommutes with `Γ`.  The displayed identities are algebraic;
no spectral, analytical, or metric identification is asserted. -/
theorem squareZero_chiralHodge_decomposition
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    SquareZeroChiralHodge a m := by
  unfold SquareZeroChiralHodge
  refine ⟨exactSupport_add_coexactSupport_add_harmonicSupport,
    ⟨exactSupport_idem h, coexactSupport_idem h, harmonicSupport_idem h ha⟩,
    ⟨exactSupport_mul_coexactSupport h ha,
      coexactSupport_mul_exactSupport ha,
      exactSupport_mul_harmonicSupport h ha,
      harmonicSupport_mul_exactSupport h ha,
      coexactSupport_mul_harmonicSupport h ha,
      harmonicSupport_mul_coexactSupport h ha⟩,
    normalizedDirac_sq_support h ha,
    ⟨chiralSupport_sq_support h ha, chiralSupport_cube h ha⟩,
    ⟨chiralSupport_mul_exactSupport h ha,
      exactSupport_mul_chiralSupport h ha,
      chiralSupport_mul_coexactSupport h ha,
      coexactSupport_mul_chiralSupport h ha⟩,
    ⟨chiralSupport_mul_eq_self h ha,
      mul_chiralSupport_eq_neg h ha,
      chiralSupport_mul_inverse_eq_neg h ha,
      inverse_mul_chiralSupport_eq_self h ha⟩,
    chiralSupport_anticommute_normalizedDirac h ha,
    ⟨mul_harmonicSupport_eq_zero h ha,
      harmonicSupport_mul_eq_zero h ha,
      inverse_mul_harmonicSupport_eq_zero h ha,
      harmonicSupport_mul_inverse_eq_zero h ha,
      normalizedDirac_mul_harmonicSupport h ha,
      harmonicSupport_mul_normalizedDirac h ha⟩⟩

/-- The complete square-zero Hodge package is invariant under the reversed
involutive pair `(a, m) ↦ (star m, star a)`. -/
theorem squareZero_chiralHodge_star_transport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    SquareZeroChiralHodge (star m) (star a) := by
  have h_reverse := h.star_reverse
  have hma : m * m = 0 := h.inverse_sq_eq_zero ha
  have h_star_m : star m * star m = 0 := by
    simpa only [star_mul, star_zero] using congrArg star hma
  exact squareZero_chiralHodge_decomposition h_reverse h_star_m

end IsMoorePenroseInverse

end InfoGeometry.Singular.MoorePenrose

