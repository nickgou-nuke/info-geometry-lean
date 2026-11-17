/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionConjugation
import InfoGeometry.Canonical.SplitOctonionRegularProjectors

/-!
# Scalar potential identities on the full real split-octonion carrier

The product and conjugation are those of the existing quaternion-pair
`SplitOctonion`. The projector operators are reused from
`SplitOctonionRegularProjectors`, including their already proved square-one,
idempotence, complementarity, and eigenvalue identities.

The scalar sandwich with an imaginary middle factor is zero. The symmetric
cross pairing of the two existing null projectors is instead half the split
norm. These are algebraic scalar identities; no Hessian, para-Kähler manifold,
or Monge–Ampère solution is asserted.
-/

namespace SplitOctonion.ScalarPotential

/-- The real scalar pairing defined by the actual Cayley conjugation is
symmetric, although the split-octonion product is not commutative. -/
theorem scalar_pairing_symm (x y : SplitOctonion) :
    (x * splitConj y).a.re = (y * splitConj x).a.re := by
  simp [splitConj, mul_a]
  ring

/-- The scalar sandwich has a fixed bracketing; no associative rewrite of
the split-octonion product is used. -/
theorem scalar_sandwich (x u : SplitOctonion) :
    ((x * u) * splitConj x).a.re = normSQ x * u.a.re := by
  simp [splitConj, normSQ, mul_a, mul_b]
  ring

/-- An imaginary middle factor gives the identically zero proposed scalar
potential. -/
theorem scalar_sandwich_zero (x u : SplitOctonion) (hu : u.a.re = 0) :
    ((x * u) * splitConj x).a.re = 0 := by
  rw [scalar_sandwich, hu, mul_zero]

/-- Polarization of the actual split norm uses the symmetric scalar pairing. -/
theorem normSQ_add (x y : SplitOctonion) :
    normSQ (x + y) = normSQ x + normSQ y +
      2 * (x * splitConj y).a.re := by
  simp [normSQ, splitConj, mul_a]
  ring

/-- The scalar pairing is nondegenerate on all eight real coordinates. -/
theorem scalar_pairing_nondegenerate (x : SplitOctonion)
    (hx : ∀ y : SplitOctonion, (x * splitConj y).a.re = 0) : x = 0 := by
  have ha : Quaternion.normSq x.a = 0 := by
    rw [normSq_eq_re_mul_star]
    simpa only [splitConj, mul_a, neg_zero, star_zero, zero_mul, add_zero]
      using hx ⟨x.a, 0⟩
  have hb : Quaternion.normSq x.b = 0 := by
    have h := hx ⟨0, x.b⟩
    have hneg : -(Quaternion.normSq x.b) = 0 := by
      simpa [splitConj, mul_a, ← normSq_eq_re_mul_star,
        Quaternion.normSq_star] using h
    exact neg_eq_zero.mp hneg
  apply SplitOctonion.ext
  · exact Quaternion.normSq_eq_zero.mp ha
  · exact Quaternion.normSq_eq_zero.mp hb

/-- Left multiplication by the existing split imaginary axis reverses the
norm, with the quaternion norm of the axis as its scale. -/
theorem normSQ_hyperbolicAxisOperator (g : H) (x : SplitOctonion) :
    normSQ (hyperbolicAxisOperator g x) =
      -(Quaternion.normSq g) * normSQ x := by
  simp only [hyperbolicAxisOperator_apply, J_g, normSQ, mul_a, mul_b,
    zero_mul, mul_zero, zero_add, ← normSq_eq_re_mul_star,
    map_mul, Quaternion.normSq_star]
  ring

/-- The positive eigenspace of a normalized split imaginary axis is null. -/
theorem normSQ_eq_zero_of_axis_fixed (g : H)
    (hg : Quaternion.normSq g = 1) (x : SplitOctonion)
    (hx : hyperbolicAxisOperator g x = x) : normSQ x = 0 := by
  have h := normSQ_hyperbolicAxisOperator g x
  rw [hx, hg] at h
  linarith

/-- The negative eigenspace is also null. -/
theorem normSQ_eq_zero_of_axis_antifixed (g : H)
    (hg : Quaternion.normSq g = 1) (x : SplitOctonion)
    (hx : hyperbolicAxisOperator g x = -x) : normSQ x = 0 := by
  have hneg : normSQ (-x) = normSQ x := by
    simp only [normSQ, neg_a, neg_b, star_neg, neg_mul_neg]
  have h := normSQ_hyperbolicAxisOperator g x
  rw [hx, hneg, hg] at h
  linarith

/-- Nullity of the existing positive projector is derived from its actual
operator eigenrelation. -/
theorem hyperbolicProjectorPlus_null (g : H)
    (hg : Quaternion.normSq g = 1) (x : SplitOctonion) :
    normSQ (hyperbolicProjectorPlus g x) = 0 := by
  apply normSQ_eq_zero_of_axis_fixed g hg
  exact LinearMap.congr_fun (hyperbolicAxisOperator_comp_projectorPlus g hg) x

/-- Nullity of the existing negative projector. -/
theorem hyperbolicProjectorMinus_null (g : H)
    (hg : Quaternion.normSq g = 1) (x : SplitOctonion) :
    normSQ (hyperbolicProjectorMinus g x) = 0 := by
  apply normSQ_eq_zero_of_axis_antifixed g hg
  exact LinearMap.congr_fun (hyperbolicAxisOperator_comp_projectorMinus g hg) x

/-- The symmetric cross-potential is half the full split norm. -/
theorem projector_cross_pairing_eq_half_norm (g : H)
    (hg : Quaternion.normSq g = 1) (x : SplitOctonion) :
    ((hyperbolicProjectorPlus g x) *
        splitConj (hyperbolicProjectorMinus g x)).a.re = normSQ x / 2 := by
  have hsum : hyperbolicProjectorPlus g x + hyperbolicProjectorMinus g x = x :=
    LinearMap.congr_fun (hyperbolicProjectorPlus_add_minus g) x
  have h := normSQ_add (hyperbolicProjectorPlus g x)
    (hyperbolicProjectorMinus g x)
  rw [hsum, hyperbolicProjectorPlus_null g hg x,
    hyperbolicProjectorMinus_null g hg x] at h
  linarith

/-- At the split unit ell=`J_g 1` and the scalar state one, the cross-potential
is nonzero, in contrast to the imaginary scalar sandwich. -/
theorem projector_cross_pairing_one :
    ((hyperbolicProjectorPlus (1 : H) (1 : SplitOctonion)) *
        splitConj (hyperbolicProjectorMinus (1 : H) (1 : SplitOctonion))).a.re =
      (1 / 2 : ℝ) := by
  rw [projector_cross_pairing_eq_half_norm (1 : H) (by simp)]
  norm_num [normSQ]

end SplitOctonion.ScalarPotential
