/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Clifford.LorentzianBivectorSignatureBridge

/-!
# Clifford sums with unrestricted mixed commutators

Every product is in a potentially noncommutative ring. The mixed commutators
are retained until compatibility is explicitly supplied. In particular the
coefficient pair is never assumed to commute. These are algebraic identities,
with no differential-geometric interpretation built into the definitions.
-/

namespace InfoGeometry.OperatorAlgebra.CliffordDirac

open scoped BigOperators

section Ring

variable {A : Type*} [Ring A]

/-- Reordering a finite operator square produces exactly these mixed defects. -/
theorem sum_sq_with_mixed_commutators {ι : Type*} [Fintype ι] (g x : ι → A) :
    (∑ i, g i * x i) * (∑ i, g i * x i) =
      (∑ i, ∑ j, (g i * g j) * (x i * x j)) +
        ∑ i, ∑ j, g i * ⁅x i, g j⁆ * x j := by
  calc
    _ = ∑ i, ∑ j, (g i * x i) * (g j * x j) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j,
        ((g i * g j) * (x i * x j) + g i * ⁅x i, g j⁆ * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Ring.lie_def]
      noncomm_ring
    _ = _ := by simp only [Finset.sum_add_distrib]

/-- No relation on any of the four inputs is used in this expansion. -/
theorem two_sum_sq_with_mixed_commutators (g h x y : A) :
    (g * x + h * y) * (g * x + h * y) =
      (g * g) * (x * x) + (h * h) * (y * y) +
        ((g * h) * (x * y) + (h * g) * (y * x)) +
        g * ⁅x, g⁆ * x + g * ⁅x, h⁆ * y +
        h * ⁅y, g⁆ * x + h * ⁅y, h⁆ * y := by
  simp only [Ring.lie_def]
  noncomm_ring

/-- The two-generator Clifford square without any mixed commutation hypotheses. -/
theorem clifford_sum_sq_with_defect (g h x y : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0) :
    (g * x + h * y) * (g * x + h * y) =
      x * x + y * y + (g * h) * ⁅x, y⁆ +
        g * ⁅x, g⁆ * x + g * ⁅x, h⁆ * y +
        h * ⁅y, g⁆ * x + h * ⁅y, h⁆ * y := by
  have hswap : h * g = -(g * h) := eq_neg_of_add_eq_zero_right hanti
  rw [two_sum_sq_with_mixed_commutators, hg, hh, hswap]
  simp only [Ring.lie_def]
  noncomm_ring

/-- Compatibility removes only the mixed defects, not the coefficient curvature. -/
theorem clifford_sum_sq (g h x y : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y)
    (chx : Commute h x) (chy : Commute h y) :
    (g * x + h * y) * (g * x + h * y) =
      x * x + y * y + (g * h) * ⁅x, y⁆ := by
  rw [clifford_sum_sq_with_defect g h x y hg hh hanti,
    cgx.symm.lie_eq, chx.symm.lie_eq, cgy.symm.lie_eq, chy.symm.lie_eq]
  simp only [mul_zero, zero_mul, add_zero]

theorem clifford_sub_sq (g h x y : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y)
    (chx : Commute h x) (chy : Commute h y) :
    (g * x - h * y) * (g * x - h * y) =
      x * x + y * y - (g * h) * ⁅x, y⁆ := by
  have hn : ⁅x, -y⁆ = -⁅x, y⁆ := by simp only [Ring.lie_def]; noncomm_ring
  simpa only [hn, mul_neg, neg_mul, neg_neg, sub_eq_add_neg] using
    clifford_sum_sq g h x (-y) hg hh hanti cgx cgy.neg_right chx chy.neg_right

theorem clifford_squares_add (g h x y : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y)
    (chx : Commute h x) (chy : Commute h y) :
    (g * x + h * y) * (g * x + h * y) +
      (g * x - h * y) * (g * x - h * y) = (2 : ℕ) • (x * x + y * y) := by
  rw [clifford_sum_sq g h x y hg hh hanti cgx cgy chx chy,
    clifford_sub_sq g h x y hg hh hanti cgx cgy chx chy, two_nsmul]
  abel

theorem clifford_squares_sub (g h x y : A)
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y)
    (chx : Commute h x) (chy : Commute h y) :
    (g * x + h * y) * (g * x + h * y) -
      (g * x - h * y) * (g * x - h * y) = (2 : ℕ) • ((g * h) * ⁅x, y⁆) := by
  rw [clifford_sum_sq g h x y hg hh hanti cgx cgy chx chy,
    clifford_sub_sq g h x y hg hh hanti cgx cgy chx chy, two_nsmul]
  abel

/-- Factor reversal differs by the paired commutators. -/
theorem sub_factor_reversal (g h x y : A) :
    (g * x + h * y) - (x * g + y * h) = ⁅g, x⁆ + ⁅h, y⁆ := by
  simp only [Ring.lie_def]
  abel

/-- A Clifford bivector cannot annihilate a nonzero coefficient. -/
theorem bivector_mul_ne_zero_iff {g h : A}
    (hg : g * g = 1) (hh : h * h = 1) (hanti : g * h + h * g = 0) (z : A) :
    (g * h) * z ≠ 0 ↔ z ≠ 0 := by
  have hs := InfoGeometry.Clifford.LorentzianBivectorSignatureBridge.positive_bivector_sq_neg_one
    hg hh hanti
  constructor
  · intro hz hz0
    exact hz (by rw [hz0, mul_zero])
  · intro hz heq
    have heq' := congrArg (fun w => (g * h) * w) heq
    rw [← mul_assoc, hs, neg_one_mul, mul_zero, neg_eq_zero] at heq'
    exact hz heq'

/-- The sign flip is inner conjugation by the first Clifford involution. -/
theorem clifford_reflection (g h x y : A)
    (hg : g * g = 1) (hanti : g * h + h * g = 0)
    (cgx : Commute g x) (cgy : Commute g y) :
    g * (g * x + h * y) * g = g * x - h * y := by
  have hswap : g * h = -(h * g) := eq_neg_of_add_eq_zero_left hanti
  calc
    _ = (g * g) * (x * g) + (g * h) * (y * g) := by noncomm_ring
    _ = (g * g) * (g * x) - (h * (g * g)) * y := by
      rw [← cgx.eq, ← cgy.eq, hswap]
      noncomm_ring
    _ = _ := by rw [hg, one_mul, mul_one]

end Ring

section Star

variable {A : Type*} [Ring A] [StarRing A]

/-- Self-adjoint factors identify factor reversal with the actual adjoint. -/
theorem star_clifford_sum {g h x y : A}
    (hg : IsSelfAdjoint g) (hh : IsSelfAdjoint h)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    star (g * x + h * y) = x * g + y * h := by
  calc
    star (g * x + h * y) = star x * star g + star y * star h := by
      rw [star_add, star_mul, star_mul]
    _ = x * g + y * h := by rw [hg.star_eq, hh.star_eq, hx.star_eq, hy.star_eq]

end Star

section GeneratedAlgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {S : Set A} {g h x y : A}

theorem clifford_sum_mem_adjoin (hg : g ∈ S) (hh : h ∈ S) (hx : x ∈ S) (hy : y ∈ S) :
    g * x + h * y ∈ Algebra.adjoin R S :=
  (Algebra.adjoin R S).add_mem
    ((Algebra.adjoin R S).mul_mem (Algebra.subset_adjoin hg) (Algebra.subset_adjoin hx))
    ((Algebra.adjoin R S).mul_mem (Algebra.subset_adjoin hh) (Algebra.subset_adjoin hy))

theorem sum_squares_mem_adjoin (hx : x ∈ S) (hy : y ∈ S) :
    x * x + y * y ∈ Algebra.adjoin R S :=
  clifford_sum_mem_adjoin hx hy hx hy

theorem curvature_mem_adjoin (hg : g ∈ S) (hh : h ∈ S) (hx : x ∈ S) (hy : y ∈ S) :
    (g * h) * ⁅x, y⁆ ∈ Algebra.adjoin R S := by
  apply (Algebra.adjoin R S).mul_mem
  · exact (Algebra.adjoin R S).mul_mem (Algebra.subset_adjoin hg) (Algebra.subset_adjoin hh)
  · exact (Algebra.adjoin R S).sub_mem
      ((Algebra.adjoin R S).mul_mem (Algebra.subset_adjoin hx) (Algebra.subset_adjoin hy))
      ((Algebra.adjoin R S).mul_mem (Algebra.subset_adjoin hy) (Algebra.subset_adjoin hx))

/-- Every element of the native joint centralizer commutes with every generated element. -/
theorem centralizer_commute_of_mem_adjoin {c z : A}
    (hc : c ∈ Subalgebra.centralizer R S) (hz : z ∈ Algebra.adjoin R S) : Commute c z := by
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz
  intro a ha
  exact ((Subalgebra.mem_centralizer_iff R).mp hc a ha).symm

end GeneratedAlgebra

end InfoGeometry.OperatorAlgebra.CliffordDirac
