/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.ThreePointLogarithmicForms
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Four-point logarithmic potential and rational localization

After fixing three distinct projective punctures at `0`, `1`, and infinity,
the remaining coordinate has potential `s log|z| + t log|1-z|` over the reals.
Its derivative is `s/z - t/(1-z)`. Over an arbitrary field, this equation has
the unique puncture-avoiding solution `s/(s+t)` when `s`, `t`, and `s+t` are
nonzero. The Hessian at that solution is nonzero, and the explicitly oriented
rational readout `-PT^2/H` evaluates to `1/s + 1/t`.
The complex potential uses the principal logarithm only locally where both
`z` and `1-z` belong to `Complex.slitPlane`.

The assumptions are algebraic regularity conditions. This module does not
assert a contour-residue theorem, a twisted-cohomology identification, a CHY
representation theorem, a physical amplitude normalization, or an algorithm
for arbitrary Feynman diagrams. In particular the minus sign in the readout
is part of its definition, not an unstated orientation convention.
-/

noncomputable section

namespace InfoGeometry.Feynman.FourPointLogarithmicPotential

section Rational

variable {K : Type*} [Field K]

/-- Coefficient of the logarithmic one-form `s dz/z + t dz/(z-1)`. -/
def scatteringCoefficient (s t z : K) : K := s / z - t / (1 - z)

/-- The gauge-fixed four-point puncture factor used in the rational readout. -/
def punctureParkeTaylor (z : K) : K := 1 / (z * (1 - z))

/-- Derivative of the scattering coefficient on the punctured domain. -/
def hessianCoefficient (s t z : K) : K := -s / z ^ 2 - t / (1 - z) ^ 2

/-- Candidate stationary coordinate; its domain conditions are theorem hypotheses. -/
def stationary (s t : K) : K := s / (s + t)

/-- Oriented algebraic readout. No residue or integration operation is asserted. -/
def algebraicLocalization (s t z : K) : K :=
  -(punctureParkeTaylor z) ^ 2 / hessianCoefficient s t z

theorem one_sub_stationary (s t : K) (hst : s + t ≠ 0) :
    1 - stationary s t = t / (s + t) := by
  unfold stationary
  field_simp [hst] <;> ring

theorem stationary_ne_zero (s t : K) (hs : s ≠ 0) (hst : s + t ≠ 0) :
    stationary s t ≠ 0 :=
  div_ne_zero hs hst

theorem stationary_ne_one (s t : K) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    stationary s t ≠ 1 := by
  have h : 1 - stationary s t ≠ 0 := by
    rw [one_sub_stationary s t hst]
    exact div_ne_zero ht hst
  intro he
  apply h
  rw [he, sub_self]

/-- Clearing only the two geometric pole denominators produces a linear numerator. -/
theorem scatteringCoefficient_eq_fraction (s t z : K)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    scatteringCoefficient s t z = (s - (s + t) * z) / (z * (1 - z)) := by
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  unfold scatteringCoefficient
  field_simp [hz0, h1z] <;> ring

/-- All solutions on the punctured domain equal the stationary coordinate. -/
theorem scatteringCoefficient_eq_zero_iff (s t z : K)
    (hst : s + t ≠ 0) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    scatteringCoefficient s t z = 0 ↔ z = stationary s t := by
  have hden : z * (1 - z) ≠ 0 :=
    mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1))
  rw [scatteringCoefficient_eq_fraction s t z hz0 hz1]
  simp only [div_eq_zero_iff, hden, or_false, sub_eq_zero]
  unfold stationary
  rw [eq_div_iff hst]
  constructor <;> intro h
  · simpa only [mul_comm] using h.symm
  · simpa only [mul_comm] using h.symm

theorem scatteringCoefficient_at_stationary (s t : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    scatteringCoefficient s t (stationary s t) = 0 := by
  exact (scatteringCoefficient_eq_zero_iff s t (stationary s t) hst
    (stationary_ne_zero s t hs hst) (stationary_ne_one s t ht hst)).mpr rfl

theorem existsUnique_stationary (s t : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    ∃! z : K, z ≠ 0 ∧ z ≠ 1 ∧ scatteringCoefficient s t z = 0 := by
  refine ⟨stationary s t, ⟨stationary_ne_zero s t hs hst,
    stationary_ne_one s t ht hst, scatteringCoefficient_at_stationary s t hs ht hst⟩, ?_⟩
  intro z hz
  exact (scatteringCoefficient_eq_zero_iff s t z hst hz.1 hz.2.1).mp hz.2.2

theorem punctureParkeTaylor_ne_zero (z : K) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    punctureParkeTaylor z ≠ 0 :=
  div_ne_zero one_ne_zero (mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1)))

theorem punctureParkeTaylor_at_stationary (s t : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    punctureParkeTaylor (stationary s t) = (s + t) ^ 2 / (s * t) := by
  unfold punctureParkeTaylor
  rw [one_sub_stationary s t hst]
  unfold stationary
  field_simp [hs, ht, hst] <;> ring

theorem hessianCoefficient_at_stationary (s t : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    hessianCoefficient s t (stationary s t) = -(s + t) ^ 3 / (s * t) := by
  unfold hessianCoefficient
  rw [one_sub_stationary s t hst]
  unfold stationary
  field_simp [hs, ht, hst] <;> ring

theorem hessianCoefficient_at_stationary_ne_zero (s t : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    hessianCoefficient s t (stationary s t) ≠ 0 := by
  rw [hessianCoefficient_at_stationary s t hs ht hst]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 hst)) (mul_ne_zero hs ht)

/-- The exact rational expression yielding the two channel denominators. -/
theorem algebraicLocalization_at_stationary (s t : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    algebraicLocalization s t (stationary s t) = 1 / s + 1 / t := by
  unfold algebraicLocalization
  rw [punctureParkeTaylor_at_stationary s t hs ht hst,
    hessianCoefficient_at_stationary s t hs ht hst]
  field_simp [hs, ht, hst] <;> ring

/-- The same value follows from any regular solution, with no solution choice left implicit. -/
theorem algebraicLocalization_at_solution (s t z : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : scatteringCoefficient s t z = 0) :
    algebraicLocalization s t z = 1 / s + 1 / t := by
  rw [(scatteringCoefficient_eq_zero_iff s t z hst hz0 hz1).mp hz]
  exact algebraicLocalization_at_stationary s t hs ht hst

/-- Explicit use of the normalized homogeneous Plücker cross-ratio. -/
theorem algebraicLocalization_normalized_plucker (s t : K)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    algebraicLocalization s t
      (Projective.ThreePointLogarithmicForms.homogeneousCrossRatio
        ![0, stationary s t, 1, 1] ![1, 1, 1, 0]) = 1 / s + 1 / t := by
  rw [Projective.ThreePointLogarithmicForms.homogeneousCrossRatio_normalized]
  exact algebraicLocalization_at_stationary s t hs ht hst

/-- At `s+t=0` with `s≠0`, there is no finite regular solution. -/
theorem no_solution_of_sum_zero (s t z : K)
    (hs : s ≠ 0) (hst : s + t = 0) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    scatteringCoefficient s t z ≠ 0 := by
  rw [scatteringCoefficient_eq_fraction s t z hz0 hz1, hst, zero_mul, sub_zero]
  exact div_ne_zero hs (mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1)))

/-- The fully degenerate zero-weight equation vanishes identically. -/
@[simp] theorem scatteringCoefficient_zero_zero (z : K) :
    scatteringCoefficient 0 0 z = 0 := by
  simp [scatteringCoefficient]

end Rational

section Differential

variable {K : Type*} [NontriviallyNormedField K]

/-- The rational Hessian is the actual derivative on the punctured domain. -/
theorem scatteringCoefficient_hasDerivAt (s t z : K)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    HasDerivAt (scatteringCoefficient s t) (hessianCoefficient s t z) z := by
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hleft := (hasDerivAt_const z s).fun_div (hasDerivAt_id z) hz0
  have hright := (hasDerivAt_const z t).fun_div ((hasDerivAt_id z).const_sub 1) h1z
  convert hleft.sub hright using 1 <;>
    dsimp [scatteringCoefficient, hessianCoefficient] <;> ring

theorem deriv_scatteringCoefficient (s t z : K)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    deriv (scatteringCoefficient s t) z = hessianCoefficient s t z :=
  (scatteringCoefficient_hasDerivAt s t z hz0 hz1).deriv

end Differential

/-- Real log-absolute potential; mathlib's real logarithm satisfies `log x = log |x|`. -/
def realLogPotential (s t z : ℝ) : ℝ := s * Real.log z + t * Real.log (1 - z)

theorem realLogPotential_hasDerivAt (s t z : ℝ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    HasDerivAt (realLogPotential s t) (scatteringCoefficient s t z) z := by
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hlog0 := (hasDerivAt_id z).log hz0
  have hlog1 := ((hasDerivAt_id z).const_sub (1 : ℝ)).log h1z
  convert (hlog0.const_mul s).add (hlog1.const_mul t) using 1 <;>
    dsimp [realLogPotential, scatteringCoefficient] <;> ring

theorem deriv_realLogPotential (s t z : ℝ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    deriv (realLogPotential s t) z = scatteringCoefficient s t z :=
  (realLogPotential_hasDerivAt s t z hz0 hz1).deriv

/-- The algebraically constructed coordinate is a stationary point of the real potential. -/
theorem realLogPotential_hasDerivAt_stationary (s t : ℝ)
    (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    HasDerivAt (realLogPotential s t) 0 (stationary s t) := by
  simpa only [scatteringCoefficient_at_stationary s t hs ht hst] using
    realLogPotential_hasDerivAt s t (stationary s t)
      (stationary_ne_zero s t hs hst) (stationary_ne_one s t ht hst)

/-- Principal-branch expression, differentiated only on the stated local branch domain.
This totalized expression does not assert a global holomorphic primitive on
all of the twice-punctured plane. -/
def complexLogPotential (s t z : ℂ) : ℂ :=
  s * Complex.log z + t * Complex.log (1 - z)

/-- Local complex potential for the scattering coefficient on the common slit domain. -/
theorem complexLogPotential_hasDerivAt (s t z : ℂ)
    (hz : z ∈ Complex.slitPlane) (h1z : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (complexLogPotential s t) (scatteringCoefficient s t z) z := by
  have hlog0 := (hasDerivAt_id z).clog hz
  have hlog1 := ((hasDerivAt_id z).const_sub (1 : ℂ)).clog h1z
  convert (hlog0.const_mul s).add (hlog1.const_mul t) using 1 <;>
    dsimp [complexLogPotential, scatteringCoefficient] <;> ring

/-- The derivative formula retains both explicit branch hypotheses. -/
theorem deriv_complexLogPotential (s t z : ℂ)
    (hz : z ∈ Complex.slitPlane) (h1z : 1 - z ∈ Complex.slitPlane) :
    deriv (complexLogPotential s t) z = scatteringCoefficient s t z :=
  (complexLogPotential_hasDerivAt s t z hz h1z).deriv

end InfoGeometry.Feynman.FourPointLogarithmicPotential
