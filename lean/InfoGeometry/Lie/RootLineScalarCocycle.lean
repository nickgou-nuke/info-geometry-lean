import InfoGeometry.Lie.CanonicalZornMathlibRootSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

theorem real_scalar_eq_one_or_neg_one_of_mul_self_eq_one
    (c : ℝ) (hc : c * c = 1) : c = 1 ∨ c = -1 := by
  have h : (c - 1) * (c + 1) = 0 := by
    calc
      (c - 1) * (c + 1) = c * c - 1 := by ring
      _ = 0 := by rw [hc]; norm_num
  rcases mul_eq_zero.mp h with h₁ | h₂
  · left
    linarith
  · right
    linarith

theorem LinearEquiv.rootLine_scalar_mul_self_eq_one_of_quadratic
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    (T : L ≃ₗ[ℝ] L) (v : L) (c : ℝ) (q : L → ℝ)
    (hT : T v = c • v)
    (hq : ∀ a x, q (a • x) = a * a * q x)
    (hpres : q (T v) = q v) (hqv : q v ≠ 0) :
    c * c = 1 := by
  have h := hpres
  rw [hT, hq] at h
  have hscaled : (c * c - 1) * q v = 0 := by
    calc
      (c * c - 1) * q v = c * c * q v - q v := by ring
      _ = 0 := by linarith
  have : c * c - 1 = 0 := (mul_eq_zero.mp hscaled).resolve_right hqv
  linarith
/-!
# Composition of scalars on a one-dimensional root line

This isolates the cocycle algebra from Weyl-specific normalization.  Once two
linear actions have been reduced to scalar action on the same root line, their
composition has the product scalar.
-/

theorem LinearMap.rootLine_scalar_comp
    {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L]
    (T U : L →ₗ[R] L) (v : L) (c d : R)
    (hT : T v = c • v) (hU : U v = d • v) :
    (T.comp U) v = (c * d) • v := by
  calc
    (T.comp U) v = T (d • v) := by simp [LinearMap.comp_apply, hU]
    _ = d • T v := by rw [T.map_smul]
    _ = d • (c • v) := by rw [hT]
    _ = (c * d) • v := by rw [smul_smul, mul_comm]

theorem LinearEquiv.rootLine_scalar_symm
    {R L : Type*} [DivisionRing R] [AddCommGroup L] [Module R L]
    (T : L ≃ₗ[R] L) (v : L) (c : R) (hc : c ≠ 0)
    (hT : T v = c • v) :
    T.symm v = c⁻¹ • v := by
  apply T.injective
  rw [T.apply_symm_apply, T.map_smul, hT]
  rw [inv_smul_smul₀ hc]

theorem LinearEquiv.rootLine_scalar_ne_zero
    {R L : Type*} [DivisionRing R] [AddCommGroup L] [Module R L]
    (T : L ≃ₗ[R] L) (v : L) (c : R) (hv : v ≠ 0)
    (hT : T v = c • v) :
    c ≠ 0 := by
  intro hc
  rw [hc, zero_smul] at hT
  apply hv
  apply T.injective
  simpa using hT

theorem LinearMap.rootLine_scalar_comp_between
    {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L]
    (T U : L →ₗ[R] L) (v w z : L) (c d : R)
    (hT : T w = c • z) (hU : U v = d • w) :
    (T.comp U) v = (c * d) • z := by
  calc
    (T.comp U) v = T (d • w) := by simp [LinearMap.comp_apply, hU]
    _ = d • T w := by rw [T.map_smul]
    _ = d • (c • z) := by rw [hT]
    _ = (c * d) • z := by rw [smul_smul, mul_comm]
