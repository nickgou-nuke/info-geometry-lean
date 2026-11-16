/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.LinearMap.Star
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic

/-! # Antilinear negative squares and real averaging defects

The square relation is an explicit hypothesis. Neither antiunitarity nor a
spacetime interpretation is inferred from conjugate linearity. The averaging
operator is formed in a real endomorphism algebra.
-/

noncomputable section

namespace InfoGeometry.Algebra.AntilinearSquare

section ConjugateLinear

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Conjugate linearity reverses the imaginary scalar. -/
theorem map_I_smul (T : V →ₗ⋆[ℂ] V) (v : V) :
    T (Complex.I • v) = -Complex.I • T v := by
  simpa using map_smulₛₗ T Complex.I v

/-- A conjugate-linear map with square minus the identity has no nonzero
complex eigenvectors. No norm or finite-dimensional hypothesis is needed. -/
theorem eq_zero_of_eigenvector (T : V →ₗ⋆[ℂ] V)
    (hT : ∀ v, T (T v) = -v) {v : V} {c : ℂ}
    (hv : T v = c • v) : v = 0 := by
  have hnorm : star c * c = (Complex.normSq c : ℂ) := by
    simpa only [Complex.star_def] using
      (Complex.normSq_eq_conj_mul_self (z := c)).symm
  have hs : (Complex.normSq c : ℂ) • v = -v := by
    calc
      (Complex.normSq c : ℂ) • v = (star c * c) • v := by rw [hnorm]
      _ = T (T v) := by rw [hv, map_smulₛₗ, hv, smul_smul]
      _ = -v := hT v
  have hz : ((Complex.normSq c : ℂ) + 1) • v = 0 := by
    rw [add_smul, one_smul, hs, neg_add_cancel]
  have hc : (Complex.normSq c : ℂ) + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re,
      Complex.zero_re] at hre
    have hnonneg := Complex.normSq_nonneg c
    linarith
  exact (smul_eq_zero.mp hz).resolve_left hc

/-- The restriction of a conjugate-linear operator to real scalars. -/
def realLinearMap (T : V →ₗ⋆[ℂ] V) : Module.End ℝ V where
  toFun := T
  map_add' := map_add T
  map_smul' r v := by
    simpa using map_smulₛₗ T (r : ℂ) v

@[simp] theorem realLinearMap_apply (T : V →ₗ⋆[ℂ] V) (v : V) :
    realLinearMap T v = T v := rfl

/-- The real restriction retains the negative-square relation. -/
theorem realLinearMap_mul_self (T : V →ₗ⋆[ℂ] V)
    (hT : ∀ v, T (T v) = -v) :
    realLinearMap T * realLinearMap T = -1 := by
  ext v
  exact hT v

end ConjugateLinear

section RealAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The averaging defect in an arbitrary associative real algebra. No
commutativity of the algebra is required. -/
theorem half_average_defect (t : A) :
    ((1 / 2 : ℝ) • (1 + t)) * ((1 / 2 : ℝ) • (1 + t)) -
      (1 / 2 : ℝ) • (1 + t) = (1 / 4 : ℝ) • (t * t - 1) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul,
    add_mul, mul_add, one_mul, mul_one]
  module

/-- Averaging a negative-square operator is not a projection: its exact
idempotence defect is minus one half of the identity. -/
theorem half_average_defect_of_negative_square (t : A) (ht : t * t = -1) :
    ((1 / 2 : ℝ) • (1 + t)) * ((1 / 2 : ℝ) • (1 + t)) -
      (1 / 2 : ℝ) • (1 + t) = -(1 / 2 : ℝ) • (1 : A) := by
  rw [half_average_defect, ht]
  module

/-- Nontriviality is necessary when concluding failure of idempotence. -/
theorem half_average_not_idempotent [Nontrivial A] (t : A) (ht : t * t = -1) :
    ((1 / 2 : ℝ) • (1 + t)) * ((1 / 2 : ℝ) • (1 + t)) ≠
      (1 / 2 : ℝ) • (1 + t) := by
  intro h
  have hd := half_average_defect_of_negative_square t ht
  rw [h, sub_self] at hd
  have hzero : (1 : A) = 0 :=
    (smul_eq_zero.mp hd.symm).resolve_left (by norm_num)
  exact one_ne_zero hzero

end RealAlgebra

end InfoGeometry.Algebra.AntilinearSquare

end
