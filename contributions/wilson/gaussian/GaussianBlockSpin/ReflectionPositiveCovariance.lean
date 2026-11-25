/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Reflection-positive covariance transport

For real finite covariance matrices, the reflected form on selected tests is
`Uᵀ * Θ * C * U`. Covariance transport `N + Q * C * Qᵀ` preserves positivity
of this form when the fine form and the noise form are positive, reflections
intertwine with `Q`, and `Qᵀ` pulls coarse selected tests back to fine selected
tests.

The algebraic identity does not need involutivity or symmetry of `Θ`; genuine
time reflections may be instantiated afterwards. Positivity of the compressed
forms is a separate hypothesis, not a consequence of commutation.

A real two-slice example proves that a symmetric reflection and a commuting
positive-definite covariance need not give a positive reflected form. The
failure persists after adding that covariance as noise to a reflection-positive
identity covariance with identity blocking.

This file proves finite covariance identities and matrix positivity. It does
not construct a Gaussian measure or prove full Osterwalder--Schrader positivity
for nonlinear observables, a continuum limit, or Lorentzian reconstruction.
-/

@[expose] public section

noncomputable section

open Matrix
open scoped Matrix

namespace GaussianBlockSpin.ReflectionPositiveCovariance

variable {n m p q : Type*} [Fintype n] [Fintype m] [Fintype p]

/-- The reflected coarse form splits into the reflected noise form and an
exact pullback of the reflected fine form. `hTests` records preservation of the
chosen positive-time test spaces by the dual blocking map. -/
theorem reflected_covariance_transport_eq
    (θf : Matrix n n ℝ) (θc : Matrix m m ℝ)
    (C : Matrix n n ℝ) (N : Matrix m m ℝ) (Q : Matrix m n ℝ)
    (Uf : Matrix n p ℝ) (Uc : Matrix m q ℝ) (B : Matrix p q ℝ)
    (hReflection : θc * Q = Q * θf)
    (hTests : Qᵀ * Uc = Uf * B) :
    Ucᵀ * θc * (N + Q * C * Qᵀ) * Uc =
      Ucᵀ * θc * N * Uc + Bᵀ * (Ufᵀ * θf * C * Uf) * B := by
  have hLeft : Ucᵀ * θc * Q = Bᵀ * Ufᵀ * θf := by
    calc
      Ucᵀ * θc * Q = Ucᵀ * (θc * Q) := Matrix.mul_assoc _ _ _
      _ = Ucᵀ * (Q * θf) := by rw [hReflection]
      _ = (Qᵀ * Uc)ᵀ * θf := by
        simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      _ = Bᵀ * Ufᵀ * θf := by rw [hTests, transpose_mul]
  calc
    Ucᵀ * θc * (N + Q * C * Qᵀ) * Uc =
        Ucᵀ * θc * N * Uc + (Ucᵀ * θc * Q) * C * (Qᵀ * Uc) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = Ucᵀ * θc * N * Uc + (Bᵀ * Ufᵀ * θf) * C * (Uf * B) := by
      rw [hLeft, hTests]
    _ = Ucᵀ * θc * N * Uc + Bᵀ * (Ufᵀ * θf * C * Uf) * B := by
      simp only [Matrix.mul_assoc]

/-- Reflection positivity of the fine covariance and of the added noise
implies reflection positivity of the transported covariance, under reflection
intertwining and preservation of the selected test spaces. -/
theorem reflected_covariance_posSemidef [Finite q]
    (θf : Matrix n n ℝ) (θc : Matrix m m ℝ)
    (C : Matrix n n ℝ) (N : Matrix m m ℝ) (Q : Matrix m n ℝ)
    (Uf : Matrix n p ℝ) (Uc : Matrix m q ℝ) (B : Matrix p q ℝ)
    (hReflection : θc * Q = Q * θf)
    (hTests : Qᵀ * Uc = Uf * B)
    (hFine : (Ufᵀ * θf * C * Uf).PosSemidef)
    (hNoise : (Ucᵀ * θc * N * Uc).PosSemidef) :
    (Ucᵀ * θc * (N + Q * C * Qᵀ) * Uc).PosSemidef := by
  rw [reflected_covariance_transport_eq θf θc C N Q Uf Uc B hReflection hTests]
  apply hNoise.add
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    hFine.conjTranspose_mul_mul_same B

namespace Counterexample

/-- Reflection exchanging the positive and negative time coordinates. -/
def reflection : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![1, 0]]

/-- The inclusion of the first coordinate as the positive-time test space. -/
def positiveTime : Matrix (Fin 2) Unit ℝ := fun i _ => if i = 0 then 1 else 0

/-- The coordinate projection onto the selected positive-time test space. -/
def positiveTimeProjection : Matrix (Fin 2) (Fin 2) ℝ := positiveTime * positiveTimeᵀ

/-- A strictly positive covariance with a negative cross-reflection pairing. -/
def noise : Matrix (Fin 2) (Fin 2) ℝ := ![![1, -(1 / 2)], ![-(1 / 2), 1]]

theorem reflection_transpose : reflectionᵀ = reflection := by
  ext i j
  simp only [transpose_apply]
  fin_cases i <;> fin_cases j <;> norm_num [reflection]

theorem reflection_sq : reflection * reflection = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> norm_num [reflection]

/-- Reflection exchanges the chosen half with the other half, so it does not
commute with the projection onto the positive-time test space. -/
theorem reflection_not_commute_positiveTime_projection :
    reflection * positiveTimeProjection ≠ positiveTimeProjection * reflection := by
  intro h
  have hEntry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp only [positiveTimeProjection, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two, Fintype.sum_unique] at hEntry
  norm_num [positiveTime, reflection] at hEntry

/-- The counterexample noise is genuinely positive definite. -/
theorem noise_posDef : noise.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply]
    fin_cases i <;> fin_cases j <;> norm_num [noise]
  · intro x hx
    have hNorm : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      by_cases hx0 : x 0 = 0
      · have hx1 : x 1 ≠ 0 := by
          intro hx1
          apply hx
          ext i
          fin_cases i <;> simp [hx0, hx1]
        simpa only [hx0, zero_pow (by decide : 2 ≠ 0), zero_add] using
          sq_pos_of_ne_zero hx1
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx0) (sq_nonneg _)
    have hDifference := sq_nonneg (x 0 - x 1)
    simp only [dotProduct, mulVec, Fin.sum_univ_two, star_trivial]
    dsimp [noise]
    nlinarith

theorem noise_commutes : reflection * noise = noise * reflection := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num [reflection, noise]

/-- Commutation and ordinary strict positivity do not imply reflected positivity. -/
theorem noise_not_reflection_positive :
    ¬ (positiveTimeᵀ * reflection * noise * positiveTime).PosSemidef := by
  intro h
  have hEntry := h.diag_nonneg (i := ())
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] at hEntry
  norm_num [positiveTime, reflection, noise] at hEntry

/-- The identity fine covariance has a zero, hence positive, reflected form on
the selected positive-time half. -/
theorem identity_reflection_positive :
    (positiveTimeᵀ * reflection * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
      positiveTime).PosSemidef := by
  have hZero :
      positiveTimeᵀ * reflection * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
        positiveTime = 0 := by
    ext i j
    simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    norm_num [positiveTime, reflection]
  rw [hZero]
  exact Matrix.PosSemidef.zero

/-- Adding the counterexample noise to the identity still gives a strictly
positive ordinary covariance. -/
theorem identity_add_noise_posDef :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) + noise).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_one.add noise_posDef.isHermitian)
  intro x hx
  have hOne : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := Matrix.PosSemidef.one
  have hIdentity := hOne.dotProduct_mulVec_nonneg x
  have hNoise := noise_posDef.dotProduct_mulVec_pos hx
  simpa only [Matrix.add_mulVec, dotProduct_add] using
    add_pos_of_nonneg_of_pos hIdentity hNoise

theorem identity_add_noise_commutes :
    reflection * ((1 : Matrix (Fin 2) (Fin 2) ℝ) + noise) =
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) + noise) * reflection := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    noise_commutes]

/-- With reflection-positive fine covariance `1` and identity blocking, a
commuting positive noise can destroy reflected positivity. -/
theorem identity_add_noise_not_reflection_positive :
    ¬ (positiveTimeᵀ * reflection *
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) + noise) * positiveTime).PosSemidef := by
  intro h
  have hEntry := h.diag_nonneg (i := ())
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.one_apply, Fin.sum_univ_two] at hEntry
  norm_num [positiveTime, reflection, noise] at hEntry

end Counterexample

end GaussianBlockSpin.ReflectionPositiveCovariance
