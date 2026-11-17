/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.ConstrainedBilinearProjection
import InfoGeometry.Canonical.KuboMoriBogoliubovPositiveForm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Constrained real BKM forces and noncommutation

The Gram projection removes a linear combination of `1` and `H`. It therefore
preserves the full ordered commutator with `H`. Noncommutation forces a
nonzero residual and, for the existing faithful real spectral BKM form, a
strictly positive quadratic response.

The converse is false: a commuting direction need not lie in `span {1, H}`.
A three-level example proves this on the same full real matrix carrier.
For the spectral surprisal, the normal equations and response are pointwise
identities. No state evolution, positivity-preserving trajectory, global
convergence, or identification of the normalization coefficient with a Gibbs
log-partition function is supplied by these identities.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealBKMConstrainedForce

open ConstrainedBilinearProjection

section Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Removing the two constraint directions preserves the energy commutator.
No commutativity of the ambient algebra or Gram nondegeneracy is needed. -/
theorem projection_commutator (B : LinearMap.BilinForm ℝ A) (H x : A) :
    projection B 1 H x * H - H * projection B 1 H x = x * H - H * x := by
  simp only [projection_eq_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one]
  abel

/-- A zero projected force can occur only in a direction commuting with the energy. -/
theorem commute_of_projection_zero (B : LinearMap.BilinForm ℝ A) (H x : A)
    (hx : projection B 1 H x = 0) : Commute x H := by
  have hcomm := projection_commutator B H x
  rw [hx, zero_mul, mul_zero, sub_self] at hcomm
  exact sub_eq_zero.mp hcomm.symm

/-- A positive real form turns the algebraic commutator obstruction into
strictly positive constrained response. -/
theorem projectedForm_pos_of_not_commute
    (B : LinearMap.BilinForm ℝ A) (H x : A)
    (hpos : ∀ y : A, y ≠ 0 → 0 < B y y) (hx : ¬ Commute x H) :
    0 < projectedForm B 1 H x x := by
  apply hpos
  intro hz
  exact hx (commute_of_projection_zero B H x hz)

end Algebra

open KuboMoriBogoliubov

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual finite spectral surprisal, defined over the real matrix algebra. -/
def spectralSurprisal (rho : FaithfulDensityState n) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => -Real.log (rho.eigenvalues i))

/-- The state-dependent Gram residual of the surprisal. -/
def constrainedSurprisal (rho : FaithfulDensityState n) (H : Matrix n n ℝ) :
    Matrix n n ℝ :=
  projection rho.bkmBilinForm 1 H (spectralSurprisal rho)

/-- These are the actual residual coefficients and both normal equations.
The denominator follows from faithful BKM positivity and nonscalar energy. -/
theorem constrainedSurprisal_normal_decomposition
    (rho : FaithfulDensityState n) (H : Matrix n n ℝ)
    (hH : H ∉ Submodule.span ℝ ({1} : Set (Matrix n n ℝ))) :
    constrainedSurprisal rho H = spectralSurprisal rho -
        identityCoefficient rho.bkmBilinForm 1 H (spectralSurprisal rho) • 1 -
        energyCoefficient rho.bkmBilinForm 1 H (spectralSurprisal rho) • H ∧
      rho.bkmBilinForm 1 (constrainedSurprisal rho H) = 0 ∧
      rho.bkmBilinForm H (constrainedSurprisal rho H) = 0 := by
  have hden := (energy_denominator_pos rho.bkmBilinForm 1 H
    rho.bkmBilinForm_pos rho.bkmBilinForm_one_one hH).ne'
  exact ⟨projection_eq_sub rho.bkmBilinForm 1 H (spectralSurprisal rho),
    projection_pairing_unit rho.bkmBilinForm 1 H
      rho.bkmBilinForm_one_one (spectralSurprisal rho),
    projection_pairing_energy rho.bkmBilinForm 1 H
      rho.bkmBilinForm_one_one hden (spectralSurprisal rho)⟩

/-- Noncommuting surprisal and energy give strictly positive constrained BKM response. -/
theorem constrainedSurprisal_production_pos_of_not_commute
    (rho : FaithfulDensityState n) (H : Matrix n n ℝ)
    (hH : ¬ Commute (spectralSurprisal rho) H) :
    0 < rho.bkmBilinForm (constrainedSurprisal rho H) (constrainedSurprisal rho H) :=
  projectedForm_pos_of_not_commute rho.bkmBilinForm H (spectralSurprisal rho)
    rho.bkmBilinForm_pos hH

/-- The same-state surprisal commutes with the density at every faithful state,
independently of any Gibbs equilibrium condition. -/
theorem spectralSurprisal_commutes_density (rho : FaithfulDensityState n) :
    Commute (spectralSurprisal rho) (Matrix.diagonal rho.eigenvalues) := by
  change Matrix.diagonal (fun i => -Real.log (rho.eigenvalues i)) *
      Matrix.diagonal rho.eigenvalues =
    Matrix.diagonal rho.eigenvalues *
      Matrix.diagonal (fun i => -Real.log (rho.eigenvalues i))
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

section CommutingCounterexample

private theorem three_level_affine_scalar_contradiction (r s : ℝ)
    (h0 : r = 1) (h1 : r + s = 0) (h2 : r + s * 2 = 0) : False := by
  linarith

/-- Three distinct energy levels in the full real matrix algebra. -/
def threeLevelEnergy : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![0, 1, 2]

/-- This diagonal direction commutes with the energy but is not affine in it. -/
def threeLevelDirection : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1, 0, 0]

theorem threeLevelEnergy_not_scalar :
    threeLevelEnergy ∉
      Submodule.span ℝ ({1} : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  intro h
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) hr
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) hr
  norm_num [threeLevelEnergy, Matrix.smul_apply, Matrix.one_apply] at h0 h1
  exact zero_ne_one (h0.symm.trans h1)

theorem threeLevelDirection_not_constraints :
    threeLevelDirection ∉ constraintSubmodule (1 : Matrix (Fin 3) (Fin 3) ℝ)
      threeLevelEnergy := by
  intro h
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp h
  have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) hrs
  have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) hrs
  have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) hrs
  norm_num [threeLevelEnergy, threeLevelDirection, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply] at h0 h1 h2
  exact three_level_affine_scalar_contradiction r s h0 h1 h2

/-- Commutation does not characterize the null space of constrained BKM response.
This example works for every faithful spectral density on three levels. -/
theorem commuting_positive_response (rho : FaithfulDensityState (Fin 3)) :
    Commute threeLevelDirection threeLevelEnergy ∧
      0 < projectedForm rho.bkmBilinForm 1 threeLevelEnergy
        threeLevelDirection threeLevelDirection := by
  constructor
  · change Matrix.diagonal ![(1 : ℝ), 0, 0] * Matrix.diagonal ![0, 1, 2] =
      Matrix.diagonal ![0, 1, 2] * Matrix.diagonal ![(1 : ℝ), 0, 0]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · have hden := (energy_denominator_pos rho.bkmBilinForm 1 threeLevelEnergy
      rho.bkmBilinForm_pos rho.bkmBilinForm_one_one threeLevelEnergy_not_scalar).ne'
    exact (projectedForm_self_pos_iff rho.bkmBilinForm 1 threeLevelEnergy
      threeLevelDirection rho.bkmBilinForm_pos rho.bkmBilinForm_one_one hden).mpr
        threeLevelDirection_not_constraints

end CommutingCounterexample

end InfoGeometry.Thermo.RealBKMConstrainedForce
