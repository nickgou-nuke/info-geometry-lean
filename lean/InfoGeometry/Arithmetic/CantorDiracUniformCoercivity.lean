/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Arithmetic.CantorDiracOperator
import InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Uniform coercivity for a finite Cantor--Dirac operator

This bridge combines the existing finite Majorana square law with the
quadratic-form estimate in `IntertwinedSpectralLowerBound`.  The operator is
the finite sum of the actual (not assumed mutually commuting) endomorphisms
from the Cantor--Dirac owner.  A nonempty prime register gives a positive
central square coefficient; symmetry of the represented operator then yields
a uniform norm lower bound.

The symmetry hypothesis is explicit, and the conclusion is finite-register
only.  No pointwise-curvature-to-uniform-gap inference is made here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.CantorDiracUniformCoercivity

open InfoGeometry.Arithmetic.CantorDiracOperator
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private lemma norm_lower_bound_of_quadratic_coercivity
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (T : Module.End ℝ W) (c : ℝ) (hc : 0 < c)
    (hcoerc : ∀ x, c ^ 2 * inner ℝ x x ≤ inner ℝ (T x) (T x)) :
    ∀ x, c * ‖x‖ ≤ ‖T x‖ := by
  intro x
  have h := hcoerc x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have hsq : (c * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by rw [mul_pow]; exact h
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (mul_nonneg (le_of_lt hc) (norm_nonneg x)),
    Real.sqrt_sq (norm_nonneg (T x))] at hsqrt

/-- The scalar in the exact finite Cantor--Dirac square law. -/
def primeRegisterLogWeight (P : PrimeRegister) : ℝ :=
  ∑ p ∈ P.primes, Real.log (p : ℝ)

/-- Every nonempty certified prime register has strictly positive total
logarithmic weight. -/
theorem primeRegisterLogWeight_pos (P : PrimeRegister)
    (hP : P.primes.Nonempty) : 0 < primeRegisterLogWeight P := by
  classical
  unfold primeRegisterLogWeight
  apply Finset.sum_pos
  · intro p hp
    exact Real.log_pos (by
      exact_mod_cast (Nat.Prime.one_lt (P.prime_mem p hp)))
  · exact hP

/-- The finite Clifford square law, transported to the quadratic energy form
of the represented operator.  This is the Lichnerowicz-type energy identity
for this finite carrier, not a claim about a geometric curvature tensor. -/
theorem cantorDirac_energy_eq_weight_mul_norm_sq
    (P : PrimeRegister)
    (γ : ℕ → Module.End ℝ V)
    (hγ : IsMajoranaCliffordRepresentation P γ)
    (symmetric : ∀ x y,
      inner ℝ (cantorDiracOperator P γ x) y =
        inner ℝ x (cantorDiracOperator P γ y))
    (x : V) :
    inner ℝ (cantorDiracOperator P γ x) (cantorDiracOperator P γ x) =
      primeRegisterLogWeight P * inner ℝ x x := by
  let D := cantorDiracOperator (Op := Module.End ℝ V) P γ
  have hDsq : D ^ 2 = cantorDiracHamiltonian (Op := Module.End ℝ V) P :=
    cantorDirac_sq_eq_hamiltonian_of_clifford P γ hγ
  have hDx : D (D x) = primeRegisterLogWeight P • x := by
    have h := congrArg (fun T : Module.End ℝ V => T x) hDsq
    change D (D x) = _ at h
    simpa [D, cantorDiracHamiltonian, primeRegisterLogWeight,
      Finset.sum_smul] using h
  calc
    inner ℝ (D x) (D x) = inner ℝ x (D (D x)) := symmetric x (D x)
    _ = inner ℝ x (primeRegisterLogWeight P • x) := by rw [hDx]
    _ = primeRegisterLogWeight P * inner ℝ x x := by
      rw [real_inner_smul_right]

/-- A nonempty prime register and a symmetric finite Cantor--Dirac operator
give an explicit positive norm gap.  The gap is the square root of the total
logarithmic weight, and the proof proceeds through the exact operator square
law and the existing uniform quadratic-coercivity theorem. -/
theorem cantorDirac_norm_lower_bound
    (P : PrimeRegister)
    (γ : ℕ → Module.End ℝ V)
    (hγ : IsMajoranaCliffordRepresentation P γ)
    (symmetric : ∀ x y,
      inner ℝ (cantorDiracOperator P γ x) y =
        inner ℝ x (cantorDiracOperator P γ y))
    (hP : P.primes.Nonempty) :
    ∀ x, Real.sqrt (primeRegisterLogWeight P) * ‖x‖ ≤
      ‖cantorDiracOperator P γ x‖ := by
  let gap := Real.sqrt (primeRegisterLogWeight P)
  have hweight : 0 < primeRegisterLogWeight P := primeRegisterLogWeight_pos P hP
  have hgap : 0 < gap := Real.sqrt_pos.2 hweight
  have hgap_sq : gap ^ 2 = primeRegisterLogWeight P := by
    dsimp [gap]
    exact Real.sq_sqrt (le_of_lt hweight)
  have hcoercive : ∀ x,
      gap ^ 2 * inner ℝ x x ≤
        inner ℝ (cantorDiracOperator P γ x) (cantorDiracOperator P γ x) := by
    intro x
    rw [hgap_sq, cantorDirac_energy_eq_weight_mul_norm_sq P γ hγ symmetric x]
  have hnorm := norm_lower_bound_of_quadratic_coercivity
    (cantorDiracOperator P γ) gap hgap hcoercive
  simpa [gap] using hnorm

/-- A nonempty prime register makes the represented finite Cantor--Dirac
operator injective. This is the zero-mode consequence of the quantitative
norm bound, stated on the same noncommuting endomorphism carrier. -/
theorem cantorDirac_injective
    (P : PrimeRegister)
    (γ : ℕ → Module.End ℝ V)
    (hγ : IsMajoranaCliffordRepresentation P γ)
    (symmetric : ∀ x y,
      inner ℝ (cantorDiracOperator P γ x) y =
        inner ℝ x (cantorDiracOperator P γ y))
    (hP : P.primes.Nonempty) :
    Function.Injective (cantorDiracOperator (Op := Module.End ℝ V) P γ) := by
  let D : Module.End ℝ V := cantorDiracOperator (Op := Module.End ℝ V) P γ
  intro x y hxy
  have hzero : D (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hgap := cantorDirac_norm_lower_bound P γ hγ symmetric hP (x - y)
  rw [hzero, norm_zero] at hgap
  have hnorm : ‖x - y‖ = 0 := by
    have hpositive := Real.sqrt_pos.2 (primeRegisterLogWeight_pos P hP)
    have hnonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The finite Cantor--Dirac operator has no nonzero zero-mode under the
explicit symmetry and nonempty-register hypotheses. -/
theorem cantorDirac_zeroMode_trivial
    (P : PrimeRegister)
    (γ : ℕ → Module.End ℝ V)
    (hγ : IsMajoranaCliffordRepresentation P γ)
    (symmetric : ∀ x y,
      inner ℝ (cantorDiracOperator P γ x) y =
        inner ℝ x (cantorDiracOperator P γ y))
    (hP : P.primes.Nonempty) (x : V)
    (hzero : cantorDiracOperator (Op := Module.End ℝ V) P γ x = 0) : x = 0 := by
  let D : Module.End ℝ V := cantorDiracOperator (Op := Module.End ℝ V) P γ
  have hEq : D x = D 0 := by simpa [D] using hzero
  exact cantorDirac_injective P γ hγ symmetric hP hEq

/-! ## Adjoint-compatible operator carrier -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Self-adjoint generator operators make the finite Cantor--Dirac sum
self-adjoint on the continuous operator carrier.  This supplies, rather than
postulates, the symmetry premise used by the finite coercivity argument. -/
theorem cantorDirac_inner_symmetric_of_generator_selfAdjoint
    (P : PrimeRegister)
    (γ : ℕ → H →L[ℝ] H)
    (hγ : ∀ p ∈ P.primes, IsSelfAdjoint (γ p)) :
    ∀ x y,
      inner ℝ (cantorDiracOperator P γ x) y =
        inner ℝ x (cantorDiracOperator P γ y) := by
  have hD : IsSelfAdjoint (cantorDiracOperator P γ) := by
    apply cantorDirac_isSelfAdjoint
    intro p hp
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (hγ p hp).adjoint_eq
  intro x y
  have h := ContinuousLinearMap.adjoint_inner_left
    (cantorDiracOperator P γ) x y
  simpa [hD.adjoint_eq, real_inner_comm] using h.symm

/-- The exact finite Cantor--Dirac square law gives its quadratic energy
identity on the continuous operator carrier, once generator self-adjointness
has supplied symmetry. -/
theorem cantorDirac_energy_eq_weight_mul_norm_sq_of_generator_selfAdjoint
    (P : PrimeRegister)
    (γ : ℕ → H →L[ℝ] H)
    (hγ : IsMajoranaCliffordRepresentation P γ)
    (hself : ∀ p ∈ P.primes, IsSelfAdjoint (γ p))
    (x : H) :
    inner ℝ (cantorDiracOperator P γ x) (cantorDiracOperator P γ x) =
      primeRegisterLogWeight P * inner ℝ x x := by
  let D := cantorDiracOperator P γ
  have hDsq : D ^ 2 = cantorDiracHamiltonian P :=
    cantorDirac_sq_eq_hamiltonian_of_clifford P γ hγ
  have hDx : D (D x) = primeRegisterLogWeight P • x := by
    have h := congrArg (fun T : H →L[ℝ] H => T x) hDsq
    change D (D x) = _ at h
    simpa [D, cantorDiracHamiltonian, primeRegisterLogWeight,
      Finset.sum_smul] using h
  calc
    inner ℝ (D x) (D x) = inner ℝ x (D (D x)) :=
      cantorDirac_inner_symmetric_of_generator_selfAdjoint P γ hself x (D x)
    _ = inner ℝ x (primeRegisterLogWeight P • x) := by rw [hDx]
    _ = primeRegisterLogWeight P * inner ℝ x x := by
      rw [real_inner_smul_right]

/-- Self-adjoint finite Cantor--Dirac generators and a nonempty prime
register yield the explicit uniform norm bound on the Hilbert-space carrier.
The result is a finite-register coercivity statement; it does not assert a
continuum or geometric mass-gap theorem. -/
theorem cantorDirac_norm_lower_bound_of_generator_selfAdjoint
    (P : PrimeRegister)
    (γ : ℕ → H →L[ℝ] H)
    (hγ : IsMajoranaCliffordRepresentation P γ)
    (hself : ∀ p ∈ P.primes, IsSelfAdjoint (γ p))
    (hP : P.primes.Nonempty) :
    ∀ x, Real.sqrt (primeRegisterLogWeight P) * ‖x‖ ≤
      ‖cantorDiracOperator P γ x‖ := by
  let D := cantorDiracOperator P γ
  have hweight : 0 < primeRegisterLogWeight P := primeRegisterLogWeight_pos P hP
  have hgap : 0 < Real.sqrt (primeRegisterLogWeight P) := Real.sqrt_pos.2 hweight
  have hgap_sq : (Real.sqrt (primeRegisterLogWeight P)) ^ 2 =
      primeRegisterLogWeight P := Real.sq_sqrt (le_of_lt hweight)
  have hcoercive : ∀ x,
      (Real.sqrt (primeRegisterLogWeight P)) ^ 2 * inner ℝ x x ≤
        inner ℝ (D x) (D x) := by
    intro x
    rw [hgap_sq,
      cantorDirac_energy_eq_weight_mul_norm_sq_of_generator_selfAdjoint
        P γ hγ hself x]
  have hbound := norm_lower_bound_of_quadratic_coercivity
    D.toLinearMap (Real.sqrt (primeRegisterLogWeight P)) hgap hcoercive
  simpa [D] using hbound

/-- Every real eigenvalue of the self-adjoint finite Cantor--Dirac operator
is separated from zero by the same uniform coercivity constant.  This is a
spectral consequence on the represented Hilbert-space carrier; the proof
uses the operator norm estimate, rather than inferring a gap from pointwise
positivity alone. -/
theorem cantorDirac_eigenvalue_abs_lower_bound_of_generator_selfAdjoint
    (P : PrimeRegister)
    (γ : ℕ → H →L[ℝ] H)
    (hγ : IsMajoranaCliffordRepresentation P γ)
    (hself : ∀ p ∈ P.primes, IsSelfAdjoint (γ p))
    (hP : P.primes.Nonempty)
    {x : H} {μ : ℝ} (hx : x ≠ 0)
    (heigen : cantorDiracOperator P γ x = μ • x) :
    Real.sqrt (primeRegisterLogWeight P) ≤ |μ| := by
  have hbound := cantorDirac_norm_lower_bound_of_generator_selfAdjoint
    P γ hγ hself hP x
  rw [heigen, norm_smul] at hbound
  rw [Real.norm_eq_abs] at hbound
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  nlinarith

end InfoGeometry.Arithmetic.CantorDiracUniformCoercivity
