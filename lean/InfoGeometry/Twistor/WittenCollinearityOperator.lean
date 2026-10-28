/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.WittenSpinorHelicity
import InfoGeometry.Twistor.PenrosePolynomialCCR

/-!
# The algebraic Witten collinearity differential operator

Equation (3.37) is realized by actual Mathlib partial derivations of the dotted
spinor polynomial algebra.  Schouten's identity proves that the operator
annihilates each total-momentum entry and every polynomial in those entries.
The operator itself is nonzero for a nonzero bracket and distinct third leg.

These are polynomial operator statements.  No Fourier transform, distribution,
momentum delta function, or analytic support implication is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.WittenCollinearityOperator

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.WittenSpinorHelicity
open scoped BigOperators

variable {n : ℕ}

/-- Dotted spinor coordinates, with the undotted spinors held as coefficients. -/
abbrev DottedPolynomial (n : ℕ) := MvPolynomial (Fin n × Fin 2) ℂ

/-- The four polynomial entries of the total complex momentum matrix. -/
def totalMomentumPolynomial (lambda : Fin n → Spinor2) (a d : Fin 2) :
    DottedPolynomial n :=
  ∑ i : Fin n, lambda i a • MvPolynomial.X (i, d)

theorem pderiv_totalMomentumPolynomial
    (lambda : Fin n → Spinor2) (k : Fin n) (d a e : Fin 2) :
    MvPolynomial.pderiv (k, d) (totalMomentumPolynomial lambda a e) =
      if d = e then lambda k a • (1 : DottedPolynomial n) else 0 := by
  classical
  unfold totalMomentumPolynomial
  rw [map_sum]
  by_cases h : d = e
  · subst e
    rw [if_pos rfl, Finset.sum_eq_single k]
    · rw [Derivation.map_smul, MvPolynomial.pderiv_X_self]
    · intro i hi hik
      have hidx : (i, d) ≠ (k, d) := fun heq => hik (congrArg Prod.fst heq)
      rw [Derivation.map_smul, MvPolynomial.pderiv_X_of_ne hidx, smul_zero]
    · intro hk
      exact False.elim (hk (Finset.mem_univ k))
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    have hidx : (i, e) ≠ (k, d) := fun heq => h (congrArg Prod.snd heq).symm
    rw [Derivation.map_smul, MvPolynomial.pderiv_X_of_ne hidx, smul_zero]

/-- The native derivation corresponding to Witten's `F_{ijk,d}`. -/
def collinearityDerivation (lambda : Fin n → Spinor2)
    (i j k : Fin n) (d : Fin 2) :
    Derivation ℂ (DottedPolynomial n) (DottedPolynomial n) :=
  spinorBracket (lambda i) (lambda j) • MvPolynomial.pderiv (k, d) +
    spinorBracket (lambda k) (lambda i) • MvPolynomial.pderiv (j, d) +
    spinorBracket (lambda j) (lambda k) • MvPolynomial.pderiv (i, d)

theorem collinearityDerivation_momentum
    (lambda : Fin n → Spinor2) (i j k : Fin n) (d a e : Fin 2) :
    collinearityDerivation lambda i j k d (totalMomentumPolynomial lambda a e) = 0 := by
  have hSchouten :
      spinorBracket (lambda i) (lambda j) * lambda k a +
          spinorBracket (lambda k) (lambda i) * lambda j a +
          spinorBracket (lambda j) (lambda k) * lambda i a = 0 := by
    have h := congrArg (fun v : Spinor2 => v a)
      (spinorBracket_schouten (lambda i) (lambda j) (lambda k))
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
    linear_combination h
  simp only [collinearityDerivation, Derivation.add_apply,
    Derivation.smul_apply, pderiv_totalMomentumPolynomial]
  by_cases h : d = e
  · simp only [if_pos h, smul_smul, ← add_smul, hSchouten, zero_smul]
  · simp [h]

/-- Every polynomial function of the four total-momentum entries is killed.
This extends the coordinate identity by the actual derivation Leibniz law. -/
theorem collinearityDerivation_momentum_polynomial
    (lambda : Fin n → Spinor2) (i j k : Fin n) (d : Fin 2)
    (P : MvPolynomial (Fin 2 × Fin 2) ℂ) :
    collinearityDerivation lambda i j k d
      (MvPolynomial.aeval (fun a => totalMomentumPolynomial lambda a.1 a.2) P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | mul_X P a hP =>
      simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz,
        hP, collinearityDerivation_momentum, smul_zero, zero_add]

/-- Evaluation on the third leg excludes a globally zero-operator proxy. -/
theorem collinearityDerivation_ne_zero
    (lambda : Fin n → Spinor2) (i j k : Fin n) (d : Fin 2)
    (hki : k ≠ i) (hkj : k ≠ j)
    (hbracket : spinorBracket (lambda i) (lambda j) ≠ 0) :
    collinearityDerivation lambda i j k d ≠ 0 := by
  intro hzero
  have h := Derivation.congr_fun hzero (MvPolynomial.X (k, d))
  have hscalar : spinorBracket (lambda i) (lambda j) • (1 : DottedPolynomial n) = 0 := by
    simpa [collinearityDerivation, MvPolynomial.pderiv_X,
      Pi.single_apply, Prod.mk.injEq, hki, hkj, Ne.symm hki, Ne.symm hkj] using h
  have hc := congrArg MvPolynomial.constantCoeff hscalar
  exact hbracket (by simpa using hc)

end InfoGeometry.Twistor.WittenCollinearityOperator
