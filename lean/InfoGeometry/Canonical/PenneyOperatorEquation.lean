/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PenneyOctonionIsospin
import Mathlib.Tactic

/-!
# Penney: operator ordering, nonassociative defects, and coupled equations

This file isolates the formal algebraic content of sections 4, 6–9 of
Penney (1971), without promoting it to a spacetime PDE or a Lorentz theorem.
No associativity is imposed on AlbertStep multiplication.
-/

namespace InfoGeometry.Canonical.PenneyOperatorEquation

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.PenneyOctonionIsospin

section OctonionicDefect

variable {F A : Type*} [CommRing F] [Ring A] [Algebra F A] [StarRing A]

/-- The failure of the doubled product to associate is retained explicitly. -/
def associatorDefect (γ : F)
    (x y z : AlbertStep F A γ) : AlbertStep F A γ :=
  AlbertStep.mul x (AlbertStep.mul y z) -
    AlbertStep.mul (AlbertStep.mul x y) z

/-- Exact condition under which left factorization of an octonion wave equation is valid. -/
theorem left_factorization_iff_defect_zero (γ : F)
    (x y z : AlbertStep F A γ) :
    AlbertStep.mul x (AlbertStep.mul y z) =
      AlbertStep.mul (AlbertStep.mul x y) z ↔
    associatorDefect γ x y z = 0 := by
  simp only [associatorDefect, AlbertStep.ext_iff, AlbertStep.sub_p,
    AlbertStep.sub_q, AlbertStep.zero_p, AlbertStep.zero_q, sub_eq_zero]

/-- Multiplying a first-order solution by an operator produces a second-order
    solution when its specific associator vanishes. -/
theorem first_order_implies_factored_second_order (γ : F)
    (x y z : AlbertStep F A γ)
    (hfirst : AlbertStep.mul y z = 0)
    (hassoc : associatorDefect γ x y z = 0) :
    AlbertStep.mul (AlbertStep.mul x y) z = 0 := by
  have heq := (left_factorization_iff_defect_zero γ x y z).2 hassoc
  rw [hfirst] at heq
  have hzero : AlbertStep.mul x (0 : AlbertStep F A γ) = 0 := by
    apply AlbertStep.ext <;> simp [AlbertStep.mul]
  exact heq.symm.trans hzero

end OctonionicDefect

section OperatorCoupling

variable {A : Type*} [Ring A]

/-- The coupled first-order equations imply second-order equations whenever
    the mass operator commutes with both kinetic factors. -/
theorem coupled_second_order {p q m χ φ : A}
    (h : Coupled p q m χ φ)
    (hpm : p * m = m * p)
    (hqm : q * m = m * q) :
    (q * p) * χ = (m * m) * χ ∧
    (p * q) * φ = (m * m) * φ := by
  rcases h with ⟨h₁, h₂⟩
  constructor
  · calc
      (q * p) * χ = q * (p * χ) := mul_assoc _ _ _
      _ = q * (m * φ) := by rw [h₁]
      _ = m * (q * φ) := by rw [← mul_assoc, hqm, mul_assoc]
      _ = m * (m * χ) := by rw [h₂]
      _ = (m * m) * χ := (mul_assoc _ _ _).symm
  · calc
      (p * q) * φ = p * (q * φ) := mul_assoc _ _ _
      _ = p * (m * χ) := by rw [h₂]
      _ = m * (p * χ) := by rw [← mul_assoc, hpm, mul_assoc]
      _ = m * (m * φ) := by rw [h₁]
      _ = (m * m) * φ := (mul_assoc _ _ _).symm

/-- A supplied invertible transformation preserves the coupled system by
    left conjugation. This is algebraic covariance, not Lorentz covariance. -/
theorem coupled_conjugation {p q m χ φ s t : A}
    (h : Coupled p q m χ φ)
    (hts : t * s = 1) :
    Coupled (s * p * t) (s * q * t) (s * m * t)
      (s * χ * t) (s * φ * t) := by
  have hconj (a b : A) :
      (s * a * t) * (s * b * t) = s * (a * b) * t := by
    calc
      (s * a * t) * (s * b * t) = s * (a * (t * s) * b) * t := by
        simp only [mul_assoc]
      _ = s * (a * b) * t := by rw [hts, mul_one]
  rcases h with ⟨h₁, h₂⟩
  exact ⟨by rw [hconj, hconj, h₁],
         by rw [hconj, hconj, h₂]⟩

/-- A shifted pair of noncommuting kinetic operators retains both cross
    terms and their ordering. -/
theorem minimally_coupled_product (p q a b : A) :
    (p - a) * (q - b) =
      p * q - p * b - a * q + a * b := by
  noncomm_ring

/-- Antisymmetric kinetic products acquire an explicit field-strength
    commutator after minimal substitution. -/
theorem minimally_coupled_commutator (p q a b : A) :
    (p - a) * (q - b) - (q - b) * (p - a) =
      (p * q - q * p) - (p * b - b * p) -
      (a * q - q * a) + (a * b - b * a) := by
  noncomm_ring

end OperatorCoupling

end InfoGeometry.Canonical.PenneyOperatorEquation
