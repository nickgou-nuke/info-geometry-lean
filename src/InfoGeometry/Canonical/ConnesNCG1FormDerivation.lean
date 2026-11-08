import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.ConnesNCG1FormDerivation

/-!
# Connes NCG 1-Form Exterior Derivative & Leibniz Rule

This module formalizes Alain Connes' Non-Commutative Geometry (NCG) 1-form exterior derivative
$$d_D(b) = [D, b] = D b - b D$$
and non-commutative 1-forms $\omega = a \cdot d_D(b)$ in a spectral triple:

Proved Theorems:
1. Dirac Commutator Leibniz Rule: $d_D(a b) = a \cdot d_D(b) + d_D(a) \cdot b$
2. Identity Derivative Annihilation: $d_D(1) = 0$
3. Zero Coefficient 1-Form Annihilation: $\text{eval}_D(0 \cdot d_D(b)) = 0$
4. Identity Base 1-Form Annihilation: $\text{eval}_D(a \cdot d_D(1)) = 0$.
-/

variable {A : Type*} [Ring A]

/-- Dirac commutator derivation d_D(a) = D a - a D. -/
def diracCommutator (D a : A) : A :=
  D * a - a * D

/-- **Theorem**: Dirac Commutator Leibniz Rule:
    d_D(a * b) = a * d_D(b) + d_D(a) * b. -/
theorem dirac_commutator_leibniz (D a b : A) :
    diracCommutator D (a * b) = a * diracCommutator D b + diracCommutator D a * b := by
  dsimp [diracCommutator]
  noncomm_ring

/-- **Theorem**: Dirac Commutator Value at Identity 1: d_D(1) = 0. -/
theorem dirac_commutator_one (D : A) :
    diracCommutator D 1 = 0 := by
  dsimp [diracCommutator]
  simp

/-- Structure representing a non-commutative 1-form ω = a * d_D(b). -/
structure NC1Form (A : Type*) [Ring A] where
  coeff : A
  base : A

/-- Valuation of NC 1-form ω = a * d_D(b) under Dirac operator D. -/
def evalNC1Form (D : A) (ω : NC1Form A) : A :=
  ω.coeff * diracCommutator D ω.base

/-- **Theorem**: Zero coefficient 1-form evaluates to 0. -/
theorem evalNC1Form_zero_coeff (D : A) (b : A) :
    evalNC1Form D ⟨0, b⟩ = 0 := by
  dsimp [evalNC1Form]
  simp

/-- **Theorem**: Identity base 1-form evaluates to 0 (d_D(1) = 0). -/
theorem evalNC1Form_one_base (D : A) (a : A) :
    evalNC1Form D ⟨a, 1⟩ = 0 := by
  dsimp [evalNC1Form]
  rw [dirac_commutator_one, mul_zero]

end InfoGeometry.Canonical.ConnesNCG1FormDerivation
