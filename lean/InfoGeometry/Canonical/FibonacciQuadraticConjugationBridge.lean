import InfoGeometry.Fibonacci.FibAnyonThm1
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The quadratic Fibonacci conjugation shadow

The map `x ↦ 1 - x` exchanges the two real roots of `x² - x - 1`.
This is the finite algebraic shadow of the nontrivial automorphism of the
quadratic Fibonacci field; no field-extension or Galois-group instance is
asserted here.
-/

namespace InfoGeometry.Canonical.FibonacciQuadraticConjugationBridge

open InfoGeometry.Fibonacci.FibAnyonThm1

def quadraticConjugate (x : ℝ) : ℝ := 1 - x

def fibonacciRootPolynomial (x : ℝ) : ℝ := x ^ 2 - x - 1

theorem quadraticConjugate_involutive (x : ℝ) :
    quadraticConjugate (quadraticConjugate x) = x := by
  simp [quadraticConjugate]

theorem quadraticConjugate_preserves_root (x : ℝ)
    (hx : fibonacciRootPolynomial x = 0) :
    fibonacciRootPolynomial (quadraticConjugate x) = 0 := by
  dsimp [fibonacciRootPolynomial, quadraticConjugate] at hx ⊢
  nlinarith

theorem quadraticConjugate_phi_eq_tau :
    quadraticConjugate φ = τ := by
  simp [quadraticConjugate, φ, τ]
  ring

theorem quadraticConjugate_tau_eq_phi :
    quadraticConjugate τ = φ := by
  simp [quadraticConjugate, φ, τ]
  ring

theorem tau_eq_one_sub_phi :
    τ = 1 - φ := by
  simp [φ, τ]
  ring

theorem phi_root : fibonacciRootPolynomial φ = 0 := by
  dsimp [fibonacciRootPolynomial]
  nlinarith [golden_identity]

theorem tau_root : fibonacciRootPolynomial τ = 0 := by
  rw [← quadraticConjugate_phi_eq_tau]
  exact quadraticConjugate_preserves_root φ phi_root

end InfoGeometry.Canonical.FibonacciQuadraticConjugationBridge
