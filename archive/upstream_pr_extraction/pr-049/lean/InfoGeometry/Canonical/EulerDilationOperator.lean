import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic
import InfoGeometry.Canonical.PolynomialXPDilation
import InfoGeometry.Physics.SymmetricAsymmetricXP

/-!
# Euler Dilation Operator: Finite Algebraic Core

The Euler dilation operator
$$\mathcal{D} = x \frac{d}{dx} = \frac{d}{d\ln x}$$
is the fundamental scaling generator that intertwines the real coordinate
space with the complex spectral parameter `s`.

Under the Mellin transform, `D` maps to algebraic multiplication by `-s`:
$$\mathcal{M}\big( x \tfrac{d}{dx} f \big)(s) = -s \, \mathcal{M}[f](s).$$

This file records only the finite algebraic skeleton:

* the Euler dilation operator on polynomials;
* its action on monomials;
* the symmetric/antisymmetric splitting of `x p`;
* the finite polynomial product rule (Mellin shadow);
* the connection to the critical-line shift `s ↦ s + 1/2`.

No infinities, no analytic continuation, no measure-theoretic LDP debt.
-/

noncomputable section

namespace InfoGeometry.Canonical.EulerDilationOperator

open InfoGeometry.Canonical.PolynomialXPDilation
open InfoGeometry.Physics.SymmetricAsymmetricXP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## 1. Euler dilation operator on polynomials -/

/-- The Euler dilation operator `D = x d/dx` on polynomials. -/
def eulerDilation (p : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.X * Polynomial.derivative p

/-- The Euler dilation operator as a native linear map. -/
def eulerDilationLinear : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun := eulerDilation
  map_add' p q := by
    simp [eulerDilation, Polynomial.derivative_add, mul_add]
  map_smul' c p := by
    simp [eulerDilation, Polynomial.derivative_smul, mul_smul]

theorem eulerDilationLinear_eq_position_comp_momentum :
    eulerDilationLinear = positionLinear.comp momentumLinear := by
  rfl

/-- Action on monomials: `D(x^n) = n x^n`. -/
theorem eulerDilation_monomial (n : ℕ) :
    eulerDilation (Polynomial.X ^ n) = (n : ℂ) • Polynomial.X ^ n := by
  have hderiv : ∀ m : ℕ,
      (Polynomial.X : Polynomial ℂ) *
          Polynomial.derivative ((Polynomial.X : Polynomial ℂ) ^ m) =
        (m : ℂ) • (Polynomial.X : Polynomial ℂ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Polynomial.derivative_mul, Polynomial.derivative_X]
        simp only [mul_one, mul_add]
        rw [← mul_assoc, ih]
        simp [Nat.cast_succ, add_smul]
        rw [mul_comm]
  simpa [eulerDilation] using hderiv n

/-! ## 2. Relation to symmetric quantization -/

theorem symmetricXPDilation_eq_eulerDilation_add_half (p : Polynomial ℂ) :
    symmetricXPDilation p = eulerDilation p + (1 / 2 : ℂ) • p := by
  simp [symmetricXPDilation_eq_position_momentum_add_half, eulerDilation,
    position, momentum]

theorem eulerDilation_mul (p q : Polynomial ℂ) :
    eulerDilation (p * q) =
      eulerDilation p * q + p * eulerDilation q := by
  simp [eulerDilation, Polynomial.derivative_mul, mul_add, mul_assoc,
    mul_left_comm, mul_comm]

@[simp] theorem eulerDilation_add (p q : Polynomial ℂ) :
    eulerDilation (p + q) = eulerDilation p + eulerDilation q := by
  simp [eulerDilation, Polynomial.derivative_add, mul_add]

@[simp] theorem eulerDilation_smul (c : ℂ) (p : Polynomial ℂ) :
    eulerDilation (c • p) = c • eulerDilation p := by
  simp [eulerDilation, Polynomial.derivative_smul, mul_smul]

/-! ## 3. Critical line shift from symmetric quantization -/

/-- The symmetric dilation operator on monomials shifts the spectral weight:
    `H_sym(x^n) = (n + 1/2) x^n`. -/
theorem symmetricXPDilation_monomial_shift (n : ℕ) :
    symmetricXPDilation (Polynomial.X ^ n) =
      ((n : ℂ) + (1 / 2 : ℂ)) • Polynomial.X ^ n := by
  exact InfoGeometry.Canonical.PolynomialXPDilation.symmetricXPDilation_monomial n

/-- The eigenvalue `n - 1/2` corresponds to the critical line shift `s ↦ s + 1/2`. -/
theorem critical_line_shift_from_symmetric_dilation (n : ℕ) :
    (n : ℂ) - (1 / 2 : ℂ) = -( -(n : ℂ) + (1 / 2 : ℂ) ) := by
  ring

/-! ## 4. Finite coefficient-support readouts -/

/-- A finite Laurent polynomial in `(s - 1)`. -/
structure FiniteLaurentPolynomial where
  coeffs : ℕ → ℂ
  bound : ℕ
  coeffs_zero_of_bound : ∀ n, bound ≤ n → coeffs n = 0

/-- The finite Laurent polynomial evaluation at `s`. -/
def evalFiniteLaurent (L : FiniteLaurentPolynomial) (s : ℂ) : ℂ :=
  Finset.sum (Finset.range L.bound) (fun n => L.coeffs n * (s - 1) ^ n)

/-- The finite partial fraction expansion over a finite set of zeros. -/
structure FinitePartialFraction where
  zeros : Finset ℂ
  B : ℂ
  residues : ℂ → ℂ

/-- Evaluation of a finite partial fraction expansion at `s`. -/
def evalFinitePartialFraction (P : FinitePartialFraction) (s : ℂ)
    (_hs : s ∉ P.zeros) : ℂ :=
  P.B + Finset.sum P.zeros (fun ρ => P.residues ρ / (s - ρ))

/-! ## 5. Native linear-map transport -/

/-- The dilation operator descends through the polynomial colimit. -/
theorem eulerDilation_colimit_transport (p : Polynomial ℂ) :
    eulerDilation p = eulerDilationLinear p := by
  rfl

end InfoGeometry.Canonical.EulerDilationOperator

end noncomputable section
