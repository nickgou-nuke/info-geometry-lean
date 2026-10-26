import InfoGeometry.Canonical.QuadraticHamiltonianCCR
import InfoGeometry.Canonical.BerryKeatingOperatorBridge
import Mathlib.Algebra.Polynomial.Derivative

/-!
# A nonvacuous polynomial CCR realization and the existing dilation owner

Polynomial endomorphisms are an infinite-dimensional algebraic realization.
This file puts no Hilbert structure on polynomials and makes no self-adjointness,
normalizability, distributional eigenstate, or spectral identification claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuadraticHamiltonian

/-- Coordinate multiplication on the native complex polynomial module. -/
def polynomialPosition : Module.End ℂ (Polynomial ℂ) where
  toFun f := Polynomial.X * f
  map_add' f g := mul_add Polynomial.X f g
  map_smul' r f := Algebra.mul_smul_comm r Polynomial.X f

/-- Exact CCR on polynomials, not a finite cutoff with a discarded boundary. -/
def polynomialCCR : SplitClifford.CCRPair (Module.End ℂ (Polynomial ℂ)) where
  ann := Polynomial.derivative
  cre := polynomialPosition
  commutator := by
    apply LinearMap.ext
    intro f
    change Polynomial.derivative (Polynomial.X * f) -
      Polynomial.X * Polynomial.derivative f = f
    simp [Polynomial.derivative_mul]

/-- Momentum `-i d/dx` on complex polynomials. -/
def polynomialMomentum : Module.End ℂ (Polynomial ℂ) :=
  (-Complex.I) • Polynomial.derivative

theorem polynomial_position_momentum_ccr :
    ⁅polynomialPosition, polynomialMomentum⁆ =
      Complex.I • (1 : Module.End ℂ (Polynomial ℂ)) :=
  ccrPair_position_momentum polynomialCCR

/-- Exact paper-normalized dilation action, including both the `2` and the `-i`. -/
theorem polynomial_H1_apply (f : Polynomial ℂ) :
    H1 polynomialPosition polynomialMomentum f =
      (-Complex.I) • ((2 : ℂ) • (Polynomial.X * Polynomial.derivative f) + f) := by
  change (-Complex.I) • Polynomial.derivative (Polynomial.X * f) +
    Polynomial.X * ((-Complex.I) • Polynomial.derivative f) = _
  rw [Polynomial.derivative_mul, Polynomial.derivative_X, one_mul]
  simp only [Algebra.mul_smul_comm, smul_add, smul_smul]
  module

/-- All three quadratic brackets on the actual native polynomial carrier. -/
theorem polynomial_quadratic_closure :
    ⁅H0 polynomialPosition polynomialMomentum, H1 polynomialPosition polynomialMomentum⁆ =
        (-4 * Complex.I) • H2 polynomialPosition polynomialMomentum ∧
    ⁅H1 polynomialPosition polynomialMomentum, H2 polynomialPosition polynomialMomentum⁆ =
        (4 * Complex.I) • H0 polynomialPosition polynomialMomentum ∧
    ⁅H2 polynomialPosition polynomialMomentum, H0 polynomialPosition polynomialMomentum⁆ =
        (-4 * Complex.I) • H1 polynomialPosition polynomialMomentum :=
  ⟨H0_comm_H1 _ _ polynomial_position_momentum_ccr,
    H1_comm_H2 _ _ polynomial_position_momentum_ccr,
    H2_comm_H0 _ _ polynomial_position_momentum_ccr⟩

/-- Exact normalization adapter to the existing real differential owner.
The physical complex momentum contributes an additional `-i`; it is not
silently identified with the real differentiation map. -/
theorem existing_real_dilation_normalization (f : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    BerryKeating.posOp (BerryKeating.derivOp f) x +
        BerryKeating.derivOp (BerryKeating.posOp f) x =
      2 * (x * deriv f x + (1 / 2 : ℝ) * f x) := by
  have h := BerryKeating.berry_keating_symmetric_form f x hf
  change x * deriv f x + deriv (fun y => y * f y) x = _
  linarith

/-- A concrete nonzero null classical generator: not the zero-Hamiltonian case. -/
theorem nonzero_null_example :
    discriminant (1 : ℝ) 0 1 = 0 ∧
    phaseGenerator 1 0 1 ^ 2 = 0 ∧ phaseGenerator 1 0 1 ≠ 0 := by
  refine ⟨by norm_num [discriminant], ?_, ?_⟩
  · apply phaseGenerator_sq_zero_of_null
    norm_num [discriminant]
  · intro h
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    norm_num [phaseGenerator] at hh

#check hamiltonian_rotated
#check diagonal_reconstruction
#check diagonal_discriminant
#check quarter_turn
#check phaseGenerator_sq
#check su11_relations
#check polynomial_quadratic_closure
#check polynomial_H1_apply
#check existing_real_dilation_normalization

end InfoGeometry.Canonical.QuadraticHamiltonian
