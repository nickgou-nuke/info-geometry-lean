import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Möbius Inversion as the Discrete Divisor Transform

The integral/discrete transform that inverts the bosonic divisor sum is
Dirichlet convolution with the Möbius kernel.

If

`g n = ∑ d | n, f d`,

then

`f n = ∑ xy = n, μ x * g y`.

Equivalently, in the arithmetic-function convolution algebra, the constant
one function `ζ` and the Möbius function `μ` are inverses.
-/

noncomputable section

open ArithmeticFunction
open scoped zeta
open scoped ArithmeticFunction.Moebius

def dirichletConvolution (f g : ArithmeticFunction ℤ) : ArithmeticFunction ℤ :=
  f * g

def bosonicKernel : ArithmeticFunction ℤ :=
  ζ

def fermionicMobiusKernel : ArithmeticFunction ℤ :=
  μ

def vacuumKernel : ArithmeticFunction ℤ :=
  1

theorem mobius_is_dirichlet_inverse :
    dirichletConvolution bosonicKernel fermionicMobiusKernel = vacuumKernel := by
  simp [dirichletConvolution, bosonicKernel, fermionicMobiusKernel, vacuumKernel]

theorem mobius_inverse_left :
    dirichletConvolution fermionicMobiusKernel bosonicKernel = vacuumKernel := by
  simp [dirichletConvolution, bosonicKernel, fermionicMobiusKernel, vacuumKernel]

theorem boson_then_fermion_recovers (f : ArithmeticFunction ℤ) :
    dirichletConvolution (dirichletConvolution f bosonicKernel)
      fermionicMobiusKernel = f := by
  unfold dirichletConvolution bosonicKernel fermionicMobiusKernel
  rw [mul_assoc, coe_zeta_mul_moebius, mul_one]

theorem fermion_then_boson_recovers (f : ArithmeticFunction ℤ) :
    dirichletConvolution (dirichletConvolution f fermionicMobiusKernel)
      bosonicKernel = f := by
  unfold dirichletConvolution bosonicKernel fermionicMobiusKernel
  rw [mul_assoc, moebius_mul_coe_zeta, mul_one]

/-- Divisor-sum Möbius inversion: the concrete discrete integral transform. -/
theorem mobius_inversion_divisor_sum {f g : ℕ → ℤ} :
    (∀ n > 0, ∑ d ∈ n.divisors, f d = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : ℤ) * g x.snd = f n :=
  sum_eq_iff_sum_mul_moebius_eq

end noncomputable section
