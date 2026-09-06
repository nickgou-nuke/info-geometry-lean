import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge

/-!
# Finite Möbius--Mangoldt Dirichlet convolution bridge

This owner records only finite coefficient identities.  It does not assert an
analytic Dirichlet transform, an infinite Euler product, or an operator
inverse.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge

open ArithmeticFunction
open InfoGeometry.Arithmetic.FiniteMobiusOperatorInversionBridge
open InfoGeometry.Arithmetic.FiniteDirichletShiftOperatorBridge
open scoped BigOperators

/-- Complex logarithmic Dirichlet coefficients. -/
def logCoefficients : ℕ → ℝ := fun n => Real.log n

/-- Complex von Mangoldt coefficients. -/
def mangoldtCoefficients : ℕ → ℝ := vonMangoldt

def logCoefficientsComplex : ℕ → ℂ := fun n => (Real.log n : ℂ)

def mangoldtCoefficientsComplex : ℕ → ℂ := fun n => (vonMangoldt n : ℂ)

noncomputable def mangoldtDirichletOperator (N : ℕ) :
    TestFun →ₗ[ℂ] TestFun :=
  dirichletOperator N mangoldtCoefficientsComplex

theorem mangoldtDirichletOperator_expTestFun (N : ℕ) (s : ℂ) :
    mangoldtDirichletOperator N (expTestFun s) =
      (∑ n ∈ Finset.Icc 1 N,
        mangoldtCoefficientsComplex n *
          Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))) • expTestFun s := by
  unfold mangoldtDirichletOperator dirichletOperator
  simp [LinearMap.sum_apply, logNatShift_expTestFun, Finset.sum_smul,
    mangoldtCoefficientsComplex]
  apply Finset.sum_congr rfl
  intro n hn
  ext t
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Complex.real_smul]
  ring

theorem mangoldtDirichletOperator_expTestFun_cpow
    (N : ℕ) (s : ℂ) :
    mangoldtDirichletOperator N (expTestFun s) =
      (∑ n ∈ Finset.Icc 1 N,
        mangoldtCoefficientsComplex n * (n : ℂ) ^ (-s)) • expTestFun s := by
  rw [mangoldtDirichletOperator_expTestFun]
  apply congrArg (fun z : ℂ => z • expTestFun s)
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  rw [← complexPow_nat_eq_exp_neg_log n hnpos s]

/-- The finite pointwise identity `Λ = μ * log`. -/
theorem vonMangoldt_eq_mobius_convolution_log (n : ℕ) :
    mangoldtCoefficients n =
      ∑ d ∈ n.divisorsAntidiagonal,
        (moebius d.1 : ℝ) * logCoefficients d.2 := by
  change vonMangoldt n =
    ∑ d ∈ n.divisorsAntidiagonal, (moebius d.1 : ℝ) * Real.log d.2
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n)
    moebius_mul_log_eq_vonMangoldt
  dsimp at h
  exact h.symm

/-- The divisor-sum identity `log n = ∑ d ∣ n, Λ d`. -/
theorem log_eq_vonMangoldt_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, vonMangoldt d) = Real.log n := by
  exact ArithmeticFunction.vonMangoldt_sum

/-- The coefficient identity `1 * Λ = log`, in divisor-sum form. -/
theorem one_convolution_vonMangoldt_eq_log (n : ℕ) :
    logCoefficients n = ∑ d ∈ n.divisors, mangoldtCoefficients d := by
  symm
  exact log_eq_vonMangoldt_divisor_sum n

theorem rectangular_zeta_mangoldt_eq_log
    (N k : ℕ) (hk : k ≤ N) (hk0 : 0 < k) :
    rectangularDirichletConvolution N zetaCoefficients
      mangoldtCoefficientsComplex k = logCoefficientsComplex k := by
  rw [rectangularConvolution_eq_dirichletConvolution_of_le N zetaCoefficients
    mangoldtCoefficientsComplex k hk hk0]
  rw [← Nat.sum_divisorsAntidiagonal
    (fun a b => (zetaCoefficients a) * mangoldtCoefficientsComplex b)]
  have hfun :
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        ArithmeticFunction.vonMangoldt = ArithmeticFunction.log :=
    ArithmeticFunction.zeta_mul_vonMangoldt
  have h := congrArg (fun F : ArithmeticFunction ℝ => F k) hfun
  dsimp at h
  have hzero :
      (∑ x ∈ k.divisorsAntidiagonal,
        ((if x.1 = 0 then 0 else 1 : ℕ) : ℝ) * vonMangoldt x.2) =
        ∑ x ∈ k.divisorsAntidiagonal, vonMangoldt x.2 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx
    simp [hx0]
  rw [hzero] at h
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
  dsimp at hcast
  simpa [zetaCoefficients, mangoldtCoefficientsComplex, logCoefficientsComplex] using hcast

theorem rectangular_mobius_log_eq_mangoldt
    (N k : ℕ) (hk : k ≤ N) (hk0 : 0 < k) :
    rectangularDirichletConvolution N mobiusCoefficients
      logCoefficientsComplex k = mangoldtCoefficientsComplex k := by
  rw [rectangularConvolution_eq_dirichletConvolution_of_le N mobiusCoefficients
    logCoefficientsComplex k hk hk0]
  rw [← Nat.sum_divisorsAntidiagonal
    (fun a b => mobiusCoefficients a * logCoefficientsComplex b)]
  have hfun :
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        ArithmeticFunction.log = ArithmeticFunction.vonMangoldt :=
    ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  have h := congrArg (fun F : ArithmeticFunction ℝ => F k) hfun
  dsimp at h
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) h
  dsimp at hcast
  simpa [mobiusCoefficients, logCoefficientsComplex, mangoldtCoefficientsComplex] using hcast

/-- Möbius inversion for the zeta coefficient function over `ℤ`. -/
theorem zeta_mul_moebius_eq_one_int :
    (ArithmeticFunction.zeta * ArithmeticFunction.moebius : ArithmeticFunction ℤ) = 1 := by
  exact ArithmeticFunction.coe_zeta_mul_coe_moebius

end InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge
