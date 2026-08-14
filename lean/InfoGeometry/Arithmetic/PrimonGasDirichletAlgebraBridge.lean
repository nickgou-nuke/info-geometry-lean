import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonGasDirichletAlgebraBridge

/-!
# Dirichlet-convolution identities

This module proves an abstract commutative-ring cancellation lemma and its
concrete specialization to Mathlib's `ArithmeticFunction ℝ` under Dirichlet
convolution. The concrete functions are Möbius, zeta, von Mangoldt, and log.
-/

-- ----------------------------------------------------------------
-- 1. Abstract Dirichlet convolution
-- ----------------------------------------------------------------

section AbstractDirichletRing

variable {A : Type*} [CommRing A]
variable (μ Λ Z L : A)

/-- Abstract cancellation/extraction identity in a commutative ring. -/
theorem abstract_mangoldt_moebius_parity_extraction
    (h_moebius_inversion : μ * Z = 1)
    (h_mangoldt_total_energy : Λ * Z = L) :
    Λ = L * μ := by
  calc
    Λ = Λ * 1 := by rw [mul_one]
    _ = Λ * (Z * μ) := by rw [← h_moebius_inversion, mul_comm μ Z]
    _ = (Λ * Z) * μ := by rw [← mul_assoc]
    _ = L * μ := by rw [h_mangoldt_total_energy]

end AbstractDirichletRing

-- ----------------------------------------------------------------
-- 2. Concrete ArithmeticFunction realization
-- ----------------------------------------------------------------

/-- Mathlib's Möbius arithmetic function, viewed over `ℝ`. -/
def moebiusArithmeticFunction : ArithmeticFunction ℝ :=
  ArithmeticFunction.moebius

/-- Mathlib's von Mangoldt arithmetic function, viewed over `ℝ`. -/
def vonMangoldtArithmeticFunction : ArithmeticFunction ℝ :=
  ArithmeticFunction.vonMangoldt

/-- Mathlib's logarithmic arithmetic function, viewed over `ℝ`. -/
def logArithmeticFunction : ArithmeticFunction ℝ :=
  ArithmeticFunction.log

/-- Mathlib's arithmetic zeta function, viewed over `ℝ`. -/
def zetaArithmeticFunction : ArithmeticFunction ℝ :=
  ArithmeticFunction.zeta

/-- Concrete Möbius inversion under Dirichlet convolution. -/
theorem concrete_moebius_inversion :
    moebiusArithmeticFunction * zetaArithmeticFunction = 1 :=
  ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ)

/-- Concrete von Mangoldt/logarithm convolution identity. -/
theorem concrete_mangoldt_total_energy :
    vonMangoldtArithmeticFunction * zetaArithmeticFunction = logArithmeticFunction :=
  ArithmeticFunction.vonMangoldt_mul_zeta

/-- Concrete extraction of the von Mangoldt function from the convolution identities. -/
theorem concrete_mangoldt_moebius_extraction :
    vonMangoldtArithmeticFunction = logArithmeticFunction * moebiusArithmeticFunction := by
  exact abstract_mangoldt_moebius_parity_extraction
    moebiusArithmeticFunction
    vonMangoldtArithmeticFunction
    zetaArithmeticFunction
    logArithmeticFunction
    concrete_moebius_inversion
    concrete_mangoldt_total_energy

/-- Bundles the three concrete Dirichlet-convolution identities. -/
theorem master_primon_gas_duality :
    (moebiusArithmeticFunction * zetaArithmeticFunction = 1) ∧
    (vonMangoldtArithmeticFunction * zetaArithmeticFunction = logArithmeticFunction) ∧
    (vonMangoldtArithmeticFunction = logArithmeticFunction * moebiusArithmeticFunction) := by
  constructor
  · exact concrete_moebius_inversion
  constructor
  · exact concrete_mangoldt_total_energy
  · exact concrete_mangoldt_moebius_extraction

end InfoGeometry.Arithmetic.PrimonGasDirichletAlgebraBridge
