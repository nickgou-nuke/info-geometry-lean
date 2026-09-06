import Mathlib
import InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
import InfoGeometry.Arithmetic.PrimonFinite
import InfoGeometry.Meta.Architecture
import InfoGeometry.Thermodynamics.SouriauTemperature

/-!
# InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauWeights

Finite complex-Souriau grand-canonical thermodynamics for the prime register.

This module keeps the theorem-carrying part finite and algebraic:

* complex Souriau temperature weights on a finite prime register;
* finite fermionic / bosonic / signed-Moebius partition readouts;
* Massieu-Planck and grand-potential scalar readouts;
* finite prime specialization of the same identities.

No infinite Euler product, analytic continuation, Lee-Yang theorem,
Hilbert--Polya operator, or RH claim is made here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauWeights

open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Arithmetic.PrimeGrandCanonicalEnsemble
open InfoGeometry.Arithmetic.PrimonFinite

/-! ## 1. Complex Souriau grand-canonical weights -/

/--
Complex grand-canonical mode weight.

The complex Souriau temperature contributes through the exponential kernel
`exp(-β(E - μ))`.
-/
def complexGrandModeWeight
    (β : InfoGeometry.Thermodynamics.SouriauTemperature)
    (energy mu : ℕ → ℝ) (p : ℕ) : ℂ :=
  Complex.exp (-(β.s * ((energy p - mu p : ℝ) : ℂ)))

/-- Finite fermionic grand partition over a finite prime register. -/
def complexFermionGrandPartition
    (P : PrimeRegister) (β : InfoGeometry.Thermodynamics.SouriauTemperature)
    (energy mu : ℕ → ℝ) : ℂ :=
  ZF P.primes (complexGrandModeWeight β energy mu)

/-- Finite signed fermionic / Möbius grand supertrace. -/
def complexFermionGrandSupertrace
    (P : PrimeRegister) (β : InfoGeometry.Thermodynamics.SouriauTemperature)
    (energy mu : ℕ → ℝ) : ℂ :=
  STrF P.primes (complexGrandModeWeight β energy mu)

/-- Finite bosonic grand partition. -/
def complexBosonGrandPartition
    (P : PrimeRegister) (β : InfoGeometry.Thermodynamics.SouriauTemperature)
    (energy mu : ℕ → ℝ) : ℂ :=
  ZB P.primes (complexGrandModeWeight β energy mu)

theorem complexFermionGrandPartition_eq_prod
  (P : PrimeRegister) (β : InfoGeometry.Thermodynamics.SouriauTemperature)
  (energy mu : ℕ → ℝ) :
    complexFermionGrandPartition P β energy mu =
      ∏ p ∈ P.primes, (1 + complexGrandModeWeight β energy mu p) := by
  simpa [complexFermionGrandPartition] using
    (ZF_eq_prod P.primes (complexGrandModeWeight β energy mu))

theorem complexFermionGrandSupertrace_eq_prod
  (P : PrimeRegister) (β : InfoGeometry.Thermodynamics.SouriauTemperature)
  (energy mu : ℕ → ℝ) :
    complexFermionGrandSupertrace P β energy mu =
      ∏ p ∈ P.primes, (1 - complexGrandModeWeight β energy mu p) := by
  simpa [complexFermionGrandSupertrace] using
    (STrF_eq_prod P.primes (complexGrandModeWeight β energy mu))

theorem complexBosonGrandPartition_eq_prod_inv
    (P : PrimeRegister) (β : InfoGeometry.Thermodynamics.SouriauTemperature)
    (energy mu : ℕ → ℝ) :
    complexBosonGrandPartition P β energy mu =
      ∏ p ∈ P.primes, (1 - complexGrandModeWeight β energy mu p)⁻¹ := by
  simp [complexBosonGrandPartition, ZB]

theorem complexBoson_mul_signedFermionGrandSupertrace_eq_one
    (P : PrimeRegister) (β : InfoGeometry.Thermodynamics.SouriauTemperature)
    (energy mu : ℕ → ℝ)
    (h : ∀ p ∈ P.primes, 1 - complexGrandModeWeight β energy mu p ≠ 0) :
    complexBosonGrandPartition P β energy mu *
        complexFermionGrandSupertrace P β energy mu = 1 := by
  rw [complexBosonGrandPartition_eq_prod_inv,
      complexFermionGrandSupertrace_eq_prod]
  rw [← Finset.prod_mul_distrib]
  exact local_susy_cancellation P.primes
    (complexGrandModeWeight β energy mu) h

/-! ## 2. Massieu / grand potential readouts -/

/-- Massieu-Planck potential `Φ = log Z`. -/
def massieuPlanck (Z : ℂ) : ℂ :=
  Complex.log Z

/-- Grand potential `Ω = -β⁻¹ Φ`. -/
def grandPotential (β Z : ℂ) : ℂ :=
  -β⁻¹ * massieuPlanck Z

theorem grandPotential_eq_neg_inv_beta_mul_massieu
    (β Z : ℂ) :
    grandPotential β Z = -β⁻¹ * massieuPlanck Z := rfl

/-! ## 3. Finite prime specialization -/

/-- Prime energy specialization `E_p = log p`. -/
def primeEnergy (p : ℕ) : ℝ :=
  Real.log p

/-- Zero chemical potential specialization. -/
def zeroChemicalPotential (_p : ℕ) : ℝ :=
  0

/-- Finite prime bosonic grand partition. -/
def finitePrimeBosonGrandPartition
    (P : PrimeRegister)
    (β : InfoGeometry.Thermodynamics.SouriauTemperature) : ℂ :=
  complexBosonGrandPartition P β primeEnergy zeroChemicalPotential

/-- Finite prime signed grand supertrace. -/
def finitePrimeSignedGrandSupertrace
    (P : PrimeRegister)
    (β : InfoGeometry.Thermodynamics.SouriauTemperature) : ℂ :=
  complexFermionGrandSupertrace P β primeEnergy zeroChemicalPotential

def finitePrimeMassieu
    (P : PrimeRegister)
    (β : InfoGeometry.Thermodynamics.SouriauTemperature) : ℂ :=
  massieuPlanck (finitePrimeBosonGrandPartition P β)

/-- Finite prime grand potential. -/
def finitePrimeGrandPotential
    (P : PrimeRegister)
    (β : InfoGeometry.Thermodynamics.SouriauTemperature) : ℂ :=
  grandPotential β.s (finitePrimeBosonGrandPartition P β)

theorem finitePrimeBosonGrandPartition_eq_prod
    (P : PrimeRegister)
    (β : InfoGeometry.Thermodynamics.SouriauTemperature) :
    finitePrimeBosonGrandPartition P β =
      ∏ p ∈ P.primes, (1 - complexGrandModeWeight β primeEnergy zeroChemicalPotential p)⁻¹ := by
  rfl

theorem finitePrimeSignedGrandSupertrace_eq_prod
    (P : PrimeRegister)
    (β : InfoGeometry.Thermodynamics.SouriauTemperature) :
    finitePrimeSignedGrandSupertrace P β =
      ∏ p ∈ P.primes, (1 - complexGrandModeWeight β primeEnergy zeroChemicalPotential p) := by
  simpa [finitePrimeSignedGrandSupertrace] using
    (complexFermionGrandSupertrace_eq_prod P β primeEnergy zeroChemicalPotential)

theorem finitePrimeGrandPotential_eq
    (P : PrimeRegister)
    (β : InfoGeometry.Thermodynamics.SouriauTemperature) :
    finitePrimeGrandPotential P β =
      -β.s⁻¹ * massieuPlanck (finitePrimeBosonGrandPartition P β) := by
  rfl

end InfoGeometry.Arithmetic.PrimeGrandCanonicalSouriauWeights
