import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.MvPolynomial.Basic
import InfoGeometry.Arithmetic.PrimeThermodynamicStage
import InfoGeometry.Arithmetic.ChiralPrimonGas

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeOccupationAlgebra

open InfoGeometry.Arithmetic.PrimeThermodynamicStage
open InfoGeometry.Arithmetic.ChiralPrimonGas

@[rep_depth thermo]
abbrev PrimeStage (n : ℕ) :=
  MvPolynomial (primesUpto n) ℂ

def primeVarEmbed {n m : ℕ} (h : n ≤ m) : primesUpto n → primesUpto m :=
  fun p => ⟨p.1, primesUpto_mono h p.2⟩

@[rep_depth thermo]
def primeBondAlg (n : ℕ) : PrimeStage n →ₐ[ℂ] PrimeStage (n + 1) :=
  MvPolynomial.rename (primeVarEmbed (Nat.le_succ n))

@[rep_depth thermo]
def primeBond (n : ℕ) : PrimeStage n →+* PrimeStage (n + 1) :=
  (primeBondAlg n).toRingHom

def bondMapAlg {n m : ℕ} (h : n ≤ m) : PrimeStage n →ₐ[ℂ] PrimeStage m :=
  MvPolynomial.rename (primeVarEmbed h)

def bondMap {n m : ℕ} (h : n ≤ m) : PrimeStage n →+* PrimeStage m :=
  (bondMapAlg h).toRingHom

@[simp]
theorem bondMap_X {n m : ℕ} (h : n ≤ m) (p : primesUpto n) :
    bondMap h (MvPolynomial.X p) = MvPolynomial.X (primeVarEmbed h p) := by
  unfold bondMap bondMapAlg
  exact MvPolynomial.rename_X (primeVarEmbed h) p

@[simp]
theorem primeBond_X (n : ℕ) (p : primesUpto n) :
    primeBond n (MvPolynomial.X p) = MvPolynomial.X (primeVarEmbed (Nat.le_succ n) p) := by
  exact bondMap_X (Nat.le_succ n) p

theorem primeVarEmbed_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (primeVarEmbed h) := by
  intro p q heq
  apply Subtype.ext
  have h1 : (primeVarEmbed h p).val = (primeVarEmbed h q).val := by rw [heq]
  exact h1

theorem bondMap_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (bondMap h) := by
  unfold bondMap bondMapAlg
  exact MvPolynomial.rename_injective (primeVarEmbed h) (primeVarEmbed_injective h)

theorem primeBond_injective (n : ℕ) :
    Function.Injective (primeBond n) :=
  bondMap_injective (Nat.le_succ n)

end InfoGeometry.Arithmetic.PrimeOccupationAlgebra
