import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeBitLattice
import InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost


noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite

def diracCoefficient
    (_L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (p : ℕ) : ℝ :=
  Real.sqrt (Real.log p)

theorem diracCoefficient_sq_eq_log
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
  {p : ℕ}
  (hp : p ∈ L.primes) :
    diracCoefficient L p * diracCoefficient L p = Real.log p := by
  unfold diracCoefficient
  have hpgt1nat : 1 ≤ p := by
    exact le_of_lt (Nat.Prime.one_lt (L.isPrime p hp))
  have hpgt1 : (1 : ℝ) ≤ p := by
    exact_mod_cast hpgt1nat
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hpgt1
  have hsquare : (Real.sqrt (Real.log p)) ^ 2 = Real.log p :=
    Real.sq_sqrt hlog
  simpa [pow_two] using hsquare

def finiteDiracHamiltonian
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) : ℝ :=
  ∑ p ∈ ψ.support, diracCoefficient L p * diracCoefficient L p

theorem finiteDiracHamiltonian_eq_primeBitEnergy
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      InfoGeometry.Arithmetic.primeBitEnergy L ψ.support := by
  unfold finiteDiracHamiltonian
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [diracCoefficient_sq_eq_log L (ψ.property hp)]

theorem finiteDiracHamiltonian_eq_log_primeBitInteger
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      Real.log (InfoGeometry.Arithmetic.primeBitInteger L ψ : ℝ) := by
  rw [finiteDiracHamiltonian_eq_primeBitEnergy]
  exact InfoGeometry.Arithmetic.primeBitEnergy_eq_log_primeBitInteger (L := L) ψ

end InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite
