import Mathlib
import InfoGeometry.Arithmetic.PrimeBitLattice
import InfoGeometry.Arithmetic.PrimeSpinorSquareRootBoost

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite

Finite Dirac-square surface for the prime-bit arithmetic lane.

This module stays entirely finite:

* the one-particle coefficient is normalized as `sqrt (log p)`;
* the Dirac Hamiltonian is the finite sum of coefficient squares;
* that readout agrees with the existing finite prime-bit energy;
* the energy readout agrees with the logarithm of the represented integer.

No infinite zeta product, analytic continuation, Pfaffian determinant, or RH
claim is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite

/-- The finite Dirac coefficient `sqrt(log p)`. -/
def diracCoefficient
    (_L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (p : ℕ) : ℝ :=
  Real.sqrt (Real.log p)

/-- The Dirac coefficient squares to the logarithmic prime energy. -/
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

/--
Finite Dirac Hamiltonian readout over the occupied prime modes of a state.

The finite Hamiltonian is the sum of coefficient squares over the occupied
prime set.  This is the square-root layer that underlies the thermal
exponential readouts.
-/
def finiteDiracHamiltonian
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) : ℝ :=
  ∑ p ∈ ψ.support, diracCoefficient L p * diracCoefficient L p

/-- The finite Dirac Hamiltonian is the occupied prime-bit energy. -/
theorem finiteDiracHamiltonian_eq_primeBitEnergy
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      InfoGeometry.Arithmetic.primeBitEnergy L ψ.support := by
  unfold finiteDiracHamiltonian
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [diracCoefficient_sq_eq_log L (ψ.property hp)]

/-- The finite Dirac Hamiltonian is the logarithm of the represented integer. -/
theorem finiteDiracHamiltonian_eq_log_primeBitInteger
    (L : InfoGeometry.Arithmetic.PrimeBitLattice)
    (ψ : InfoGeometry.Arithmetic.PrimeBitState L) :
    finiteDiracHamiltonian L ψ =
      Real.log (InfoGeometry.Arithmetic.primeBitInteger L ψ : ℝ) := by
  rw [finiteDiracHamiltonian_eq_primeBitEnergy]
  exact InfoGeometry.Arithmetic.primeBitEnergy_eq_log_primeBitInteger (L := L) ψ

end InfoGeometry.Arithmetic.PrimeMajoranaDiracFinite
