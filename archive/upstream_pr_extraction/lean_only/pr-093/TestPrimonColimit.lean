import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.External.Auto.FermionicPrimonPartition

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

noncomputable section

namespace InfoGeometry.Canonical.PrimonThermodynamicColimit

variable (primes : ℕ → ℕ) (β : ℝ)

/-- Unnormalized Boltzmann weight of a configuration `w : BitWord n` -/
def finiteBoltzmannWeight (n : ℕ) (w : BitWord n) : ℝ :=
  (Finset.univ : Finset (Fin n)).prod fun i => fermionOccupationWeight (primes i) β (w i)

/-- The partition function is the sum of unnormalized weights -/
def finitePartitionFunction (n : ℕ) : ℝ :=
  (Finset.univ : Finset (BitWord n)).sum (finiteBoltzmannWeight primes β n)

/-- The normalized thermodynamic state (probability measure on BitWord n) -/
def finiteGibbsState (n : ℕ) (w : BitWord n) : ℝ :=
  finiteBoltzmannWeight primes β n w / finitePartitionFunction primes β n

/-- The expected value of a diagonal observable `f : DiagAlg n` -/
def expectedValue (n : ℕ) (f : DiagAlg n) : ℂ :=
  (Finset.univ : Finset (BitWord n)).sum fun w => f w * (finiteGibbsState primes β n w : ℂ)

end InfoGeometry.Canonical.PrimonThermodynamicColimit
