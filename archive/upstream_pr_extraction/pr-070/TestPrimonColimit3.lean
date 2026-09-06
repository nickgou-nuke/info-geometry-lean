import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.External.Auto.FermionicPrimonPartition

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

noncomputable section

namespace InfoGeometry.Canonical.PrimonThermodynamicColimit

variable (primes : ℕ → ℕ) (β : ℝ)

def finiteBoltzmannWeight (n : ℕ) (w : BitWord n) : ℝ :=
  (Finset.univ : Finset (Fin n)).prod fun i => fermionOccupationWeight (primes i) β (w i)

def finitePartitionFunction (n : ℕ) : ℝ :=
  (Finset.univ : Finset (BitWord n)).sum (finiteBoltzmannWeight primes β n)

def finiteGibbsState (n : ℕ) (w : BitWord n) : ℝ :=
  finiteBoltzmannWeight primes β n w / finitePartitionFunction primes β n

def expectedValue (n : ℕ) (f : DiagAlg n) : ℂ :=
  (Finset.univ : Finset (BitWord n)).sum fun w => f w * (finiteGibbsState primes β n w : ℂ)

def singlePrimeFactor (n : ℕ) : ℝ :=
  singlePrimeFermionPartition (primes n) β

theorem finiteBoltzmannWeight_succ (n : ℕ) (w : BitWord (n + 1)) :
    finiteBoltzmannWeight primes β (n + 1) w =
      finiteBoltzmannWeight primes β n (prefixSucc n w) *
        fermionOccupationWeight (primes n) β (w ⟨n, Nat.lt_succ_self n⟩) := by
  dsimp [finiteBoltzmannWeight, prefixSucc]
  rw [Fin.prod_univ_castSucc]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  congr

end InfoGeometry.Canonical.PrimonThermodynamicColimit
