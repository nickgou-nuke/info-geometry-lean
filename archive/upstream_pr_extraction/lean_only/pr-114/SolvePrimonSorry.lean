import Mathlib.Tactic
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.External.Auto.FermionicPrimonPartition

open InfoGeometry.Canonical.UHFInductiveColimitBoundary

noncomputable section

variable (primes : ℕ → ℕ) (β : ℝ) (n : ℕ)

def singlePrimeFactor (n : ℕ) : ℝ :=
  singlePrimeFermionPartition (primes n) β

theorem singlePrimeFactor_pos : 0 < singlePrimeFactor primes β n := by
  dsimp [singlePrimeFactor]
  rw [singlePrimeFermionPartition_eq]
  dsimp [fermionPrimeBoltzmannWeight]
  have h1 : (0 : ℝ) ≤ (primes n : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (primes n : ℝ) ^ (-β) := Real.rpow_nonneg h1 _
  linarith

theorem singlePrimeFactor_ne_zero : (singlePrimeFactor primes β n : ℂ) ≠ 0 := by
  have hpos := singlePrimeFactor_pos primes β n
  have hne : singlePrimeFactor primes β n ≠ 0 := ne_of_gt hpos
  exact_mod_cast hne

end noncomputable section
