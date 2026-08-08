import Mathlib
import proofs.ProjectiveWallpaperGaugePSA
import proofs.PentagonPenroseWallpaperFractal

/-!
# Ising model on the aperiodic Smith hat

Theorem-honest digest of Okabe--Niizeki--Araki,
"Ising model on the aperiodic Smith hat", arXiv:2402.11331v2.

The Lean kernel records the finite data, the original/dual Smith-kite pairing,
and the exact algebraic form of the Kramers--Wannier checks.
-/

noncomputable section

namespace SmithHatIsingDuality

open ProjectiveWallpaperGaugePSA

/-! ## 1. Finite Smith-hat / Smith-kite data -/

/-- The two dual lattices studied in arXiv:2402.11331v2. -/
inductive SmithKiteLattice where
  | original
  | dual
  deriving DecidableEq, Repr

/-- The Smith hat is a 13-sided monotile. -/
def smithHatSides : ℕ := 13

/-- The Smith hat used in the paper consists of eight kites. -/
def smithHatKites : ℕ := 8

/-- Largest total spin number reported in the simulations. -/
def maxReportedSpinNumber : ℕ := 939201

/-- Reported critical-temperature estimates, in units `T_c/J`. -/
def reportedCriticalTemperature : SmithKiteLattice → ℚ
  | .original => 2405 / 1000
  | .dual => 2143 / 1000

/-- Reported half-width uncertainty for each critical temperature. -/
def reportedCriticalTemperatureTolerance : ℚ := 5 / 10000

/-- Reported critical energy per spin for the original and dual lattices. -/
def reportedCriticalEnergyPerSpin : SmithKiteLattice → ℚ
  | .original => -1319 / 1000
  | .dual => -1505 / 1000

@[simp] theorem smith_hat_sides :
    smithHatSides = 13 := rfl

@[simp] theorem smith_hat_kites :
    smithHatKites = 8 := rfl

@[simp] theorem smith_hat_max_spins :
    maxReportedSpinNumber = 939201 := rfl

@[simp] theorem original_reported_Tc :
    reportedCriticalTemperature .original = 2405 / 1000 := rfl

@[simp] theorem dual_reported_Tc :
    reportedCriticalTemperature .dual = 2143 / 1000 := rfl

@[simp] theorem reported_Tc_tolerance :
    reportedCriticalTemperatureTolerance = 5 / 10000 := rfl

@[simp] theorem original_reported_energy_per_spin :
    reportedCriticalEnergyPerSpin .original = -1319 / 1000 := rfl

@[simp] theorem dual_reported_energy_per_spin :
    reportedCriticalEnergyPerSpin .dual = -1505 / 1000 := rfl

/-! ## 2. Kramers--Wannier algebraic readout -/

/-- Hyperbolic cotangent, used in the paper's critical-energy duality check. -/
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- Kramers--Wannier critical-temperature product for a dual pair. -/
def temperatureDualityProduct (J Tc TcDual : ℝ) : ℝ :=
  Real.sinh (2 * J / Tc) * Real.sinh (2 * J / TcDual)

/-- Critical-energy duality sum for a dual pair. -/
def energyDualitySum (J Tc TcDual eps epsDual : ℝ) : ℝ :=
  eps / coth (2 * J / Tc) + epsDual / coth (2 * J / TcDual)

/-- Nearest-neighbor correlation from the paper's energy convention. -/
def nearestNeighborCorrelation (energy : ℝ) (spinNumber : ℝ) : ℝ :=
  -energy / (2 * spinNumber)

/-- The temperature-duality equation is exactly the statement that the product is `1`. -/
theorem kramers_wannier_temperature_duality
    {J Tc TcDual : ℝ}
    (h : temperatureDualityProduct J Tc TcDual = 1) :
    Real.sinh (2 * J / Tc) * Real.sinh (2 * J / TcDual) = 1 := by
  exact h

/-- The energy-duality equation is exactly the statement that the normalized sum is `1`. -/
theorem kramers_wannier_energy_duality
    {J Tc TcDual eps epsDual : ℝ}
    (h : energyDualitySum J Tc TcDual eps epsDual = 1) :
    eps / coth (2 * J / Tc) + epsDual / coth (2 * J / TcDual) = 1 := by
  exact h

/-- The original and dual Smith-kite labels are distinct. -/
theorem original_ne_dual : SmithKiteLattice.original ≠ SmithKiteLattice.dual := by
  decide

/-! ## 3. Synthesis -/

/-- Capstone: finite paper data and exact duality equations compile. -/
theorem smith_hat_ising_duality_synthesis :
    smithHatSides = 13 ∧
    smithHatKites = 8 ∧
    maxReportedSpinNumber = 939201 ∧
    reportedCriticalTemperature .original = 2405 / 1000 ∧
    reportedCriticalTemperature .dual = 2143 / 1000 ∧
    reportedCriticalTemperatureTolerance = 5 / 10000 ∧
    reportedCriticalEnergyPerSpin .original = -1319 / 1000 ∧
    reportedCriticalEnergyPerSpin .dual = -1505 / 1000 ∧
    ProjectiveWallpaperGaugePSA.allWallpaperGroups.length = 17 ∧
    SmithKiteLattice.original ≠ SmithKiteLattice.dual := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ProjectiveWallpaperGaugePSA.allWallpaperGroups_length,
    original_ne_dual⟩

#check smith_hat_ising_duality_synthesis
#check kramers_wannier_temperature_duality
#check kramers_wannier_energy_duality

end SmithHatIsingDuality
