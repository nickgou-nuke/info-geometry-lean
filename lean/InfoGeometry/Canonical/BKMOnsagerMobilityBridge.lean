import Mathlib.Tactic
import InfoGeometry.InformationGeometry.BKMMetricModularBridge
import InfoGeometry.Canonical.FreeEnergyDissipationRate

/-!
# Finite BKM-induced Onsager mobility

The noncommutative BKM logarithmic-mean weights provide a concrete complex-linear
mobility map, acting entrywise in the chosen spectral basis. This module
identifies its Hilbert--Schmidt quadratic form with the repository-owned BKM
inner product and uses the existing metriplectic free-energy theorem.

This is a finite matrix realization, not an identification of arbitrary Onsager
operators with BKM, nor a theorem about analytic Type III modular flows.
-/

noncomputable section

namespace InfoGeometry.Canonical.BKMOnsagerMobilityBridge

open Matrix
open InfoGeometry.InformationGeometry.BKM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Mat := Matrix ι ι ℂ

/-- The positive logarithmic-mean multiplier on each spectral matrix unit. -/
def bkmOnsager (energies : ι → ℝ) : Mat →ₗ[ℂ] Mat where
  toFun X := fun i j => (bkmWeightScalar (energies i) (energies j) : ℂ) * X i j
  map_add' X Y := by
    ext i j
    simp [mul_add]
  map_smul' c X := by
    ext i j
    simp [mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem bkmOnsager_apply (energies : ι → ℝ) (X : Mat) (i j : ι) :
    bkmOnsager energies X i j =
      (bkmWeightScalar (energies i) (energies j) : ℂ) * X i j := rfl

/-- Hilbert--Schmidt pairing against the BKM mobility is the native BKM
pairing. The indices transpose inside the matrix trace, and weight symmetry
returns the original ordering. -/
theorem trace_star_bkmOnsager (energies : ι → ℝ) (X Y : Mat) :
    trace (star X * bkmOnsager energies Y) =
      bkmInnerProduct energies X Y := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.star_apply, bkmOnsager_apply, bkmInnerProduct]
  simp only [starRingEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positivity is inherited from the constructive BKM logarithmic mean. -/
theorem bkmOnsager_positive (energies : ι → ℝ) (X : Mat) :
    0 ≤ (trace (star X * bkmOnsager energies X)).re := by
  rw [trace_star_bkmOnsager]
  exact bkmInnerProduct_self_nonneg energies X

/-- The repository-owned metriplectic system with BKM-derived mobility. -/
def bkmDissipativeSystem (energies : ι → ℝ)
    (rho H gradF : Mat) :
    MetriplecticDissipation.MetriplecticDissipativeSystem ι where
  rho := rho
  H := H
  grad_F := gradF
  Onsager := bkmOnsager energies

/-- Unitary free-energy invariance is the only remaining condition for the
existing metriplectic theorem to imply nonincreasing free energy. -/
theorem bkm_freeEnergy_rate_nonpos
    (energies : ι → ℝ) (rho H gradF : Mat)
    (hunitary :
      (trace (star gradF *
        (-Complex.I • (H * rho - rho * H)))).re = 0) :
    MetriplecticDissipation.freeEnergyRate
      (bkmDissipativeSystem energies rho H gradF) ≤ 0 := by
  apply MetriplecticDissipation.freeEnergy_rate_nonpos
  · intro A
    exact bkmOnsager_positive energies A
  · exact hunitary

/-- A purely dissipative specialization needs no supplementary invariance
hypothesis: a zero Hamiltonian yields no unitary contribution. -/
theorem bkm_pureDissipation_rate_nonpos
    (energies : ι → ℝ) (rho gradF : Mat) :
    MetriplecticDissipation.freeEnergyRate
      (bkmDissipativeSystem energies rho 0 gradF) ≤ 0 := by
  apply bkm_freeEnergy_rate_nonpos
  simp

end InfoGeometry.Canonical.BKMOnsagerMobilityBridge
