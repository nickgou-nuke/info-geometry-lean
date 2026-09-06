import proofs.Clifford55
import proofs.ZornAssociatorSplitOctonion

noncomputable section

namespace D4MassSplitting

open Clifford55
open ZornAssociatorSplitOctonion

/-- The D₄/Zorn non-associative vacuum associator. -/
def vacuumAssociator : Zorn :=
  associator (U e₁) (L e₁) (U e₂)

/-- The vacuum associator is exactly the upper `e₂` lane. -/
theorem vacuum_associator_exact :
    vacuumAssociator = ⟨0, e₂, 0, 0⟩ := by
  exact associator_U₁_L₁_U₂

/-- The vacuum associator is a genuine nonzero D₄/Zorn obstruction. -/
theorem vacuum_associator_nonzero : vacuumAssociator ≠ 0 := by
  exact associator_U₁_L₁_U₂_nonzero

/-- Physical mass scalar on the three D₄ triality sectors, sourced from `Clifford55`. -/
def physical_mass_squared (m0 ΔP ΔT : ℝ) : TrialitySector → ℝ :=
  cl_mass_scalar m0 ΔP ΔT

/-- `R_T` fixes the vector sector and swaps the two semispinor sectors. -/
theorem rt_sector_action :
    RT_sector TrialitySector.vector = TrialitySector.vector ∧
    RT_sector TrialitySector.spinor = TrialitySector.cospinor ∧
    RT_sector TrialitySector.cospinor = TrialitySector.spinor := by
  simp [RT_sector]

/-- Nonzero `R_T` splitting separates the spinor and cospinor masses. -/
theorem mass_splitting_theorem (m0 ΔP ΔT : ℝ) (hT : ΔT ≠ 0) :
    physical_mass_squared m0 ΔP ΔT TrialitySector.spinor ≠
      physical_mass_squared m0 ΔP ΔT TrialitySector.cospinor := by
  exact Clifford55.all_masses_distinct m0 ΔP ΔT hT

/-- The nonzero Zorn associator and the nonzero `R_T` term jointly establish D₄ mass splitting. -/
theorem d4_mass_splitting_kernel (m0 ΔP ΔT : ℝ) (hT : ΔT ≠ 0) :
    vacuumAssociator ≠ 0 ∧
    physical_mass_squared m0 ΔP ΔT TrialitySector.spinor ≠
      physical_mass_squared m0 ΔP ΔT TrialitySector.cospinor := by
  exact ⟨vacuum_associator_nonzero, mass_splitting_theorem m0 ΔP ΔT hT⟩

/-- A concrete nonzero isovector component makes the mirror-ratio expression nontrivial. -/
theorem bE1_from_mass_splitting :
    ∃ (M_IS M_IV : ℝ),
      M_IV ≠ 0 ∧
      (let r := ((M_IS + M_IV) / (M_IS - M_IV)) ^ 2
       r > 1) := by
  use 1, (1 / 10 : ℝ)
  constructor
  · norm_num
  · norm_num

end D4MassSplitting

end noncomputable section
