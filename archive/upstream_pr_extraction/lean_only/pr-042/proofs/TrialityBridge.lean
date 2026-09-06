import proofs.Clifford55
import proofs.ZornAssociatorSplitOctonion

noncomputable section

namespace TrialityBridge

open Clifford55
open ZornAssociatorSplitOctonion

/-- The Zorn associator `(U e1, L e1, U e2)` as an explicit element. -/
def zornAssociatorU1L1U2 : Zorn :=
  ZornAssociatorSplitOctonion.associator (U e₁) (L e₁) (U e₂)

/-- The associator `(U e1, L e1, U e2)` is the Zorn element with upper component `e2`. -/
theorem zorn_associator_U1_L1_U2_eq_upper_e2 :
    zornAssociatorU1L1U2 = ⟨0, e₂, 0, 0⟩ := by
  unfold zornAssociatorU1L1U2 ZornAssociatorSplitOctonion.associator
  change
    zornSub
      (zornMul (zornMul (U e₁) (L e₁)) (U e₂))
      (zornMul (U e₁) (zornMul (L e₁) (U e₂))) =
        ⟨0, e₂, 0, 0⟩
  apply Zorn.ext'
  · norm_num [zornSub, zornAdd, zornNeg, zornMul, U, L, dot3, cross3, e₁, e₂, basis3]
  · funext i
    fin_cases i <;>
      simp [zornSub, zornAdd, zornNeg, zornMul, U, L, cross3, dot3, e₁, e₂, basis3]
  · funext i
    fin_cases i <;>
      simp [zornSub, zornAdd, zornNeg, zornMul, U, L, cross3, dot3, e₁, e₂, basis3]
  · norm_num [zornSub, zornAdd, zornNeg, zornMul, U, L, dot3, cross3, e₁, e₂, basis3]

/-- The associator `(U e1, L e1, U e2)` is nonzero. -/
theorem zorn_associator_U1_L1_U2_ne_zero : zornAssociatorU1L1U2 ≠ 0 := by
  intro h
  have hu := congrArg (fun X : Zorn => X.u 1) h
  rw [zorn_associator_U1_L1_U2_eq_upper_e2] at hu
  change (1 : ℂ) = 0 at hu
  exact one_ne_zero hu

/-- The real Cl(5,5) layer supplies the `R_T` chirality swap. -/
theorem cl55_rt_semispinor_swap :
    RT_sector TrialitySector.spinor = TrialitySector.cospinor ∧
    RT_sector TrialitySector.cospinor = TrialitySector.spinor := by
  simp [RT_sector]

/-- Triality-sector mass scalar imported from the full `Clifford55` implementation. -/
def bridge_mass (m0 ΔP ΔT : ℝ) (s : TrialitySector) : ℝ :=
  cl_mass_scalar m0 ΔP ΔT s

/-- Nonzero `R_T` splitting lifts the `8s/8c` degeneracy in the Cl(5,5) spine. -/
theorem rt_lifts_semispinor_degeneracy (m0 ΔP ΔT : ℝ) (hT : ΔT ≠ 0) :
    bridge_mass m0 ΔP ΔT TrialitySector.spinor ≠
      bridge_mass m0 ΔP ΔT TrialitySector.cospinor := by
  intro h
  apply hT
  simp [bridge_mass, cl_mass_scalar] at h
  linarith

/-- Nonzero Zorn associator together with the `R_T` semispinor mass splitting. -/
theorem triality_bridge_semispinor_mass_splitting (m0 ΔP ΔT : ℝ) (hT : ΔT ≠ 0) :
    zornAssociatorU1L1U2 ≠ 0 ∧
    RT_sector TrialitySector.spinor = TrialitySector.cospinor ∧
    RT_sector TrialitySector.cospinor = TrialitySector.spinor ∧
    bridge_mass m0 ΔP ΔT TrialitySector.spinor ≠
      bridge_mass m0 ΔP ΔT TrialitySector.cospinor := by
  refine And.intro ?_ ?_
  · simpa using zorn_associator_U1_L1_U2_ne_zero
  refine And.intro ?_ ?_
  · simp [RT_sector]
  refine And.intro ?_ ?_
  · simp [RT_sector]
  · intro h
    apply hT
    simp [bridge_mass, cl_mass_scalar] at h
    linarith

end TrialityBridge

end noncomputable section
