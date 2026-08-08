import Mathlib
import proofs.SplitOctonionDerivationSpace
import proofs.SplitOctonionInnerDerivation
import proofs.SplitOctonionDerivationG2Bridge

open SplitOctonion
open OctDerivation
open SplitOctonionInnerDerivation
open SplitOctonionG2Bridge

namespace SplitOctonionDerivationG2Chevalley

/-- The First Simple Root (Short Root α) 
    Re-using the certified operators from the G2Bridge. -/
noncomputable def H_alpha : OctDerivation := mkInnerDeriv E F
noncomputable def E_alpha : OctDerivation := (1/2 : ℝ) • mkInnerDeriv H E
noncomputable def F_alpha : OctDerivation := -(1/2 : ℝ) • mkInnerDeriv H F

/-- The Second Simple Root (Long Root β) -/
noncomputable def H_beta : OctDerivation := sorry
noncomputable def E_beta : OctDerivation := sorry
noncomputable def F_beta : OctDerivation := sorry

/-- The G_2 Cartan Matrix relations
    A = [[ 2, -1 ],
         [-3,  2 ]] -/

theorem cartan_alpha_alpha :
    ⁅H_alpha, E_alpha⁆ = (2 : ℝ) • E_alpha := by sorry

theorem cartan_beta_beta :
    ⁅H_beta, E_beta⁆ = (2 : ℝ) • E_beta := by sorry

theorem cartan_alpha_beta :
    ⁅H_alpha, E_beta⁆ = (-1 : ℝ) • E_beta := by sorry

theorem cartan_beta_alpha :
    ⁅H_beta, E_alpha⁆ = (-3 : ℝ) • E_alpha := by sorry

/-- Serre Relations -/
theorem serre_alpha_beta :
    ⁅E_alpha, ⁅E_alpha, E_beta⁆⁆ = 0 := by sorry

theorem serre_beta_alpha :
    ⁅E_beta, ⁅E_beta, ⁅E_beta, ⁅E_beta, E_alpha⁆⁆⁆⁆ = 0 := by sorry

/-- The Dimension Theorem (Span and Independence) -/
theorem g2_dim_fourteen : 
    Module.finrank ℝ OctDerivation = 14 := by sorry

end SplitOctonionDerivationG2Chevalley
