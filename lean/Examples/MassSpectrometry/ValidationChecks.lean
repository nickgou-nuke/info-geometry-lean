/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.MassSpectrometry.AbsorbingFragmentGrammar
import InfoGeometry.MassSpectrometry.CandidateChemistry
import InfoGeometry.MassSpectrometry.RationalSinkhorn

/-! Kernel-reduced acceptance and adversarial rejection examples. -/
namespace InfoGeometry.MassSpectrometry.ValidationChecks

private def candidate : RationalCandidate 2 2 where
  peakMass := ![100, 60]
  intensity := ![1, 1/2]
  edge u v := decide (u = 0 ∧ v = 1)
  rank := ![1, 0]
  fragmentMass := ![100, 60]
  assignment := !![1, 0; 0, 1]
  weight := ![!![0, 1/2; 0, 0], !![0, 3/4; 0, 0]]

example : candidate.check = true := by decide +kernel
example : ({ candidate with edge := fun _ _ => true }).check = false := by decide +kernel
example : ({ candidate with rank := ![0, 1] }).check = false := by decide +kernel
example : ({ candidate with fragmentMass := ![60, 100] }).check = false := by decide +kernel
example : ({ candidate with peakMass := ![0, 60] }).check = false := by decide +kernel
example : ({ candidate with intensity := ![1, -1] }).check = false := by decide +kernel
example : ({ candidate with assignment := !![1, 0; 1, 0] }).check = false := by decide +kernel
example : ({ candidate with weight := fun (_ : Fin 2) => !![0, -1; 0, 0] }).check = false := by decide +kernel
example : ({ candidate with weight := fun (_ : Fin 2) => !![0, 2; 0, 0] }).check = false := by decide +kernel
example : ({ candidate with weight := fun (_ : Fin 2) => !![0, 0; 1, 0] }).check = false := by decide +kernel

example : ¬ ∃ c : RationalCandidate 0 2, c.Valid := by
  rintro ⟨c, h⟩
  exact Nat.lt_irrefl 0 h.1

example : ¬ ∃ c : RationalCandidate 2 0, c.Valid := by
  rintro ⟨c, h⟩
  exact Nat.lt_irrefl 0 h.2.1

/-- Nonempty accepted input actually constructs the established model carrier. -/
noncomputable example : FiniteValuedFragmentationModel 2 :=
  candidate.toModel (candidate.check_eq_true_iff.mp (by decide +kernel)) (fun _ => 0)

private def chemistry : CandidateChemistry 2 2 where
  inventory := ![![4, 2], ![2, 2]]
  lossInventory := fun _ _ => ![2, 0]
  charge := ![1, 1]
  lossCharge := fun _ _ => 0

example : chemistry.check candidate = true := by decide +kernel
example : chemistry.checkNeutralLosses candidate = true := by decide +kernel
example : chemistry.checkMassModel candidate (![20, 10]) = true := by decide +kernel
example : chemistry.checkMassModel candidate (![12, 1]) = false := by decide +kernel
example : ({ chemistry with lossInventory := fun _ _ => ![0, 0] }).check candidate = false := by
  decide +kernel
example : ({ chemistry with lossCharge := fun _ _ => 1 }).check candidate = false := by decide +kernel

example : NumericalValidation.checkMassFit candidate 0 = true := by decide +kernel
example : NumericalValidation.checkMassFit { candidate with peakMass := ![101, 60] } 0 = false := by
  decide +kernel
example : NumericalValidation.checkMassFit { candidate with peakMass := ![101, 60] } 1 = true := by
  decide +kernel
example : NumericalValidation.checkAssignment (!![1, 0; 0, (999/1000 : ℚ)]) (1/1000) = true := by
  decide +kernel
example : NumericalValidation.checkAssignment (!![1, 0; 0, (999/1000 : ℚ)]) 0 = false := by
  decide +kernel
example : NumericalValidation.checkObservedResidual (![![1, 2]]) (![![1, 3]]) 0 = false := by
  decide +kernel
example : NumericalValidation.checkObservedResidual (![![1, 2]]) (![![1, 3]]) 1 = true := by
  decide +kernel

example : RationalSinkhorn.iterate 1 (!![1, 1; 1, (1 : ℚ)]) = !![1/2, 1/2; 1/2, 1/2] := by
  decide +kernel
example : NumericalValidation.checkAssignment
    (RationalSinkhorn.iterate 1 (!![1, 1; 1, (1 : ℚ)])) 0 = true := by decide +kernel
example : NumericalValidation.checkAssignment
    (RationalSinkhorn.iterate 1 (!![0, 0; 1, (1 : ℚ)])) 0 = false := by decide +kernel
-- String parsing is exercised by the executable JsonChecks suite.

end InfoGeometry.MassSpectrometry.ValidationChecks
