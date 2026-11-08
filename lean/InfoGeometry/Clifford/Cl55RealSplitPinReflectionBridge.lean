import InfoGeometry.Clifford.Cl55RealSplitPinAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittPinCoverBridge

namespace InfoGeometry.Clifford.Clifford55

/-!
# Reflection bridge for the corrected split Pin subgroup

This file transfers only those reflection identities for which a corrected
split-subgroup unit is identified with a native Mathlib Pin lift.  It does not
claim that Mathlib's `pinGroup Q55` is the full split Pin group, nor that the
resulting image is all of `O(5,5)`.
-/

theorem realSplitPinTwistedActionEquiv_eq_pinTwistedActionEquiv
    (g : realSplitPin55) (h : Pin55)
    (hunit : (g : Cl55ˣ) = pinToUnits h) :
    realSplitPinTwistedActionEquiv g = pinTwistedActionEquiv h := by
  apply LinearEquiv.ext
  intro v
  change realSplitPinTwistedAction g v = pinTwistedAction h v
  apply ι55_injective
  rw [realSplitPinTwistedAction_apply_ι, pinTwistedAction_apply_ι]
  simp [realSplitPinTwistedAdj, pinTwistedAdj, hunit]

theorem realSplitPinOrthogonalAction_eq_pinTwistedOrthogonalAction
    (g : realSplitPin55) (h : Pin55)
    (hunit : (g : Cl55ˣ) = pinToUnits h) :
    realSplitPinOrthogonalAction g = pinTwistedOrthogonalAction h := by
  apply Subtype.ext
  simpa [realSplitPinOrthogonalAction, pinTwistedOrthogonalAction] using
    realSplitPinTwistedActionEquiv_eq_pinTwistedActionEquiv g h hunit

theorem realSplitPinTwistedActionEquiv_fNegPin_eq_negativeReflection
    (i : Fin 5) :
    ∃ g : realSplitPin55,
      realSplitPinTwistedActionEquiv g = negativeReflectionLinearEquiv i := by
  rcases fNeg_mem_realSplitPin i with ⟨g, hg⟩
  have hunit : (g : Cl55ˣ) = fNegUnit i := by
    apply Units.ext
    rw [hg, fNegUnit_coe]
  refine ⟨g, ?_⟩
  rw [realSplitPinTwistedActionEquiv_eq_pinTwistedActionEquiv g (fNegPin i) ?_]
  · exact pinTwistedActionEquiv_fNegPin_eq_negativeReflection i
  apply Units.ext
  rw [hunit]
  simpa [fNegPin] using
    congrArg (fun u : Cl55ˣ => (u : Cl55)) (pinToUnits_f_neg i).symm

theorem realSplitPinOrthogonalAction_fNeg (i : Fin 5) :
    ∃ g : realSplitPin55,
      realSplitPinOrthogonalAction g = coordinateReflectionGenerator i := by
  rcases fNeg_mem_realSplitPin i with ⟨g, hg⟩
  have hunit : (g : Cl55ˣ) = pinToUnits (fNegPin i) := by
    apply Units.ext
    rw [hg]
    simpa [fNegPin] using (pinToUnits_f_neg i).symm
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact realSplitPinTwistedActionEquiv_eq_pinTwistedActionEquiv g
    (fNegPin i) hunit |>.trans
      (by exact pinTwistedActionEquiv_fNegPin_eq_negativeReflection i)

theorem realSplitPinOrthogonalAction_globalSheet :
    ∃ g : realSplitPin55,
      realSplitPinOrthogonalAction g = globalSheetReflectionGenerator := by
  have hunit : globalSheetUnit = pinToUnits globalSheetPin := by
    apply Units.ext
    simpa [pinToUnits] using globalSheetUnit_coe
  refine ⟨⟨globalSheetUnit, globalSheetUnit_mem_realSplitPin⟩, ?_⟩
  apply Subtype.ext
  exact realSplitPinTwistedActionEquiv_eq_pinTwistedActionEquiv
    ⟨globalSheetUnit, globalSheetUnit_mem_realSplitPin⟩
    globalSheetPin hunit |>.trans
      (by exact pinTwistedActionEquiv_globalSheetPin_eq_globalSheetReflection)

end InfoGeometry.Clifford.Clifford55
