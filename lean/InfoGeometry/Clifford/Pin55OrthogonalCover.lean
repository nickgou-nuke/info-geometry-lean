import InfoGeometry.Clifford.Cl55RealSplitPinKernelExact
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55RealSplitPinImage
import InfoGeometry.Clifford.Cl55WittFullOrthogonalSurjectivity

namespace InfoGeometry.Clifford.Clifford55

/-!
# Algebraic real split-Pin cover of the native orthogonal group

This owner packages the native corrected split-Pin action together with its
exact sign kernel and its surjectivity onto the native orthogonal group.
This is an algebraic double-cover statement.  It asserts no topology,
continuity, local triviality, or Lie-group covering-map structure.
-/

noncomputable def realSplitPinOrthogonalCover :
    realSplitPin55 →* orthogonalGroup55 :=
  realSplitPinOrthogonalAction

theorem realSplitPinOrthogonalCover_kernel_eq_signSubgroup :
    (realSplitPinOrthogonalCover).ker = realSplitPinSignSubgroup := by
  exact realSplitPinOrthogonalAction_kernel_eq_signSubgroup

theorem coordinateReflectionSubgroup_le_realSplitPinOrthogonalCover_range :
    coordinateReflectionSubgroup ≤ (realSplitPinOrthogonalCover).range := by
  exact coordinateReflectionSubgroup_le_realSplitPinOrthogonalImage

theorem globalSheetReflectionGenerator_mem_realSplitPinOrthogonalCover_range :
    globalSheetReflectionGenerator ∈ (realSplitPinOrthogonalCover).range := by
  exact globalSheetReflectionGenerator_mem_realSplitPinOrthogonalImage

theorem realSplitPinOrthogonalCover_negOne_mem_kernel :
    realSplitNegOne ∈ (realSplitPinOrthogonalCover).ker := by
  exact realSplitNegOne_mem_kernel

theorem realSplitNegOne_ne_one :
    realSplitNegOne ≠ 1 := by
  intro h
  have hc := congrArg
    (fun g : realSplitPin55 => ((g : Cl55ˣ) : Cl55)) h
  change ((realSplitNegOne : Cl55ˣ) : Cl55) = 1 at hc
  rw [realSplitNegOne_coe] at hc
  have hchar : CharP Cl55 0 :=
    (RingHom.charP_iff_charP (algebraMap ℝ Cl55) 0).mp inferInstance
  letI : CharP Cl55 0 := hchar
  have htwo : (2 : Cl55) ≠ 0 := by
    intro h2
    have hdiv : 0 ∣ (2 : ℕ) :=
      (CharP.cast_eq_zero_iff Cl55 0 2).mp h2
    simpa using hdiv
  have hsum : (1 : Cl55) + 1 = 0 := neg_eq_iff_add_eq_zero.mp hc
  exact htwo (by simpa [one_add_one_eq_two] using hsum)

/-- The canonical cover API is surjective onto the full native orthogonal group. -/
theorem realSplitPinOrthogonalCover_surjective :
    Function.Surjective realSplitPinOrthogonalCover := by
  exact realSplitPinOrthogonalAction_surjective

/-- The cover has the full native orthogonal group as its range. -/
theorem realSplitPinOrthogonalCover_range_eq_top :
    (realSplitPinOrthogonalCover).range = (⊤ : Subgroup orthogonalGroup55) := by
  exact MonoidHom.range_eq_top.mpr realSplitPinOrthogonalCover_surjective

end InfoGeometry.Clifford.Clifford55
