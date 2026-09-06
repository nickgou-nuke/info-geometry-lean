import InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
import InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
import InfoGeometry.Algebra.Zorn.G2TwoRootSystem
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteWeightBridge

open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization

def cycleWeight : TracelessWeight →ₗ[ℝ] TracelessWeight where
  toFun k :=
    ⟨![k.1 1, k.1 2, k.1 0], by
      change ∑ i, (![k.1 1, k.1 2, k.1 0] : Fin 3 → ℝ) i = 0
      rw [Fin.sum_univ_three]
      have h := k.2
      change ∑ i, k.1 i = 0 at h
      rw [Fin.sum_univ_three] at h
      simpa [add_assoc, add_left_comm, add_comm] using h⟩
  map_add' k l := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
  map_smul' a k := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp

theorem zmod6_val_succ (j : ZMod 6) :
    (j + 1).val = if j.val = 5 then 0 else j.val + 1 := by
  fin_cases j <;> native_decide

theorem rootWeight_cycle_short_0 (k : TracelessWeight) :
    rootWeight 0 (cycleWeight k) = rootWeight 3 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_short_1 (k : TracelessWeight) :
    rootWeight 3 (cycleWeight k) = -rootWeight 4 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_short_2 (k : TracelessWeight) :
    rootWeight 4 (cycleWeight k) = rootWeight 10 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_short_3 (k : TracelessWeight) :
    rootWeight 8 (cycleWeight k) = -rootWeight 10 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_short_4 (k : TracelessWeight) :
    rootWeight 9 (cycleWeight k) = rootWeight 4 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_short_5 (k : TracelessWeight) :
    rootWeight 10 (cycleWeight k) = -rootWeight 3 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_long_0 (k : TracelessWeight) :
    rootWeight 1 (cycleWeight k) = rootWeight 7 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_long_1 (k : TracelessWeight) :
    rootWeight 2 (cycleWeight k) = rootWeight 5 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_long_2 (k : TracelessWeight) :
    rootWeight 5 (cycleWeight k) = -rootWeight 7 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_long_3 (k : TracelessWeight) :
    rootWeight 7 (cycleWeight k) = rootWeight 11 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_long_4 (k : TracelessWeight) :
    rootWeight 11 (cycleWeight k) = -rootWeight 5 k := by
  simp [cycleWeight, rootWeight, coordWeight]

theorem rootWeight_cycle_long_5 (k : TracelessWeight) :
    rootWeight 12 (cycleWeight k) = rootWeight 2 k := by
  simp [cycleWeight, rootWeight, coordWeight]

/-! The presently defined `cycleWeight` is not the contragredient action of
the native `cAction` on the displayed root labels.  This concrete witness is
kept as an obstruction rather than hiding the mismatch behind an assumed
compatibility theorem. -/
theorem cycleWeight_not_cAction_dual :
    ∃ r : G2Root, ∃ k : TracelessWeight,
      rootWeight (rootCoordinate (cAction r)) (cycleWeight k) ≠
        rootWeight (rootCoordinate r) k := by
  let k : TracelessWeight :=
    ⟨![1, -1, 0], by
      change weightSum (![1, -1, 0] : Fin 3 → ℝ) = 0
      simp [weightSum, Fin.sum_univ_three]⟩
  refine ⟨(RootLength.Short, (0 : ZMod 6)), k, ?_⟩
  rw [rootCoordinate_cAction_short_0]
  change rootWeight 3 (cycleWeight k) ≠ rootWeight 0 k
  simp [k, cycleWeight, rootWeight, coordWeight]
