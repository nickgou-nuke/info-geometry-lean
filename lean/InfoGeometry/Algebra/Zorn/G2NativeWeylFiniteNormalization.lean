import InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
import InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
import InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
import InfoGeometry.Lie.CanonicalZornCartanRootReflections
import InfoGeometry.Lie.CanonicalZornDerivationDimension

namespace InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization

open InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.G2NativeRootIndexAlignment
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornDerivationDimension

def cartanParameterOfWeight : TracelessWeight →ₗ[ℝ] Params where
  toFun k :=
    k.1 0 • parameterUnit 6 + k.1 1 • parameterUnit 13
  map_add' k l := by
    ext i
    by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
      simp [parameterUnit, h6, h13] <;> ring
  map_smul' r k := by
    ext i
    by_cases h6 : i = 6 <;> by_cases h13 : i = 13 <;>
      simp [parameterUnit, h6, h13] <;> ring

theorem cartanParameterOfWeight_apply_6 (k : TracelessWeight) :
    cartanParameterOfWeight k 6 = k.1 0 := by
  simp [cartanParameterOfWeight, parameterUnit]

theorem cartanParameterOfWeight_apply_13 (k : TracelessWeight) :
    cartanParameterOfWeight k 13 = k.1 1 := by
  simp [cartanParameterOfWeight, parameterUnit]
open InfoGeometry.Lie.CanonicalZornCartanRootReflections

def cycleTracelessWeight :
    TracelessWeight →ₗ[ℝ] TracelessWeight where
  toFun k :=
    ⟨![k.1 1, k.1 2, k.1 0], by
      change ∑ i, (![k.1 1, k.1 2, k.1 0] : Fin 3 → ℝ) i = 0
      rw [Fin.sum_univ_three]
      have hk := k.2
      change ∑ i, k.1 i = 0 at hk
      rw [Fin.sum_univ_three] at hk
      simpa [add_assoc, add_left_comm, add_comm] using hk⟩
  map_add' k l := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp
  map_smul' r k := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp

theorem cActionPowNat_one (r : G2Root) :
    cActionPowNat 1 r = cAction r := by
  rfl

theorem cActionPow_one (r : G2Root) :
    cActionPow (1 : ZMod 6) r = cAction r := by
  rfl

theorem weylRootAction_cycle (r : G2Root) :
    G2RootSystemWeylBridge.weylRootAction (1, false) r = cAction r := by
  simp [G2RootSystemWeylBridge.weylRootAction, cActionPow_one]

theorem weylRootAction_reflection (r : G2Root) :
    G2RootSystemWeylBridge.weylRootAction (0, true) r = sAction r := by
  rfl

theorem rootCoordinate_cAction_short_0 :
    rootCoordinate (cAction (RootLength.Short, (0 : ZMod 6))) = 3 := by
  native_decide

theorem rootCoordinate_cAction_short_1 :
    rootCoordinate (cAction (RootLength.Short, (1 : ZMod 6))) = 4 := by
  native_decide

theorem rootCoordinate_cAction_short_2 :
    rootCoordinate (cAction (RootLength.Short, (2 : ZMod 6))) = 8 := by
  native_decide

theorem rootCoordinate_cAction_short_3 :
    rootCoordinate (cAction (RootLength.Short, (3 : ZMod 6))) = 9 := by
  native_decide

theorem rootCoordinate_cAction_short_4 :
    rootCoordinate (cAction (RootLength.Short, (4 : ZMod 6))) = 10 := by
  native_decide

theorem rootCoordinate_cAction_short_5 :
    rootCoordinate (cAction (RootLength.Short, (5 : ZMod 6))) = 0 := by
  native_decide

theorem rootCoordinate_cAction_long_0 :
    rootCoordinate (cAction (RootLength.Long, (0 : ZMod 6))) = 2 := by
  native_decide

theorem rootCoordinate_cAction_long_1 :
    rootCoordinate (cAction (RootLength.Long, (1 : ZMod 6))) = 5 := by
  native_decide

theorem rootCoordinate_cAction_long_2 :
    rootCoordinate (cAction (RootLength.Long, (2 : ZMod 6))) = 7 := by
  native_decide

theorem rootCoordinate_cAction_long_3 :
    rootCoordinate (cAction (RootLength.Long, (3 : ZMod 6))) = 11 := by
  native_decide

theorem rootCoordinate_cAction_long_4 :
    rootCoordinate (cAction (RootLength.Long, (4 : ZMod 6))) = 12 := by
  native_decide

theorem rootCoordinate_cAction_long_5 :
    rootCoordinate (cAction (RootLength.Long, (5 : ZMod 6))) = 1 := by
  native_decide


theorem rootCoordinate_sAction_short_0 :
    rootCoordinate (sAction (RootLength.Short, (0 : ZMod 6))) = 8 := by
  native_decide

theorem rootCoordinate_sAction_short_1 :
    rootCoordinate (sAction (RootLength.Short, (1 : ZMod 6))) = 4 := by
  native_decide

theorem rootCoordinate_sAction_short_2 :
    rootCoordinate (sAction (RootLength.Short, (2 : ZMod 6))) = 3 := by
  native_decide

theorem rootCoordinate_sAction_short_3 :
    rootCoordinate (sAction (RootLength.Short, (3 : ZMod 6))) = 0 := by
  native_decide

theorem rootCoordinate_sAction_short_4 :
    rootCoordinate (sAction (RootLength.Short, (4 : ZMod 6))) = 10 := by
  native_decide

theorem rootCoordinate_sAction_short_5 :
    rootCoordinate (sAction (RootLength.Short, (5 : ZMod 6))) = 9 := by
  native_decide

theorem rootCoordinate_sAction_long_0 :
    rootCoordinate (sAction (RootLength.Long, (0 : ZMod 6))) = 1 := by
  native_decide

theorem rootCoordinate_sAction_long_1 :
    rootCoordinate (sAction (RootLength.Long, (1 : ZMod 6))) = 12 := by
  native_decide

theorem rootCoordinate_sAction_long_2 :
    rootCoordinate (sAction (RootLength.Long, (2 : ZMod 6))) = 11 := by
  native_decide

theorem rootCoordinate_sAction_long_3 :
    rootCoordinate (sAction (RootLength.Long, (3 : ZMod 6))) = 7 := by
  native_decide

theorem rootCoordinate_sAction_long_4 :
    rootCoordinate (sAction (RootLength.Long, (4 : ZMod 6))) = 5 := by
  native_decide

theorem rootCoordinate_sAction_long_5 :
    rootCoordinate (sAction (RootLength.Long, (5 : ZMod 6))) = 2 := by
  native_decide

theorem rootIndexOf_weylRootAction_cycle (r : G2Root) :
    rootIndexOf (G2RootSystemWeylBridge.weylRootAction (1, false) r) =
      rootIndexOf (cAction r) := by
  rw [weylRootAction_cycle]

theorem rootIndexOf_weylRootAction_reflection (r : G2Root) :
    rootIndexOf (G2RootSystemWeylBridge.weylRootAction (0, true) r) =
      rootIndexOf (sAction r) := by
  rw [weylRootAction_reflection]

theorem rootWeight_cycle_short_0 (k : TracelessWeight) :
    rootWeight 0 (cycleTracelessWeight k) = rootWeight 3 k := by
  simp [cycleTracelessWeight, rootWeight, coordWeight]
end InfoGeometry.Algebra.Zorn.G2NativeWeylFiniteNormalization
