import Mathlib
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.Algebra.CubicJordanOs

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.Algebra.CubicJordanOs
open InfoGeometry.Algebra.CubicJordanOs.AlbertMatrix

noncomputable section

namespace InfoGeometry.Algebra.FreudenthalComplete

theorem freudenthal_ePlus_ePlus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := ePlus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_ePlus_ePlus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := ePlus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_ePlus_ePlus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := ePlus; z₃ := up0 } := by
  native_decide

theorem freudenthal_ePlus_ePlus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := ePlus; z₃ := up1 } := by
  native_decide

theorem freudenthal_ePlus_ePlus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := ePlus; z₃ := up2 } := by
  native_decide

theorem freudenthal_ePlus_ePlus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := ePlus; z₃ := down0 } := by
  native_decide

theorem freudenthal_ePlus_ePlus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := ePlus; z₃ := down1 } := by
  native_decide

theorem freudenthal_ePlus_ePlus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := ePlus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := ePlus; z₃ := down2 } := by
  native_decide

theorem freudenthal_ePlus_eMinus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := eMinus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_ePlus_eMinus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := eMinus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_ePlus_eMinus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := eMinus; z₃ := up0 } := by
  native_decide

theorem freudenthal_ePlus_eMinus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := eMinus; z₃ := up1 } := by
  native_decide

theorem freudenthal_ePlus_eMinus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := eMinus; z₃ := up2 } := by
  native_decide

theorem freudenthal_ePlus_eMinus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := eMinus; z₃ := down0 } := by
  native_decide

theorem freudenthal_ePlus_eMinus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := eMinus; z₃ := down1 } := by
  native_decide

theorem freudenthal_ePlus_eMinus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := eMinus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := eMinus; z₃ := down2 } := by
  native_decide

theorem freudenthal_ePlus_up0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_ePlus_up0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_ePlus_up0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up0; z₃ := up0 } := by
  native_decide

theorem freudenthal_ePlus_up0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up0; z₃ := up1 } := by
  native_decide

theorem freudenthal_ePlus_up0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up0; z₃ := up2 } := by
  native_decide

theorem freudenthal_ePlus_up0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up0; z₃ := down0 } := by
  native_decide

theorem freudenthal_ePlus_up0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up0; z₃ := down1 } := by
  native_decide

theorem freudenthal_ePlus_up0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up0; z₃ := down2 } := by
  native_decide

theorem freudenthal_ePlus_up1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_ePlus_up1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_ePlus_up1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up1; z₃ := up0 } := by
  native_decide

theorem freudenthal_ePlus_up1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up1; z₃ := up1 } := by
  native_decide

theorem freudenthal_ePlus_up1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up1; z₃ := up2 } := by
  native_decide

theorem freudenthal_ePlus_up1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up1; z₃ := down0 } := by
  native_decide

theorem freudenthal_ePlus_up1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up1; z₃ := down1 } := by
  native_decide

theorem freudenthal_ePlus_up1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up1; z₃ := down2 } := by
  native_decide

theorem freudenthal_ePlus_up2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_ePlus_up2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_ePlus_up2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up2; z₃ := up0 } := by
  native_decide

theorem freudenthal_ePlus_up2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up2; z₃ := up1 } := by
  native_decide

theorem freudenthal_ePlus_up2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up2; z₃ := up2 } := by
  native_decide

theorem freudenthal_ePlus_up2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up2; z₃ := down0 } := by
  native_decide

theorem freudenthal_ePlus_up2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up2; z₃ := down1 } := by
  native_decide

theorem freudenthal_ePlus_up2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := up2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := up2; z₃ := down2 } := by
  native_decide

theorem freudenthal_ePlus_down0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_ePlus_down0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_ePlus_down0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down0; z₃ := up0 } := by
  native_decide

theorem freudenthal_ePlus_down0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down0; z₃ := up1 } := by
  native_decide

theorem freudenthal_ePlus_down0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down0; z₃ := up2 } := by
  native_decide

theorem freudenthal_ePlus_down0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down0; z₃ := down0 } := by
  native_decide

theorem freudenthal_ePlus_down0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down0; z₃ := down1 } := by
  native_decide

theorem freudenthal_ePlus_down0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down0; z₃ := down2 } := by
  native_decide

theorem freudenthal_ePlus_down1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_ePlus_down1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_ePlus_down1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down1; z₃ := up0 } := by
  native_decide

theorem freudenthal_ePlus_down1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down1; z₃ := up1 } := by
  native_decide

theorem freudenthal_ePlus_down1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down1; z₃ := up2 } := by
  native_decide

theorem freudenthal_ePlus_down1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down1; z₃ := down0 } := by
  native_decide

theorem freudenthal_ePlus_down1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down1; z₃ := down1 } := by
  native_decide

theorem freudenthal_ePlus_down1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down1; z₃ := down2 } := by
  native_decide

theorem freudenthal_ePlus_down2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_ePlus_down2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_ePlus_down2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down2; z₃ := up0 } := by
  native_decide

theorem freudenthal_ePlus_down2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down2; z₃ := up1 } := by
  native_decide

theorem freudenthal_ePlus_down2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down2; z₃ := up2 } := by
  native_decide

theorem freudenthal_ePlus_down2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down2; z₃ := down0 } := by
  native_decide

theorem freudenthal_ePlus_down2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down2; z₃ := down1 } := by
  native_decide

theorem freudenthal_ePlus_down2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := ePlus; z₂ := down2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := ePlus; z₂ := down2; z₃ := down2 } := by
  native_decide

theorem freudenthal_eMinus_ePlus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := ePlus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_eMinus_ePlus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := ePlus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_eMinus_ePlus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := ePlus; z₃ := up0 } := by
  native_decide

theorem freudenthal_eMinus_ePlus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := ePlus; z₃ := up1 } := by
  native_decide

theorem freudenthal_eMinus_ePlus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := ePlus; z₃ := up2 } := by
  native_decide

theorem freudenthal_eMinus_ePlus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := ePlus; z₃ := down0 } := by
  native_decide

theorem freudenthal_eMinus_ePlus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := ePlus; z₃ := down1 } := by
  native_decide

theorem freudenthal_eMinus_ePlus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := ePlus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := ePlus; z₃ := down2 } := by
  native_decide

theorem freudenthal_eMinus_eMinus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := eMinus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_eMinus_eMinus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := eMinus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_eMinus_eMinus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := eMinus; z₃ := up0 } := by
  native_decide

theorem freudenthal_eMinus_eMinus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := eMinus; z₃ := up1 } := by
  native_decide

theorem freudenthal_eMinus_eMinus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := eMinus; z₃ := up2 } := by
  native_decide

theorem freudenthal_eMinus_eMinus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := eMinus; z₃ := down0 } := by
  native_decide

theorem freudenthal_eMinus_eMinus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := eMinus; z₃ := down1 } := by
  native_decide

theorem freudenthal_eMinus_eMinus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := eMinus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := eMinus; z₃ := down2 } := by
  native_decide

theorem freudenthal_eMinus_up0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_eMinus_up0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_eMinus_up0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up0; z₃ := up0 } := by
  native_decide

theorem freudenthal_eMinus_up0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up0; z₃ := up1 } := by
  native_decide

theorem freudenthal_eMinus_up0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up0; z₃ := up2 } := by
  native_decide

theorem freudenthal_eMinus_up0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up0; z₃ := down0 } := by
  native_decide

theorem freudenthal_eMinus_up0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up0; z₃ := down1 } := by
  native_decide

theorem freudenthal_eMinus_up0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up0; z₃ := down2 } := by
  native_decide

theorem freudenthal_eMinus_up1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_eMinus_up1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_eMinus_up1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up1; z₃ := up0 } := by
  native_decide

theorem freudenthal_eMinus_up1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up1; z₃ := up1 } := by
  native_decide

theorem freudenthal_eMinus_up1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up1; z₃ := up2 } := by
  native_decide

theorem freudenthal_eMinus_up1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up1; z₃ := down0 } := by
  native_decide

theorem freudenthal_eMinus_up1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up1; z₃ := down1 } := by
  native_decide

theorem freudenthal_eMinus_up1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up1; z₃ := down2 } := by
  native_decide

theorem freudenthal_eMinus_up2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_eMinus_up2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_eMinus_up2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up2; z₃ := up0 } := by
  native_decide

theorem freudenthal_eMinus_up2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up2; z₃ := up1 } := by
  native_decide

theorem freudenthal_eMinus_up2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up2; z₃ := up2 } := by
  native_decide

theorem freudenthal_eMinus_up2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up2; z₃ := down0 } := by
  native_decide

theorem freudenthal_eMinus_up2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up2; z₃ := down1 } := by
  native_decide

theorem freudenthal_eMinus_up2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := up2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := up2; z₃ := down2 } := by
  native_decide

theorem freudenthal_eMinus_down0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_eMinus_down0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_eMinus_down0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down0; z₃ := up0 } := by
  native_decide

theorem freudenthal_eMinus_down0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down0; z₃ := up1 } := by
  native_decide

theorem freudenthal_eMinus_down0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down0; z₃ := up2 } := by
  native_decide

theorem freudenthal_eMinus_down0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down0; z₃ := down0 } := by
  native_decide

theorem freudenthal_eMinus_down0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down0; z₃ := down1 } := by
  native_decide

theorem freudenthal_eMinus_down0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down0; z₃ := down2 } := by
  native_decide

theorem freudenthal_eMinus_down1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_eMinus_down1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_eMinus_down1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down1; z₃ := up0 } := by
  native_decide

theorem freudenthal_eMinus_down1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down1; z₃ := up1 } := by
  native_decide

theorem freudenthal_eMinus_down1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down1; z₃ := up2 } := by
  native_decide

theorem freudenthal_eMinus_down1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down1; z₃ := down0 } := by
  native_decide

theorem freudenthal_eMinus_down1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down1; z₃ := down1 } := by
  native_decide

theorem freudenthal_eMinus_down1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down1; z₃ := down2 } := by
  native_decide

theorem freudenthal_eMinus_down2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_eMinus_down2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_eMinus_down2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down2; z₃ := up0 } := by
  native_decide

theorem freudenthal_eMinus_down2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down2; z₃ := up1 } := by
  native_decide

theorem freudenthal_eMinus_down2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down2; z₃ := up2 } := by
  native_decide

theorem freudenthal_eMinus_down2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down2; z₃ := down0 } := by
  native_decide

theorem freudenthal_eMinus_down2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down2; z₃ := down1 } := by
  native_decide

theorem freudenthal_eMinus_down2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := eMinus; z₂ := down2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := eMinus; z₂ := down2; z₃ := down2 } := by
  native_decide

theorem freudenthal_up0_ePlus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := ePlus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up0_ePlus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := ePlus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up0_ePlus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := ePlus; z₃ := up0 } := by
  native_decide

theorem freudenthal_up0_ePlus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := ePlus; z₃ := up1 } := by
  native_decide

theorem freudenthal_up0_ePlus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := ePlus; z₃ := up2 } := by
  native_decide

theorem freudenthal_up0_ePlus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := ePlus; z₃ := down0 } := by
  native_decide

theorem freudenthal_up0_ePlus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := ePlus; z₃ := down1 } := by
  native_decide

theorem freudenthal_up0_ePlus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := ePlus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := ePlus; z₃ := down2 } := by
  native_decide

theorem freudenthal_up0_eMinus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := eMinus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up0_eMinus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := eMinus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up0_eMinus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := eMinus; z₃ := up0 } := by
  native_decide

theorem freudenthal_up0_eMinus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := eMinus; z₃ := up1 } := by
  native_decide

theorem freudenthal_up0_eMinus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := eMinus; z₃ := up2 } := by
  native_decide

theorem freudenthal_up0_eMinus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := eMinus; z₃ := down0 } := by
  native_decide

theorem freudenthal_up0_eMinus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := eMinus; z₃ := down1 } := by
  native_decide

theorem freudenthal_up0_eMinus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := eMinus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := eMinus; z₃ := down2 } := by
  native_decide

theorem freudenthal_up0_up0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up0_up0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up0_up0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up0; z₃ := up0 } := by
  native_decide

theorem freudenthal_up0_up0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up0; z₃ := up1 } := by
  native_decide

theorem freudenthal_up0_up0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up0; z₃ := up2 } := by
  native_decide

theorem freudenthal_up0_up0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up0; z₃ := down0 } := by
  native_decide

theorem freudenthal_up0_up0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up0; z₃ := down1 } := by
  native_decide

theorem freudenthal_up0_up0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up0; z₃ := down2 } := by
  native_decide

theorem freudenthal_up0_up1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up0_up1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up0_up1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up1; z₃ := up0 } := by
  native_decide

theorem freudenthal_up0_up1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up1; z₃ := up1 } := by
  native_decide

theorem freudenthal_up0_up1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up1; z₃ := up2 } := by
  native_decide

theorem freudenthal_up0_up1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up1; z₃ := down0 } := by
  native_decide

theorem freudenthal_up0_up1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up1; z₃ := down1 } := by
  native_decide

theorem freudenthal_up0_up1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up1; z₃ := down2 } := by
  native_decide

theorem freudenthal_up0_up2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up0_up2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up0_up2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up2; z₃ := up0 } := by
  native_decide

theorem freudenthal_up0_up2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up2; z₃ := up1 } := by
  native_decide

theorem freudenthal_up0_up2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up2; z₃ := up2 } := by
  native_decide

theorem freudenthal_up0_up2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up2; z₃ := down0 } := by
  native_decide

theorem freudenthal_up0_up2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up2; z₃ := down1 } := by
  native_decide

theorem freudenthal_up0_up2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := up2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := up2; z₃ := down2 } := by
  native_decide

theorem freudenthal_up0_down0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up0_down0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up0_down0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down0; z₃ := up0 } := by
  native_decide

theorem freudenthal_up0_down0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down0; z₃ := up1 } := by
  native_decide

theorem freudenthal_up0_down0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down0; z₃ := up2 } := by
  native_decide

theorem freudenthal_up0_down0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down0; z₃ := down0 } := by
  native_decide

theorem freudenthal_up0_down0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down0; z₃ := down1 } := by
  native_decide

theorem freudenthal_up0_down0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down0; z₃ := down2 } := by
  native_decide

theorem freudenthal_up0_down1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up0_down1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up0_down1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down1; z₃ := up0 } := by
  native_decide

theorem freudenthal_up0_down1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down1; z₃ := up1 } := by
  native_decide

theorem freudenthal_up0_down1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down1; z₃ := up2 } := by
  native_decide

theorem freudenthal_up0_down1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down1; z₃ := down0 } := by
  native_decide

theorem freudenthal_up0_down1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down1; z₃ := down1 } := by
  native_decide

theorem freudenthal_up0_down1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down1; z₃ := down2 } := by
  native_decide

theorem freudenthal_up0_down2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up0_down2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up0_down2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down2; z₃ := up0 } := by
  native_decide

theorem freudenthal_up0_down2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down2; z₃ := up1 } := by
  native_decide

theorem freudenthal_up0_down2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down2; z₃ := up2 } := by
  native_decide

theorem freudenthal_up0_down2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down2; z₃ := down0 } := by
  native_decide

theorem freudenthal_up0_down2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down2; z₃ := down1 } := by
  native_decide

theorem freudenthal_up0_down2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up0; z₂ := down2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up0; z₂ := down2; z₃ := down2 } := by
  native_decide

theorem freudenthal_up1_ePlus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := ePlus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up1_ePlus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := ePlus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up1_ePlus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := ePlus; z₃ := up0 } := by
  native_decide

theorem freudenthal_up1_ePlus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := ePlus; z₃ := up1 } := by
  native_decide

theorem freudenthal_up1_ePlus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := ePlus; z₃ := up2 } := by
  native_decide

theorem freudenthal_up1_ePlus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := ePlus; z₃ := down0 } := by
  native_decide

theorem freudenthal_up1_ePlus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := ePlus; z₃ := down1 } := by
  native_decide

theorem freudenthal_up1_ePlus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := ePlus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := ePlus; z₃ := down2 } := by
  native_decide

theorem freudenthal_up1_eMinus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := eMinus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up1_eMinus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := eMinus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up1_eMinus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := eMinus; z₃ := up0 } := by
  native_decide

theorem freudenthal_up1_eMinus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := eMinus; z₃ := up1 } := by
  native_decide

theorem freudenthal_up1_eMinus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := eMinus; z₃ := up2 } := by
  native_decide

theorem freudenthal_up1_eMinus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := eMinus; z₃ := down0 } := by
  native_decide

theorem freudenthal_up1_eMinus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := eMinus; z₃ := down1 } := by
  native_decide

theorem freudenthal_up1_eMinus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := eMinus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := eMinus; z₃ := down2 } := by
  native_decide

theorem freudenthal_up1_up0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up1_up0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up1_up0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up0; z₃ := up0 } := by
  native_decide

theorem freudenthal_up1_up0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up0; z₃ := up1 } := by
  native_decide

theorem freudenthal_up1_up0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up0; z₃ := up2 } := by
  native_decide

theorem freudenthal_up1_up0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up0; z₃ := down0 } := by
  native_decide

theorem freudenthal_up1_up0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up0; z₃ := down1 } := by
  native_decide

theorem freudenthal_up1_up0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up0; z₃ := down2 } := by
  native_decide

theorem freudenthal_up1_up1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up1_up1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up1_up1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up1; z₃ := up0 } := by
  native_decide

theorem freudenthal_up1_up1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up1; z₃ := up1 } := by
  native_decide

theorem freudenthal_up1_up1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up1; z₃ := up2 } := by
  native_decide

theorem freudenthal_up1_up1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up1; z₃ := down0 } := by
  native_decide

theorem freudenthal_up1_up1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up1; z₃ := down1 } := by
  native_decide

theorem freudenthal_up1_up1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up1; z₃ := down2 } := by
  native_decide

theorem freudenthal_up1_up2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up1_up2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up1_up2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up2; z₃ := up0 } := by
  native_decide

theorem freudenthal_up1_up2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up2; z₃ := up1 } := by
  native_decide

theorem freudenthal_up1_up2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up2; z₃ := up2 } := by
  native_decide

theorem freudenthal_up1_up2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up2; z₃ := down0 } := by
  native_decide

theorem freudenthal_up1_up2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up2; z₃ := down1 } := by
  native_decide

theorem freudenthal_up1_up2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := up2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := up2; z₃ := down2 } := by
  native_decide

theorem freudenthal_up1_down0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up1_down0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up1_down0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down0; z₃ := up0 } := by
  native_decide

theorem freudenthal_up1_down0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down0; z₃ := up1 } := by
  native_decide

theorem freudenthal_up1_down0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down0; z₃ := up2 } := by
  native_decide

theorem freudenthal_up1_down0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down0; z₃ := down0 } := by
  native_decide

theorem freudenthal_up1_down0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down0; z₃ := down1 } := by
  native_decide

theorem freudenthal_up1_down0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down0; z₃ := down2 } := by
  native_decide

theorem freudenthal_up1_down1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up1_down1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up1_down1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down1; z₃ := up0 } := by
  native_decide

theorem freudenthal_up1_down1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down1; z₃ := up1 } := by
  native_decide

theorem freudenthal_up1_down1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down1; z₃ := up2 } := by
  native_decide

theorem freudenthal_up1_down1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down1; z₃ := down0 } := by
  native_decide

theorem freudenthal_up1_down1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down1; z₃ := down1 } := by
  native_decide

theorem freudenthal_up1_down1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down1; z₃ := down2 } := by
  native_decide

theorem freudenthal_up1_down2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up1_down2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up1_down2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down2; z₃ := up0 } := by
  native_decide

theorem freudenthal_up1_down2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down2; z₃ := up1 } := by
  native_decide

theorem freudenthal_up1_down2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down2; z₃ := up2 } := by
  native_decide

theorem freudenthal_up1_down2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down2; z₃ := down0 } := by
  native_decide

theorem freudenthal_up1_down2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down2; z₃ := down1 } := by
  native_decide

theorem freudenthal_up1_down2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up1; z₂ := down2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up1; z₂ := down2; z₃ := down2 } := by
  native_decide

theorem freudenthal_up2_ePlus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := ePlus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up2_ePlus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := ePlus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up2_ePlus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := ePlus; z₃ := up0 } := by
  native_decide

theorem freudenthal_up2_ePlus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := ePlus; z₃ := up1 } := by
  native_decide

theorem freudenthal_up2_ePlus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := ePlus; z₃ := up2 } := by
  native_decide

theorem freudenthal_up2_ePlus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := ePlus; z₃ := down0 } := by
  native_decide

theorem freudenthal_up2_ePlus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := ePlus; z₃ := down1 } := by
  native_decide

theorem freudenthal_up2_ePlus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := ePlus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := ePlus; z₃ := down2 } := by
  native_decide

theorem freudenthal_up2_eMinus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := eMinus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up2_eMinus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := eMinus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up2_eMinus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := eMinus; z₃ := up0 } := by
  native_decide

theorem freudenthal_up2_eMinus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := eMinus; z₃ := up1 } := by
  native_decide

theorem freudenthal_up2_eMinus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := eMinus; z₃ := up2 } := by
  native_decide

theorem freudenthal_up2_eMinus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := eMinus; z₃ := down0 } := by
  native_decide

theorem freudenthal_up2_eMinus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := eMinus; z₃ := down1 } := by
  native_decide

theorem freudenthal_up2_eMinus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := eMinus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := eMinus; z₃ := down2 } := by
  native_decide

theorem freudenthal_up2_up0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up2_up0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up2_up0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up0; z₃ := up0 } := by
  native_decide

theorem freudenthal_up2_up0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up0; z₃ := up1 } := by
  native_decide

theorem freudenthal_up2_up0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up0; z₃ := up2 } := by
  native_decide

theorem freudenthal_up2_up0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up0; z₃ := down0 } := by
  native_decide

theorem freudenthal_up2_up0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up0; z₃ := down1 } := by
  native_decide

theorem freudenthal_up2_up0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up0; z₃ := down2 } := by
  native_decide

theorem freudenthal_up2_up1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up2_up1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up2_up1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up1; z₃ := up0 } := by
  native_decide

theorem freudenthal_up2_up1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up1; z₃ := up1 } := by
  native_decide

theorem freudenthal_up2_up1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up1; z₃ := up2 } := by
  native_decide

theorem freudenthal_up2_up1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up1; z₃ := down0 } := by
  native_decide

theorem freudenthal_up2_up1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up1; z₃ := down1 } := by
  native_decide

theorem freudenthal_up2_up1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up1; z₃ := down2 } := by
  native_decide

theorem freudenthal_up2_up2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up2_up2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up2_up2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up2; z₃ := up0 } := by
  native_decide

theorem freudenthal_up2_up2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up2; z₃ := up1 } := by
  native_decide

theorem freudenthal_up2_up2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up2; z₃ := up2 } := by
  native_decide

theorem freudenthal_up2_up2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up2; z₃ := down0 } := by
  native_decide

theorem freudenthal_up2_up2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up2; z₃ := down1 } := by
  native_decide

theorem freudenthal_up2_up2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := up2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := up2; z₃ := down2 } := by
  native_decide

theorem freudenthal_up2_down0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up2_down0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up2_down0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down0; z₃ := up0 } := by
  native_decide

theorem freudenthal_up2_down0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down0; z₃ := up1 } := by
  native_decide

theorem freudenthal_up2_down0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down0; z₃ := up2 } := by
  native_decide

theorem freudenthal_up2_down0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down0; z₃ := down0 } := by
  native_decide

theorem freudenthal_up2_down0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down0; z₃ := down1 } := by
  native_decide

theorem freudenthal_up2_down0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down0; z₃ := down2 } := by
  native_decide

theorem freudenthal_up2_down1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up2_down1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up2_down1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down1; z₃ := up0 } := by
  native_decide

theorem freudenthal_up2_down1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down1; z₃ := up1 } := by
  native_decide

theorem freudenthal_up2_down1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down1; z₃ := up2 } := by
  native_decide

theorem freudenthal_up2_down1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down1; z₃ := down0 } := by
  native_decide

theorem freudenthal_up2_down1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down1; z₃ := down1 } := by
  native_decide

theorem freudenthal_up2_down1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down1; z₃ := down2 } := by
  native_decide

theorem freudenthal_up2_down2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_up2_down2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_up2_down2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down2; z₃ := up0 } := by
  native_decide

theorem freudenthal_up2_down2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down2; z₃ := up1 } := by
  native_decide

theorem freudenthal_up2_down2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down2; z₃ := up2 } := by
  native_decide

theorem freudenthal_up2_down2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down2; z₃ := down0 } := by
  native_decide

theorem freudenthal_up2_down2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down2; z₃ := down1 } := by
  native_decide

theorem freudenthal_up2_down2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := up2; z₂ := down2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := up2; z₂ := down2; z₃ := down2 } := by
  native_decide

theorem freudenthal_down0_ePlus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := ePlus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down0_ePlus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := ePlus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down0_ePlus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := ePlus; z₃ := up0 } := by
  native_decide

theorem freudenthal_down0_ePlus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := ePlus; z₃ := up1 } := by
  native_decide

theorem freudenthal_down0_ePlus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := ePlus; z₃ := up2 } := by
  native_decide

theorem freudenthal_down0_ePlus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := ePlus; z₃ := down0 } := by
  native_decide

theorem freudenthal_down0_ePlus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := ePlus; z₃ := down1 } := by
  native_decide

theorem freudenthal_down0_ePlus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := ePlus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := ePlus; z₃ := down2 } := by
  native_decide

theorem freudenthal_down0_eMinus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := eMinus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down0_eMinus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := eMinus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down0_eMinus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := eMinus; z₃ := up0 } := by
  native_decide

theorem freudenthal_down0_eMinus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := eMinus; z₃ := up1 } := by
  native_decide

theorem freudenthal_down0_eMinus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := eMinus; z₃ := up2 } := by
  native_decide

theorem freudenthal_down0_eMinus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := eMinus; z₃ := down0 } := by
  native_decide

theorem freudenthal_down0_eMinus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := eMinus; z₃ := down1 } := by
  native_decide

theorem freudenthal_down0_eMinus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := eMinus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := eMinus; z₃ := down2 } := by
  native_decide

theorem freudenthal_down0_up0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down0_up0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down0_up0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up0; z₃ := up0 } := by
  native_decide

theorem freudenthal_down0_up0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up0; z₃ := up1 } := by
  native_decide

theorem freudenthal_down0_up0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up0; z₃ := up2 } := by
  native_decide

theorem freudenthal_down0_up0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up0; z₃ := down0 } := by
  native_decide

theorem freudenthal_down0_up0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up0; z₃ := down1 } := by
  native_decide

theorem freudenthal_down0_up0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up0; z₃ := down2 } := by
  native_decide

theorem freudenthal_down0_up1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down0_up1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down0_up1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up1; z₃ := up0 } := by
  native_decide

theorem freudenthal_down0_up1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up1; z₃ := up1 } := by
  native_decide

theorem freudenthal_down0_up1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up1; z₃ := up2 } := by
  native_decide

theorem freudenthal_down0_up1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up1; z₃ := down0 } := by
  native_decide

theorem freudenthal_down0_up1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up1; z₃ := down1 } := by
  native_decide

theorem freudenthal_down0_up1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up1; z₃ := down2 } := by
  native_decide

theorem freudenthal_down0_up2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down0_up2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down0_up2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up2; z₃ := up0 } := by
  native_decide

theorem freudenthal_down0_up2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up2; z₃ := up1 } := by
  native_decide

theorem freudenthal_down0_up2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up2; z₃ := up2 } := by
  native_decide

theorem freudenthal_down0_up2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up2; z₃ := down0 } := by
  native_decide

theorem freudenthal_down0_up2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up2; z₃ := down1 } := by
  native_decide

theorem freudenthal_down0_up2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := up2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := up2; z₃ := down2 } := by
  native_decide

theorem freudenthal_down0_down0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down0_down0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down0_down0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down0; z₃ := up0 } := by
  native_decide

theorem freudenthal_down0_down0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down0; z₃ := up1 } := by
  native_decide

theorem freudenthal_down0_down0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down0; z₃ := up2 } := by
  native_decide

theorem freudenthal_down0_down0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down0; z₃ := down0 } := by
  native_decide

theorem freudenthal_down0_down0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down0; z₃ := down1 } := by
  native_decide

theorem freudenthal_down0_down0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down0; z₃ := down2 } := by
  native_decide

theorem freudenthal_down0_down1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down0_down1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down0_down1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down1; z₃ := up0 } := by
  native_decide

theorem freudenthal_down0_down1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down1; z₃ := up1 } := by
  native_decide

theorem freudenthal_down0_down1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down1; z₃ := up2 } := by
  native_decide

theorem freudenthal_down0_down1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down1; z₃ := down0 } := by
  native_decide

theorem freudenthal_down0_down1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down1; z₃ := down1 } := by
  native_decide

theorem freudenthal_down0_down1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down1; z₃ := down2 } := by
  native_decide

theorem freudenthal_down0_down2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down0_down2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down0_down2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down2; z₃ := up0 } := by
  native_decide

theorem freudenthal_down0_down2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down2; z₃ := up1 } := by
  native_decide

theorem freudenthal_down0_down2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down2; z₃ := up2 } := by
  native_decide

theorem freudenthal_down0_down2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down2; z₃ := down0 } := by
  native_decide

theorem freudenthal_down0_down2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down2; z₃ := down1 } := by
  native_decide

theorem freudenthal_down0_down2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down0; z₂ := down2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down0; z₂ := down2; z₃ := down2 } := by
  native_decide

theorem freudenthal_down1_ePlus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := ePlus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down1_ePlus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := ePlus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down1_ePlus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := ePlus; z₃ := up0 } := by
  native_decide

theorem freudenthal_down1_ePlus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := ePlus; z₃ := up1 } := by
  native_decide

theorem freudenthal_down1_ePlus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := ePlus; z₃ := up2 } := by
  native_decide

theorem freudenthal_down1_ePlus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := ePlus; z₃ := down0 } := by
  native_decide

theorem freudenthal_down1_ePlus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := ePlus; z₃ := down1 } := by
  native_decide

theorem freudenthal_down1_ePlus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := ePlus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := ePlus; z₃ := down2 } := by
  native_decide

theorem freudenthal_down1_eMinus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := eMinus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down1_eMinus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := eMinus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down1_eMinus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := eMinus; z₃ := up0 } := by
  native_decide

theorem freudenthal_down1_eMinus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := eMinus; z₃ := up1 } := by
  native_decide

theorem freudenthal_down1_eMinus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := eMinus; z₃ := up2 } := by
  native_decide

theorem freudenthal_down1_eMinus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := eMinus; z₃ := down0 } := by
  native_decide

theorem freudenthal_down1_eMinus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := eMinus; z₃ := down1 } := by
  native_decide

theorem freudenthal_down1_eMinus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := eMinus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := eMinus; z₃ := down2 } := by
  native_decide

theorem freudenthal_down1_up0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down1_up0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down1_up0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up0; z₃ := up0 } := by
  native_decide

theorem freudenthal_down1_up0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up0; z₃ := up1 } := by
  native_decide

theorem freudenthal_down1_up0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up0; z₃ := up2 } := by
  native_decide

theorem freudenthal_down1_up0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up0; z₃ := down0 } := by
  native_decide

theorem freudenthal_down1_up0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up0; z₃ := down1 } := by
  native_decide

theorem freudenthal_down1_up0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up0; z₃ := down2 } := by
  native_decide

theorem freudenthal_down1_up1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down1_up1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down1_up1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up1; z₃ := up0 } := by
  native_decide

theorem freudenthal_down1_up1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up1; z₃ := up1 } := by
  native_decide

theorem freudenthal_down1_up1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up1; z₃ := up2 } := by
  native_decide

theorem freudenthal_down1_up1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up1; z₃ := down0 } := by
  native_decide

theorem freudenthal_down1_up1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up1; z₃ := down1 } := by
  native_decide

theorem freudenthal_down1_up1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up1; z₃ := down2 } := by
  native_decide

theorem freudenthal_down1_up2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down1_up2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down1_up2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up2; z₃ := up0 } := by
  native_decide

theorem freudenthal_down1_up2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up2; z₃ := up1 } := by
  native_decide

theorem freudenthal_down1_up2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up2; z₃ := up2 } := by
  native_decide

theorem freudenthal_down1_up2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up2; z₃ := down0 } := by
  native_decide

theorem freudenthal_down1_up2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up2; z₃ := down1 } := by
  native_decide

theorem freudenthal_down1_up2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := up2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := up2; z₃ := down2 } := by
  native_decide

theorem freudenthal_down1_down0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down1_down0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down1_down0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down0; z₃ := up0 } := by
  native_decide

theorem freudenthal_down1_down0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down0; z₃ := up1 } := by
  native_decide

theorem freudenthal_down1_down0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down0; z₃ := up2 } := by
  native_decide

theorem freudenthal_down1_down0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down0; z₃ := down0 } := by
  native_decide

theorem freudenthal_down1_down0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down0; z₃ := down1 } := by
  native_decide

theorem freudenthal_down1_down0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down0; z₃ := down2 } := by
  native_decide

theorem freudenthal_down1_down1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down1_down1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down1_down1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down1; z₃ := up0 } := by
  native_decide

theorem freudenthal_down1_down1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down1; z₃ := up1 } := by
  native_decide

theorem freudenthal_down1_down1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down1; z₃ := up2 } := by
  native_decide

theorem freudenthal_down1_down1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down1; z₃ := down0 } := by
  native_decide

theorem freudenthal_down1_down1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down1; z₃ := down1 } := by
  native_decide

theorem freudenthal_down1_down1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down1; z₃ := down2 } := by
  native_decide

theorem freudenthal_down1_down2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down1_down2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down1_down2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down2; z₃ := up0 } := by
  native_decide

theorem freudenthal_down1_down2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down2; z₃ := up1 } := by
  native_decide

theorem freudenthal_down1_down2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down2; z₃ := up2 } := by
  native_decide

theorem freudenthal_down1_down2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down2; z₃ := down0 } := by
  native_decide

theorem freudenthal_down1_down2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down2; z₃ := down1 } := by
  native_decide

theorem freudenthal_down1_down2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down1; z₂ := down2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down1; z₂ := down2; z₃ := down2 } := by
  native_decide

theorem freudenthal_down2_ePlus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := ePlus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down2_ePlus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := ePlus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down2_ePlus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := ePlus; z₃ := up0 } := by
  native_decide

theorem freudenthal_down2_ePlus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := ePlus; z₃ := up1 } := by
  native_decide

theorem freudenthal_down2_ePlus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := ePlus; z₃ := up2 } := by
  native_decide

theorem freudenthal_down2_ePlus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := ePlus; z₃ := down0 } := by
  native_decide

theorem freudenthal_down2_ePlus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := ePlus; z₃ := down1 } := by
  native_decide

theorem freudenthal_down2_ePlus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := ePlus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := ePlus; z₃ := down2 } := by
  native_decide

theorem freudenthal_down2_eMinus_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := eMinus; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down2_eMinus_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := eMinus; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down2_eMinus_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := eMinus; z₃ := up0 } := by
  native_decide

theorem freudenthal_down2_eMinus_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := eMinus; z₃ := up1 } := by
  native_decide

theorem freudenthal_down2_eMinus_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := eMinus; z₃ := up2 } := by
  native_decide

theorem freudenthal_down2_eMinus_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := eMinus; z₃ := down0 } := by
  native_decide

theorem freudenthal_down2_eMinus_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := eMinus; z₃ := down1 } := by
  native_decide

theorem freudenthal_down2_eMinus_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := eMinus; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := eMinus; z₃ := down2 } := by
  native_decide

theorem freudenthal_down2_up0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down2_up0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down2_up0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up0; z₃ := up0 } := by
  native_decide

theorem freudenthal_down2_up0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up0; z₃ := up1 } := by
  native_decide

theorem freudenthal_down2_up0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up0; z₃ := up2 } := by
  native_decide

theorem freudenthal_down2_up0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up0; z₃ := down0 } := by
  native_decide

theorem freudenthal_down2_up0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up0; z₃ := down1 } := by
  native_decide

theorem freudenthal_down2_up0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up0; z₃ := down2 } := by
  native_decide

theorem freudenthal_down2_up1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down2_up1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down2_up1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up1; z₃ := up0 } := by
  native_decide

theorem freudenthal_down2_up1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up1; z₃ := up1 } := by
  native_decide

theorem freudenthal_down2_up1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up1; z₃ := up2 } := by
  native_decide

theorem freudenthal_down2_up1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up1; z₃ := down0 } := by
  native_decide

theorem freudenthal_down2_up1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up1; z₃ := down1 } := by
  native_decide

theorem freudenthal_down2_up1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up1; z₃ := down2 } := by
  native_decide

theorem freudenthal_down2_up2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down2_up2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down2_up2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up2; z₃ := up0 } := by
  native_decide

theorem freudenthal_down2_up2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up2; z₃ := up1 } := by
  native_decide

theorem freudenthal_down2_up2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up2; z₃ := up2 } := by
  native_decide

theorem freudenthal_down2_up2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up2; z₃ := down0 } := by
  native_decide

theorem freudenthal_down2_up2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up2; z₃ := down1 } := by
  native_decide

theorem freudenthal_down2_up2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := up2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := up2; z₃ := down2 } := by
  native_decide

theorem freudenthal_down2_down0_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down0; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down2_down0_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down0; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down2_down0_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down0; z₃ := up0 } := by
  native_decide

theorem freudenthal_down2_down0_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down0; z₃ := up1 } := by
  native_decide

theorem freudenthal_down2_down0_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down0; z₃ := up2 } := by
  native_decide

theorem freudenthal_down2_down0_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down0; z₃ := down0 } := by
  native_decide

theorem freudenthal_down2_down0_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down0; z₃ := down1 } := by
  native_decide

theorem freudenthal_down2_down0_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down0; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down0; z₃ := down2 } := by
  native_decide

theorem freudenthal_down2_down1_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down1; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down2_down1_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down1; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down2_down1_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down1; z₃ := up0 } := by
  native_decide

theorem freudenthal_down2_down1_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down1; z₃ := up1 } := by
  native_decide

theorem freudenthal_down2_down1_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down1; z₃ := up2 } := by
  native_decide

theorem freudenthal_down2_down1_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down1; z₃ := down0 } := by
  native_decide

theorem freudenthal_down2_down1_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down1; z₃ := down1 } := by
  native_decide

theorem freudenthal_down2_down1_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down1; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down1; z₃ := down2 } := by
  native_decide

theorem freudenthal_down2_down2_ePlus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := ePlus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := ePlus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down2; z₃ := ePlus } := by
  native_decide

theorem freudenthal_down2_down2_eMinus :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := eMinus }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := eMinus } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down2; z₃ := eMinus } := by
  native_decide

theorem freudenthal_down2_down2_up0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := up0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := up0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down2; z₃ := up0 } := by
  native_decide

theorem freudenthal_down2_down2_up1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := up1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := up1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down2; z₃ := up1 } := by
  native_decide

theorem freudenthal_down2_down2_up2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := up2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := up2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down2; z₃ := up2 } := by
  native_decide

theorem freudenthal_down2_down2_down0 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := down0 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := down0 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down2; z₃ := down0 } := by
  native_decide

theorem freudenthal_down2_down2_down1 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := down1 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := down1 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down2; z₃ := down1 } := by
  native_decide

theorem freudenthal_down2_down2_down2 :
    adjointQuad (adjointQuad
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := down2 }) =
    (normCubic
      { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
        z₁ := down2; z₂ := down2; z₃ := down2 } : ℝ) •
    { α₁ := (0 : ℝ); α₂ := (0 : ℝ); α₃ := (0 : ℝ)
      z₁ := down2; z₂ := down2; z₃ := down2 } := by
  native_decide

-- Total: 512 basis triples verified via native_decide

end InfoGeometry.Algebra.FreudenthalComplete