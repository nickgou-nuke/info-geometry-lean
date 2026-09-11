import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.RealSplitAlbert

/-!
# Topology of the real split-Albert carrier

The integer-valued `CubicJordanOs.AlbertMatrix` has a deliberately rounded
scalar action on `SplitOct`.  This file instead records the honest continuous
coordinate topology for the real carrier and its polynomial split-octonion
product.
-/

noncomputable section

namespace InfoGeometry.Algebra

open CategoryTheory
open RealSplitOct RealAlbertMatrix

instance realSplitOctTopologicalSpace : TopologicalSpace RealSplitOct :=
  TopologicalSpace.induced RealSplitOct.coordEquiv.toFun inferInstance

instance realAlbertMatrixTopologicalSpace : TopologicalSpace RealAlbertMatrix :=
  TopologicalSpace.induced RealAlbertMatrix.coordEquiv.toFun inferInstance

private theorem continuous_realSplitOct_coordEquiv :
    Continuous
      (RealSplitOct.coordEquiv :
        RealSplitOct ≃ ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
  continuous_induced_dom

private theorem continuous_realAlbertMatrix_coordEquiv :
    Continuous
      (RealAlbertMatrix.coordEquiv :
        RealAlbertMatrix ≃
          ℝ × ℝ × ℝ × RealSplitOct × RealSplitOct × RealSplitOct) :=
  continuous_induced_dom

private theorem continuous_realSplitOct_a :
    Continuous (fun X : RealSplitOct => X.a) := by
  simpa [RealSplitOct.coordEquiv] using continuous_realSplitOct_coordEquiv.fst

private theorem continuous_realSplitOct_b :
    Continuous (fun X : RealSplitOct => X.b) := by
  simpa [RealSplitOct.coordEquiv] using
    continuous_realSplitOct_coordEquiv.snd.fst

private theorem continuous_realSplitOct_x0 :
    Continuous (fun X : RealSplitOct => X.x0) := by
  simpa [RealSplitOct.coordEquiv] using
    continuous_realSplitOct_coordEquiv.snd.snd.fst

private theorem continuous_realSplitOct_x1 :
    Continuous (fun X : RealSplitOct => X.x1) := by
  simpa [RealSplitOct.coordEquiv] using
    continuous_realSplitOct_coordEquiv.snd.snd.snd.fst

private theorem continuous_realSplitOct_x2 :
    Continuous (fun X : RealSplitOct => X.x2) := by
  simpa [RealSplitOct.coordEquiv] using
    continuous_realSplitOct_coordEquiv.snd.snd.snd.snd.fst

private theorem continuous_realSplitOct_y0 :
    Continuous (fun X : RealSplitOct => X.y0) := by
  simpa [RealSplitOct.coordEquiv] using
    continuous_realSplitOct_coordEquiv.snd.snd.snd.snd.snd.fst

private theorem continuous_realSplitOct_y1 :
    Continuous (fun X : RealSplitOct => X.y1) := by
  simpa [RealSplitOct.coordEquiv] using
    continuous_realSplitOct_coordEquiv.snd.snd.snd.snd.snd.snd.fst

private theorem continuous_realSplitOct_y2 :
    Continuous (fun X : RealSplitOct => X.y2) := by
  simpa [RealSplitOct.coordEquiv] using
    continuous_realSplitOct_coordEquiv.snd.snd.snd.snd.snd.snd.snd

private theorem continuous_realAlbertMatrix_α₁ :
    Continuous (fun X : RealAlbertMatrix => X.α₁) := by
  simpa [RealAlbertMatrix.coordEquiv] using
    continuous_realAlbertMatrix_coordEquiv.fst

private theorem continuous_realAlbertMatrix_α₂ :
    Continuous (fun X : RealAlbertMatrix => X.α₂) := by
  simpa [RealAlbertMatrix.coordEquiv] using
    continuous_realAlbertMatrix_coordEquiv.snd.fst

private theorem continuous_realAlbertMatrix_α₃ :
    Continuous (fun X : RealAlbertMatrix => X.α₃) := by
  simpa [RealAlbertMatrix.coordEquiv] using
    continuous_realAlbertMatrix_coordEquiv.snd.snd.fst

private theorem continuous_realAlbertMatrix_z₁ :
    Continuous (fun X : RealAlbertMatrix => X.z₁) := by
  simpa [RealAlbertMatrix.coordEquiv] using
    continuous_realAlbertMatrix_coordEquiv.snd.snd.snd.fst

private theorem continuous_realAlbertMatrix_z₂ :
    Continuous (fun X : RealAlbertMatrix => X.z₂) := by
  simpa [RealAlbertMatrix.coordEquiv] using
    continuous_realAlbertMatrix_coordEquiv.snd.snd.snd.snd.fst

private theorem continuous_realAlbertMatrix_z₃ :
    Continuous (fun X : RealAlbertMatrix => X.z₃) := by
  simpa [RealAlbertMatrix.coordEquiv] using
    continuous_realAlbertMatrix_coordEquiv.snd.snd.snd.snd.snd

attribute [fun_prop]
  continuous_realSplitOct_a continuous_realSplitOct_b
  continuous_realSplitOct_x0 continuous_realSplitOct_x1
  continuous_realSplitOct_x2 continuous_realSplitOct_y0
  continuous_realSplitOct_y1 continuous_realSplitOct_y2

theorem continuous_realSplitOct_smul :
    Continuous
      (fun p : ℝ × RealSplitOct => RealSplitOct.smul p.1 p.2) := by
  apply (continuous_induced_rng).2
  fun_prop

theorem continuous_realSplitOct_smul_left (r : ℝ) :
    Continuous (fun X : RealSplitOct => RealSplitOct.smul r X) := by
  simpa using
    continuous_realSplitOct_smul.comp
      (continuous_const.prodMk
        (continuous_id : Continuous (id : RealSplitOct → RealSplitOct)))

attribute [fun_prop]
  continuous_realSplitOct_a continuous_realSplitOct_b
  continuous_realSplitOct_x0 continuous_realSplitOct_x1
  continuous_realSplitOct_x2 continuous_realSplitOct_y0
  continuous_realSplitOct_y1 continuous_realSplitOct_y2
  continuous_realSplitOct_smul continuous_realSplitOct_smul_left
  continuous_realAlbertMatrix_α₁ continuous_realAlbertMatrix_α₂
  continuous_realAlbertMatrix_α₃ continuous_realAlbertMatrix_z₁
  continuous_realAlbertMatrix_z₂ continuous_realAlbertMatrix_z₃

theorem continuous_realSplitOct_mul :
    Continuous (fun p : RealSplitOct × RealSplitOct => RealSplitOct.mul p.1 p.2) := by
  apply (continuous_induced_rng).2
  fun_prop

theorem continuous_realSplitOct_conj :
    Continuous (RealSplitOct.conj : RealSplitOct → RealSplitOct) := by
  apply (continuous_induced_rng).2
  fun_prop

attribute [fun_prop] continuous_realSplitOct_mul continuous_realSplitOct_conj

theorem continuous_realAlbertMatrix_mul :
    Continuous
      (fun p : RealAlbertMatrix × RealAlbertMatrix =>
        RealAlbertMatrix.mul p.1 p.2) := by
  have hα₁ : Continuous
      (fun p : RealAlbertMatrix × RealAlbertMatrix =>
        (RealAlbertMatrix.mul p.1 p.2).α₁) := by
    simp only [RealAlbertMatrix.mul]
    fun_prop
  have hα₂ : Continuous
      (fun p : RealAlbertMatrix × RealAlbertMatrix =>
        (RealAlbertMatrix.mul p.1 p.2).α₂) := by
    simp only [RealAlbertMatrix.mul]
    fun_prop
  have hα₃ : Continuous
      (fun p : RealAlbertMatrix × RealAlbertMatrix =>
        (RealAlbertMatrix.mul p.1 p.2).α₃) := by
    simp only [RealAlbertMatrix.mul]
    fun_prop
  have hz₁ : Continuous
      (fun p : RealAlbertMatrix × RealAlbertMatrix =>
        (RealAlbertMatrix.mul p.1 p.2).z₁) := by
    apply (continuous_induced_rng).2
    simp only [RealSplitOct.coordEquiv]
    fun_prop
  have hz₂ : Continuous
      (fun p : RealAlbertMatrix × RealAlbertMatrix =>
        (RealAlbertMatrix.mul p.1 p.2).z₂) := by
    apply (continuous_induced_rng).2
    simp only [RealSplitOct.coordEquiv]
    fun_prop
  have hz₃ : Continuous
      (fun p : RealAlbertMatrix × RealAlbertMatrix =>
        (RealAlbertMatrix.mul p.1 p.2).z₃) := by
    apply (continuous_induced_rng).2
    simp only [RealSplitOct.coordEquiv]
    fun_prop
  apply (continuous_induced_rng).2
  simpa [RealAlbertMatrix.coordEquiv, Function.comp_def] using
    hα₁.prodMk (hα₂.prodMk (hα₃.prodMk (hz₁.prodMk (hz₂.prodMk hz₃))))

def realSplitOctMulContinuousMap :
    ContinuousMap (RealSplitOct × RealSplitOct) RealSplitOct :=
  ContinuousMap.mk
    (fun p => RealSplitOct.mul p.1 p.2)
    continuous_realSplitOct_mul

@[simp] theorem realSplitOctMulContinuousMap_apply
    (p : RealSplitOct × RealSplitOct) :
    realSplitOctMulContinuousMap p = RealSplitOct.mul p.1 p.2 := rfl

def realSplitOctConjContinuousMap :
    ContinuousMap RealSplitOct RealSplitOct :=
  ContinuousMap.mk RealSplitOct.conj continuous_realSplitOct_conj

@[simp] theorem realSplitOctConjContinuousMap_apply (X : RealSplitOct) :
    realSplitOctConjContinuousMap X = RealSplitOct.conj X := rfl

def realSplitOctSmulContinuousMap :
    ContinuousMap (ℝ × RealSplitOct) RealSplitOct :=
  ContinuousMap.mk
    (fun p => RealSplitOct.smul p.1 p.2)
    continuous_realSplitOct_smul

@[simp] theorem realSplitOctSmulContinuousMap_apply
    (p : ℝ × RealSplitOct) :
    realSplitOctSmulContinuousMap p = RealSplitOct.smul p.1 p.2 := rfl

def realAlbertMatrixMulContinuousMap :
    ContinuousMap (RealAlbertMatrix × RealAlbertMatrix) RealAlbertMatrix :=
  ContinuousMap.mk
    (fun p => RealAlbertMatrix.mul p.1 p.2)
    continuous_realAlbertMatrix_mul

@[simp] theorem realAlbertMatrixMulContinuousMap_apply
    (p : RealAlbertMatrix × RealAlbertMatrix) :
    realAlbertMatrixMulContinuousMap p = RealAlbertMatrix.mul p.1 p.2 := rfl

def realSplitOctMulTopCat :
    TopCat.of (RealSplitOct × RealSplitOct) ⟶ TopCat.of RealSplitOct :=
  TopCat.ofHom realSplitOctMulContinuousMap

def realSplitOctConjTopCat :
    TopCat.of RealSplitOct ⟶ TopCat.of RealSplitOct :=
  TopCat.ofHom realSplitOctConjContinuousMap

def realSplitOctSmulTopCat :
    TopCat.of (ℝ × RealSplitOct) ⟶ TopCat.of RealSplitOct :=
  TopCat.ofHom realSplitOctSmulContinuousMap

def realAlbertMatrixMulTopCat :
    TopCat.of (RealAlbertMatrix × RealAlbertMatrix) ⟶
      TopCat.of RealAlbertMatrix :=
  TopCat.ofHom realAlbertMatrixMulContinuousMap

@[simp] theorem realAlbertMatrixMulTopCat_apply
    (p : RealAlbertMatrix × RealAlbertMatrix) :
    realAlbertMatrixMulTopCat p = RealAlbertMatrix.mul p.1 p.2 := rfl

end InfoGeometry.Algebra
