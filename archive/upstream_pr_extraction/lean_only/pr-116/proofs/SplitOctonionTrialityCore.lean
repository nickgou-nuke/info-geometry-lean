import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.Algebra.Lie.Subalgebra
import proofs.SplitOctonionNorm44
import proofs.SplitOctonionDerivationSpace

open SplitOctonion
open SplitOctonionNorm44
open LinearMap

namespace SplitOctonionTrialityCore

abbrev EndOS := SplitOct →ₗ[ℝ] SplitOct

noncomputable def splitBilinForm : LinearMap.BilinForm ℝ SplitOct :=
  LinearMap.mk₂ ℝ splitBilinear
    (by intro x1 x2 y; dsimp [splitBilinear, splitNorm, add_def]; ring)
    (by intro c x y; dsimp [splitBilinear, splitNorm, add_def, smul_def]; ring)
    (by intro x y1 y2; dsimp [splitBilinear, splitNorm, add_def]; ring)
    (by intro c x y; dsimp [splitBilinear, splitNorm, add_def, smul_def]; ring)

noncomputable abbrev SO44 := skewAdjointLieSubalgebra splitBilinForm

noncomputable abbrev TrialityAmbient := SO44 × SO44 × SO44

noncomputable instance : Bracket TrialityAmbient TrialityAmbient where
  bracket T1 T2 := (⁅T1.1, T2.1⁆, ⁅T1.2.1, T2.2.1⁆, ⁅T1.2.2, T2.2.2⁆)

noncomputable instance : LieRing TrialityAmbient where
  add_lie _ _ _ := Prod.ext (add_lie _ _ _) (Prod.ext (add_lie _ _ _) (add_lie _ _ _))
  lie_add _ _ _ := Prod.ext (lie_add _ _ _) (Prod.ext (lie_add _ _ _) (lie_add _ _ _))
  lie_self _ := Prod.ext (lie_self _) (Prod.ext (lie_self _) (lie_self _))
  leibniz_lie _ _ _ := Prod.ext (leibniz_lie _ _ _) (Prod.ext (leibniz_lie _ _ _) (leibniz_lie _ _ _))

noncomputable instance : LieAlgebra ℝ TrialityAmbient where
  lie_smul _ _ _ := Prod.ext (lie_smul _ _ _) (Prod.ext (lie_smul _ _ _) (lie_smul _ _ _))

noncomputable def trialityVec (T : TrialityAmbient) : SO44 := T.1
noncomputable def trialityLeft (T : TrialityAmbient) : SO44 := T.2.1
noncomputable def trialityRight (T : TrialityAmbient) : SO44 := T.2.2

def IsTriality (T : TrialityAmbient) : Prop :=
  ∀ x y : SplitOct, (trialityVec T).val (x * y) = (trialityLeft T).val x * y + x * (trialityRight T).val y

lemma triality_zero : IsTriality (0 : TrialityAmbient) := by
  intro x y
  simp only [trialityVec, trialityLeft, trialityRight, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero, zero_apply, mul_zero, zero_mul, add_zero]

lemma triality_add (T1 T2 : TrialityAmbient) (h1 : IsTriality T1) (h2 : IsTriality T2) : IsTriality (T1 + T2) := by
  intro x y
  have ha : (trialityVec (T1 + T2)).val = (trialityVec T1).val + (trialityVec T2).val := rfl
  have hb : (trialityLeft (T1 + T2)).val = (trialityLeft T1).val + (trialityLeft T2).val := rfl
  have hc : (trialityRight (T1 + T2)).val = (trialityRight T1).val + (trialityRight T2).val := rfl
  rw [ha, hb, hc]
  simp only [add_apply]
  rw [h1 x y, h2 x y]
  simp only [add_mul, mul_add]
  abel

lemma triality_smul (c : ℝ) (T : TrialityAmbient) (h : IsTriality T) : IsTriality (c • T) := by
  intro x y
  have ha : (trialityVec (c • T)).val = c • (trialityVec T).val := rfl
  have hb : (trialityLeft (c • T)).val = c • (trialityLeft T).val := rfl
  have hc : (trialityRight (c • T)).val = c • (trialityRight T).val := rfl
  rw [ha, hb, hc]
  simp only [smul_apply]
  rw [h x y]
  simp only [smul_add, smul_mul_assoc, mul_smul_comm]

lemma triality_lie (T1 T2 : TrialityAmbient) (h1 : IsTriality T1) (h2 : IsTriality T2) : IsTriality ⁅T1, T2⁆ := by
  intro x y
  have ha : (trialityVec ⁅T1, T2⁆).val = (trialityVec T1).val ∘ₗ (trialityVec T2).val - (trialityVec T2).val ∘ₗ (trialityVec T1).val := rfl
  have hb : (trialityLeft ⁅T1, T2⁆).val = (trialityLeft T1).val ∘ₗ (trialityLeft T2).val - (trialityLeft T2).val ∘ₗ (trialityLeft T1).val := rfl
  have hc : (trialityRight ⁅T1, T2⁆).val = (trialityRight T1).val ∘ₗ (trialityRight T2).val - (trialityRight T2).val ∘ₗ (trialityRight T1).val := rfl
  rw [ha, hb, hc]
  simp only [sub_apply, comp_apply]
  
  have e1 : (trialityVec T1).val ((trialityVec T2).val (x * y)) = 
    (trialityLeft T1).val ((trialityLeft T2).val x) * y + 
    (trialityLeft T2).val x * (trialityRight T1).val y + 
    (trialityLeft T1).val x * (trialityRight T2).val y + 
    x * (trialityRight T1).val ((trialityRight T2).val y) := by
    rw [h2 x y]
    rw [map_add]
    rw [h1, h1]
    abel
  
  have e2 : (trialityVec T2).val ((trialityVec T1).val (x * y)) = 
    (trialityLeft T2).val ((trialityLeft T1).val x) * y + 
    (trialityLeft T1).val x * (trialityRight T2).val y + 
    (trialityLeft T2).val x * (trialityRight T1).val y + 
    x * (trialityRight T2).val ((trialityRight T1).val y) := by
    rw [h1 x y]
    rw [map_add]
    rw [h2, h2]
    abel
    
  rw [e1, e2]
  simp only [sub_mul, mul_sub]
  abel

noncomputable def trialityLieSubalgebra : LieSubalgebra ℝ TrialityAmbient where
  carrier := { T | IsTriality T }
  zero_mem' := triality_zero
  add_mem' := by intro a b ha hb; exact triality_add a b ha hb
  smul_mem' := by intro c a ha; exact triality_smul c a ha
  lie_mem' := by intro a b ha hb; exact triality_lie a b ha hb

end SplitOctonionTrialityCore
