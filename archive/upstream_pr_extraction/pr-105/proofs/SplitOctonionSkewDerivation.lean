import Mathlib
import proofs.SplitOctonionDerivationSpace
import proofs.SplitOctonionNorm44

open SplitOctonion
open SplitOctonionNorm44
open OctDerivation

/-- A SkewDerivation is a derivation that also preserves the split bilinear form infinitesimally. -/
structure SkewDerivation where
  toOctDerivation : OctDerivation
  skew' : ∀ x y, splitBilinear (toOctDerivation x) y + splitBilinear x (toOctDerivation y) = 0

namespace SkewDerivation

instance : CoeFun SkewDerivation (fun _ => SplitOct → SplitOct) where
  coe D := D.toOctDerivation.toLinearMap.toFun

@[ext]
theorem ext_skew (D1 D2 : SkewDerivation) (h : D1.toOctDerivation = D2.toOctDerivation) : D1 = D2 := by
  cases D1; cases D2
  have h_eq : _ = _ := h
  subst h_eq
  rfl

instance : Add SkewDerivation where
  add D1 D2 := {
    toOctDerivation := D1.toOctDerivation + D2.toOctDerivation
    skew' := by
      intro x y
      have h1 := D1.skew' x y
      have h2 := D2.skew' x y
      change splitBilinear (D1.toOctDerivation x + D2.toOctDerivation x) y + splitBilinear x (D1.toOctDerivation y + D2.toOctDerivation y) = 0
      -- We need splitBilinear_add_left and splitBilinear_add_right
      have h_add_L : splitBilinear (D1.toOctDerivation x + D2.toOctDerivation x) y = splitBilinear (D1.toOctDerivation x) y + splitBilinear (D2.toOctDerivation x) y := by
        dsimp [splitBilinear, splitNorm, add_def]
        ring
      have h_add_R : splitBilinear x (D1.toOctDerivation y + D2.toOctDerivation y) = splitBilinear x (D1.toOctDerivation y) + splitBilinear x (D2.toOctDerivation y) := by
        dsimp [splitBilinear, splitNorm, add_def]
        ring
      rw [h_add_L, h_add_R]
      linarith
  }

instance : Neg SkewDerivation where
  neg D := {
    toOctDerivation := -D.toOctDerivation
    skew' := by
      intro x y
      have h := D.skew' x y
      change splitBilinear (-D.toOctDerivation x) y + splitBilinear x (-D.toOctDerivation y) = 0
      have h_neg_L : splitBilinear (-D.toOctDerivation x) y = - splitBilinear (D.toOctDerivation x) y := by
        dsimp [splitBilinear, splitNorm, add_def, neg_def]
        ring
      have h_neg_R : splitBilinear x (-D.toOctDerivation y) = - splitBilinear x (D.toOctDerivation y) := by
        dsimp [splitBilinear, splitNorm, add_def, neg_def]
        ring
      rw [h_neg_L, h_neg_R]
      linarith
  }

instance : Sub SkewDerivation where
  sub D1 D2 := D1 + (-D2)

instance : Zero SkewDerivation where
  zero := {
    toOctDerivation := 0
    skew' := by
      intro x y
      change splitBilinear 0 y + splitBilinear x 0 = 0
      have h_zero_L : splitBilinear 0 y = 0 := by dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
      have h_zero_R : splitBilinear x 0 = 0 := by dsimp [splitBilinear, splitNorm, add_def, zero_def]; ring
      rw [h_zero_L, h_zero_R, add_zero]
  }

instance : SMul ℝ SkewDerivation where
  smul c D := {
    toOctDerivation := c • D.toOctDerivation
    skew' := by
      intro x y
      have h := D.skew' x y
      change splitBilinear (c • D.toOctDerivation x) y + splitBilinear x (c • D.toOctDerivation y) = 0
      have h_smul_L : splitBilinear (c • D.toOctDerivation x) y = c * splitBilinear (D.toOctDerivation x) y := by
        dsimp [splitBilinear, splitNorm, add_def, smul_def]
        ring
      have h_smul_R : splitBilinear x (c • D.toOctDerivation y) = c * splitBilinear x (D.toOctDerivation y) := by
        dsimp [splitBilinear, splitNorm, add_def, smul_def]
        ring
      rw [h_smul_L, h_smul_R, ← mul_add, h, mul_zero]
  }

instance : AddCommGroup SkewDerivation where
  add_assoc := by intro a b c; apply ext_skew; apply add_assoc
  zero_add := by intro a; apply ext_skew; apply zero_add
  add_zero := by intro a; apply ext_skew; apply add_zero
  add_comm := by intro a b; apply ext_skew; apply add_comm
  neg_add_cancel := by intro a; apply ext_skew; apply neg_add_cancel
  sub_eq_add_neg := by intro a b; apply ext_skew; apply sub_eq_add_neg
  nsmul := nsmulRec
  nsmul_zero := by intro a; apply ext_skew; rfl
  nsmul_succ := by intro n a; apply ext_skew; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro a; apply ext_skew; rfl
  zsmul_succ' := by intro n a; apply ext_skew; rfl
  zsmul_neg' := by intro n a; apply ext_skew; rfl

instance : Module ℝ SkewDerivation where
  smul_add := by intro c a b; apply ext_skew; apply smul_add
  add_smul := by intro c d a; apply ext_skew; apply add_smul
  mul_smul := by intro c d a; apply ext_skew; apply mul_smul
  one_smul := by intro a; apply ext_skew; apply one_smul
  smul_zero := by intro c; apply ext_skew; apply smul_zero
  zero_smul := by intro a; apply ext_skew; apply zero_smul

instance : Bracket SkewDerivation SkewDerivation where
  bracket D1 D2 := {
    toOctDerivation := ⁅D1.toOctDerivation, D2.toOctDerivation⁆
    skew' := by
      intro x y
      change splitBilinear (D1.toOctDerivation (D2.toOctDerivation x) - D2.toOctDerivation (D1.toOctDerivation x)) y + splitBilinear x (D1.toOctDerivation (D2.toOctDerivation y) - D2.toOctDerivation (D1.toOctDerivation y)) = 0
      
      have h_sub_L : ∀ a b, splitBilinear (a - b) y = splitBilinear a y - splitBilinear b y := by
        intro a b; dsimp [splitBilinear, splitNorm, add_def, sub_def, neg_def]; ring
      have h_sub_R : ∀ a b, splitBilinear x (a - b) = splitBilinear x a - splitBilinear x b := by
        intro a b; dsimp [splitBilinear, splitNorm, add_def, sub_def, neg_def]; ring
        
      rw [h_sub_L, h_sub_R]
      
      -- use skewness of D1 and D2
      have h1_D2x := D1.skew' (D2.toOctDerivation x) y
      have h2_x := D2.skew' x (D1.toOctDerivation y)
      have h2_D1x := D2.skew' (D1.toOctDerivation x) y
      have h1_x := D1.skew' x (D2.toOctDerivation y)
      
      -- splitBilinear (D1 (D2 x)) y = - splitBilinear (D2 x) (D1 y)
      -- splitBilinear x (D1 (D2 y)) = - splitBilinear (D1 x) (D2 y)
      have eq1 : splitBilinear (D1.toOctDerivation (D2.toOctDerivation x)) y = - splitBilinear (D2.toOctDerivation x) (D1.toOctDerivation y) := eq_neg_of_add_eq_zero_left h1_D2x
      have eq2 : splitBilinear x (D1.toOctDerivation (D2.toOctDerivation y)) = - splitBilinear (D1.toOctDerivation x) (D2.toOctDerivation y) := by
        have H := D1.skew' (D2.toOctDerivation y) x
        have H_sym1 : splitBilinear (D1.toOctDerivation (D2.toOctDerivation y)) x = splitBilinear x (D1.toOctDerivation (D2.toOctDerivation y)) := splitBilinear_symmetric _ _
        have H_sym2 : splitBilinear (D2.toOctDerivation y) (D1.toOctDerivation x) = splitBilinear (D1.toOctDerivation x) (D2.toOctDerivation y) := splitBilinear_symmetric _ _
        rw [H_sym1, H_sym2] at H
        exact eq_neg_of_add_eq_zero_left H
        
      have eq3 : splitBilinear (D2.toOctDerivation (D1.toOctDerivation x)) y = - splitBilinear (D1.toOctDerivation x) (D2.toOctDerivation y) := eq_neg_of_add_eq_zero_left h2_D1x
      have eq4 : splitBilinear x (D2.toOctDerivation (D1.toOctDerivation y)) = - splitBilinear (D2.toOctDerivation x) (D1.toOctDerivation y) := by
        have H := D2.skew' (D1.toOctDerivation y) x
        have H_sym1 : splitBilinear (D2.toOctDerivation (D1.toOctDerivation y)) x = splitBilinear x (D2.toOctDerivation (D1.toOctDerivation y)) := splitBilinear_symmetric _ _
        have H_sym2 : splitBilinear (D1.toOctDerivation y) (D2.toOctDerivation x) = splitBilinear (D2.toOctDerivation x) (D1.toOctDerivation y) := splitBilinear_symmetric _ _
        rw [H_sym1, H_sym2] at H
        exact eq_neg_of_add_eq_zero_left H

      rw [eq1, eq2, eq3, eq4]
      ring
  }

instance : LieRing SkewDerivation where
  add_lie := by intro a b c; apply ext_skew; apply add_lie
  lie_add := by intro a b c; apply ext_skew; apply lie_add
  lie_self := by intro a; apply ext_skew; apply lie_self
  leibniz_lie := by intro a b c; apply ext_skew; apply leibniz_lie

instance : LieAlgebra ℝ SkewDerivation where
  lie_smul := by intro c a b; apply ext_skew; apply lie_smul

end SkewDerivation
