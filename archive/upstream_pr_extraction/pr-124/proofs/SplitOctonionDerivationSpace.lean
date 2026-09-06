import Mathlib
import proofs.SplitOctonionAlgebra

open SplitOctonion
open LinearMap

/-- A derivation on the split octonions is an R-linear map that satisfies the Leibniz rule
    with respect to the Cayley-Dickson product.
    We avoid Mathlib's RingTheory.Derivation because it assumes an associative algebra. -/
structure OctDerivation where
  toLinearMap : SplitOct →ₗ[ℝ] SplitOct
  leibniz' : ∀ x y, toLinearMap (x * y) = toLinearMap x * y + x * toLinearMap y

namespace OctDerivation

instance : CoeFun OctDerivation (fun _ => SplitOct → SplitOct) where
  coe D := D.toLinearMap.toFun

@[ext]
theorem ext_lin (D1 D2 : OctDerivation) (h : D1.toLinearMap = D2.toLinearMap) : D1 = D2 := by
  cases D1; cases D2
  have h_lin : _ = _ := h
  subst h_lin
  rfl

instance : Add OctDerivation where
  add D1 D2 := {
    toLinearMap := D1.toLinearMap + D2.toLinearMap
    leibniz' := by 
      intro x y
      simp only [add_apply, D1.leibniz', D2.leibniz']
      simp only [add_mul, mul_add]
      abel
  }

instance : Neg OctDerivation where
  neg D := {
    toLinearMap := -D.toLinearMap
    leibniz' := by 
      intro x y
      simp only [neg_apply]
      have hd := D.leibniz' x y
      rw [hd, neg_add, neg_mul, mul_neg]
  }

instance : Sub OctDerivation where
  sub D1 D2 := D1 + (-D2)

instance : Zero OctDerivation where
  zero := {
    toLinearMap := 0
    leibniz' := by intro x y; simp
  }

instance : SMul ℝ OctDerivation where
  smul c D := {
    toLinearMap := c • D.toLinearMap
    leibniz' := by
      intro x y
      simp only [smul_apply, D.leibniz']
      simp only [smul_add, smul_mul_assoc, mul_smul_comm]
  }

instance : AddCommGroup OctDerivation where
  add_assoc := by intro a b c; apply ext_lin; apply add_assoc
  zero_add := by intro a; apply ext_lin; apply zero_add
  add_zero := by intro a; apply ext_lin; apply add_zero
  add_comm := by intro a b; apply ext_lin; apply add_comm
  neg_add_cancel := by intro a; apply ext_lin; apply neg_add_cancel
  sub_eq_add_neg := by intro a b; apply ext_lin; apply sub_eq_add_neg
  nsmul := nsmulRec
  nsmul_zero := by intros a; apply ext_lin; rfl
  nsmul_succ := by intros n a; apply ext_lin; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intros a; apply ext_lin; rfl
  zsmul_succ' := by intros n a; apply ext_lin; rfl
  zsmul_neg' := by intros n a; apply ext_lin; rfl

instance : Module ℝ OctDerivation where
  smul_add := by intro c a b; apply ext_lin; apply smul_add
  add_smul := by intro c d a; apply ext_lin; apply add_smul
  mul_smul := by intro c d a; apply ext_lin; apply mul_smul
  one_smul := by intro a; apply ext_lin; apply one_smul
  smul_zero := by intro c; apply ext_lin; apply smul_zero
  zero_smul := by intro a; apply ext_lin; apply zero_smul

instance : Bracket OctDerivation OctDerivation where
  bracket D1 D2 := {
    toLinearMap := D1.toLinearMap ∘ₗ D2.toLinearMap - D2.toLinearMap ∘ₗ D1.toLinearMap
    leibniz' := by
      intro x y
      simp only [sub_apply, comp_apply]
      have hd1 := D1.leibniz'
      have hd2 := D2.leibniz'
      have h1 : D1.toLinearMap (D2.toLinearMap (x * y)) = D1.toLinearMap (D2.toLinearMap x * y) + D1.toLinearMap (x * D2.toLinearMap y) := by
        rw [hd2, map_add]
      have h2 : D2.toLinearMap (D1.toLinearMap (x * y)) = D2.toLinearMap (D1.toLinearMap x * y) + D2.toLinearMap (x * D1.toLinearMap y) := by
        rw [hd1, map_add]
      rw [h1, h2]
      simp only [hd1, hd2, sub_mul, mul_sub]
      abel
  }

@[simp] lemma zero_toLinearMap : (0 : OctDerivation).toLinearMap = 0 := rfl
@[simp] lemma add_toLinearMap (D1 D2 : OctDerivation) : (D1 + D2).toLinearMap = D1.toLinearMap + D2.toLinearMap := rfl
@[simp] lemma sub_toLinearMap (D1 D2 : OctDerivation) : (D1 - D2).toLinearMap = D1.toLinearMap - D2.toLinearMap := rfl
@[simp] lemma smul_toLinearMap (c : ℝ) (D : OctDerivation) : (c • D).toLinearMap = c • D.toLinearMap := rfl
@[simp] lemma bracket_toLinearMap (D1 D2 : OctDerivation) : (⁅D1, D2⁆).toLinearMap = D1.toLinearMap ∘ₗ D2.toLinearMap - D2.toLinearMap ∘ₗ D1.toLinearMap := rfl

instance : LieRing OctDerivation where
  add_lie := by 
    intro a b c; apply ext_lin
    simp only [add_toLinearMap, bracket_toLinearMap, add_comp, comp_add]
    abel
  lie_add := by 
    intro a b c; apply ext_lin
    simp only [add_toLinearMap, bracket_toLinearMap, add_comp, comp_add]
    abel
  lie_self := by 
    intro a; apply ext_lin
    simp only [zero_toLinearMap, bracket_toLinearMap, sub_self]
  leibniz_lie := by 
    intro a b c; apply ext_lin
    simp only [add_toLinearMap, bracket_toLinearMap, comp_sub, sub_comp, comp_assoc]
    abel

instance : LieAlgebra ℝ OctDerivation where
  lie_smul := by 
    intro c a b; apply ext_lin
    simp only [smul_toLinearMap, bracket_toLinearMap, smul_comp, comp_smul, smul_sub]

end OctDerivation
