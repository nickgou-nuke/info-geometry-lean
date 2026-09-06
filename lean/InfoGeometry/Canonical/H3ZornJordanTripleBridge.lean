import Mathlib
import InfoGeometry.Algebra.H3ZornJordanInstance
import InfoGeometry.Algebra.BaezF4H3Zorn

noncomputable section

namespace InfoGeometry.Canonical.H3ZornJordanTripleBridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

abbrev H3 := H3Zorn ℝ

def jordanTriple (x y z : H3) : H3 :=
  (x * y) * z + (z * y) * x - (x * z) * y

theorem jordanTriple_outer_symm (x y z : H3) :
    jordanTriple x y z = jordanTriple z y x := by
  simp [jordanTriple, mul_comm]
  abel

theorem jordanTriple_K_expression_zero (x y z : H3) :
    jordanTriple x z y - jordanTriple y z x = 0 := by
  rw [jordanTriple_outer_symm x z y]
  simp

@[simp] theorem jordanTriple_add_left (x₁ x₂ y z : H3) :
    jordanTriple (x₁ + x₂) y z =
      jordanTriple x₁ y z + jordanTriple x₂ y z := by
  simp [jordanTriple, mul_add, add_mul]
  abel

@[simp] theorem jordanTriple_smul_left (r : ℝ) (x y z : H3) :
    jordanTriple (r • x) y z = r • jordanTriple x y z := by
  simp [jordanTriple, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm]

@[simp] theorem jordanTriple_add_middle (x y₁ y₂ z : H3) :
    jordanTriple x (y₁ + y₂) z =
      jordanTriple x y₁ z + jordanTriple x y₂ z := by
  simp [jordanTriple, mul_add, add_mul]
  abel

@[simp] theorem jordanTriple_smul_middle (r : ℝ) (x y z : H3) :
    jordanTriple x (r • y) z = r • jordanTriple x y z := by
  simp [jordanTriple, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm]

@[simp] theorem jordanTriple_add_right (x y z₁ z₂ : H3) :
    jordanTriple x y (z₁ + z₂) =
      jordanTriple x y z₁ + jordanTriple x y z₂ := by
  simp [jordanTriple, mul_add, add_mul]
  abel

@[simp] theorem jordanTriple_smul_right (r : ℝ) (x y z : H3) :
    jordanTriple x y (r • z) = r • jordanTriple x y z := by
  simp [jordanTriple, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm]

noncomputable def jordanTripleD (x y : H3) : Module.End ℝ H3 where
  toFun z := jordanTriple x y z
  map_add' := jordanTriple_add_right x y
  map_smul' := fun r z => jordanTriple_smul_right r x y z

@[simp] theorem jordanTripleD_apply (x y z : H3) :
    jordanTripleD x y z = jordanTriple x y z := rfl

/-! The native inner derivation carrier is reused from the verified
    split-Albert Jordan instance rather than reconstructed on coordinates. -/

noncomputable def innerDerivation (x y : H3) : Module.End ℝ H3 :=
  (InfoGeometry.Algebra.h3ZornJordanInnerDerivation x y : Module.End ℝ H3)

@[simp] theorem innerDerivation_apply (x y z : H3) :
    innerDerivation x y z = x * (y * z) - y * (x * z) := by
  rfl

theorem innerDerivation_skew (x y : H3) :
    innerDerivation y x = - innerDerivation x y := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.neg_apply, innerDerivation_apply]
  abel

theorem innerDerivation_leibniz (x y u v : H3) :
    innerDerivation x y (u * v) =
      innerDerivation x y u * v + u * innerDerivation x y v := by
  exact InfoGeometry.Algebra.h3ZornJordanInnerDerivation_leibniz x y u v

theorem jordanTriple_derivation
    (D : Module.End ℝ H3) (hD : H3ZornJordanDerivation D)
    (x y z : H3) :
    D (jordanTriple x y z) =
      jordanTriple (D x) y z + jordanTriple x (D y) z +
        jordanTriple x y (D z) := by
  have hDc (a b : H3) :
      D (a * b) = D a * b + a * D b := hD a b
  simp only [jordanTriple, map_add, map_sub]
  simp only [hDc]
  simp only [add_mul, mul_add, sub_mul, mul_sub]
  abel

end InfoGeometry.Canonical.H3ZornJordanTripleBridge
