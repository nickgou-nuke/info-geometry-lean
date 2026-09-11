import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Quaternion

noncomputable section

abbrev H := Quaternion ℝ

structure SplitOctonion where
  a : H
  b : H

namespace SplitOctonion

@[ext]
lemma ext (X Y : SplitOctonion) (ha : X.a = Y.a) (hb : X.b = Y.b) : X = Y := by
  cases X; cases Y; simp_all

instance : Zero SplitOctonion where
  zero := ⟨0, 0⟩

instance : One SplitOctonion where
  one := ⟨1, 0⟩

instance : Add SplitOctonion where
  add X Y := ⟨X.a + Y.a, X.b + Y.b⟩

instance : Neg SplitOctonion where
  neg X := ⟨-X.a, -X.b⟩

instance : Sub SplitOctonion where
  sub X Y := ⟨X.a - Y.a, X.b - Y.b⟩

instance : Mul SplitOctonion where
  mul X Y := ⟨X.a * Y.a + (star Y.b) * X.b, Y.b * X.a + X.b * (star Y.a)⟩

@[simp]
lemma mul_a (X Y : SplitOctonion) : (X * Y).a = X.a * Y.a + star Y.b * X.b := rfl

@[simp]
lemma mul_b (X Y : SplitOctonion) : (X * Y).b = Y.b * X.a + X.b * star Y.a := rfl

lemma smul_mul (r : ℝ) (x y : H) : (r • x) * y = r • (x * y) :=
  Algebra.smul_mul_assoc r x y

lemma mul_smul (r : ℝ) (x y : H) : x * (r • y) = r • (x * y) :=
  Algebra.mul_smul_comm r x y

lemma smul_mul_smul (r s : ℝ) (x y : H) : (r • x) * (s • y) = (r * s) • (x * y) := by
  rw [smul_mul, mul_smul, smul_smul]

def normSQ (X : SplitOctonion) : ℝ :=
  (X.a * star X.a).re - (X.b * star X.b).re

def xiL (X : SplitOctonion) : H :=
  X.b * (X.a)⁻¹

lemma normSq_eq_re_mul_star (x : H) : Quaternion.normSq x = (x * star x).re := by
  simp [Quaternion.normSq, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star, Quaternion.re_star, Quaternion.re_mul]

theorem left_reconstruction (X : SplitOctonion) (ha : X.a ≠ 0) :
    X = ⟨X.a, 0⟩ * ⟨1, xiL X⟩ := by
  apply SplitOctonion.ext
  · change X.a = X.a * 1 + (star (xiL X)) * 0
    rw [mul_one, mul_zero, add_zero]
  · change X.b = (xiL X) * X.a + 0 * (star 1)
    unfold xiL
    rw [zero_mul, add_zero, mul_assoc, inv_mul_cancel₀ ha, mul_one]

theorem norm_factorization (X : SplitOctonion) (ha : X.a ≠ 0) :
    normSQ X = (X.a * star X.a).re * (1 - ((xiL X) * star (xiL X)).re) := by
  have h1 : (X.a * star X.a).re = Quaternion.normSq X.a := (normSq_eq_re_mul_star X.a).symm
  have h2 : ((xiL X) * star (xiL X)).re = Quaternion.normSq (xiL X) := (normSq_eq_re_mul_star _).symm
  have h3 : (X.b * star X.b).re = Quaternion.normSq X.b := (normSq_eq_re_mul_star X.b).symm
  unfold normSQ
  rw [h1, h2, h3]
  unfold xiL
  rw [map_mul Quaternion.normSq, Quaternion.normSq_inv X.a]
  have ha_norm : Quaternion.normSq X.a ≠ 0 := Quaternion.normSq_ne_zero.mpr ha
  rw [mul_sub, mul_one]
  have h4 : Quaternion.normSq X.a * (Quaternion.normSq X.b * (Quaternion.normSq X.a)⁻¹) = Quaternion.normSq X.b := by
    calc Quaternion.normSq X.a * (Quaternion.normSq X.b * (Quaternion.normSq X.a)⁻¹)
      _ = Quaternion.normSq X.a * (Quaternion.normSq X.a)⁻¹ * Quaternion.normSq X.b := by ring
      _ = 1 * Quaternion.normSq X.b := by rw [mul_inv_cancel₀ ha_norm]
      _ = Quaternion.normSq X.b := by ring
  rw [h4]

end SplitOctonion
