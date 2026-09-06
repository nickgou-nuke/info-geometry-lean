import Mathlib.Tactic

/-!
# Projective/Affine Penrose PGA anchors

Finite theorem-honest anchors for the projective-affine tiling picture:

* golden-ratio inflation algebra;
* affine homotheties and ratio preservation;
* projective cross-ratio and Möbius/projective invariance;
* homogeneous point/line incidence via the exterior/cross product;
-/

noncomputable section

namespace ProjectivePenrosePGA

open Matrix

/-! ## Golden ratio / Robinson-triangle inflation algebra -/

/-- Golden ratio as the positive algebraic root. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Algebraic golden-ratio relation. -/
theorem phi_sq_eq_phi_add_one : phi ^ 2 = phi + 1 := by
  unfold phi
  have h5 : 0 ≤ (5 : ℝ) := by norm_num
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt h5
  nlinarith [hs]

/-- Fibonacci/Penrose substitution matrix. -/
def FibSubst : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1;
     1, 0]

@[simp] theorem FibSubst_det : FibSubst.det = -1 := by
  simp [FibSubst]

/-- The substitution matrix satisfies its characteristic/golden polynomial. -/
theorem FibSubst_sq : FibSubst * FibSubst = FibSubst + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [FibSubst, Matrix.mul_apply]

/-! ## Affine maps and ratios -/

/-- One-dimensional affine/homothety map. -/
def affineMap (a b x : ℂ) : ℂ := a * x + b

/-- Affine differences scale by the linear coefficient. -/
theorem affineMap_sub (a b x y : ℂ) :
    affineMap a b x - affineMap a b y = a * (x - y) := by
  unfold affineMap
  ring

/-- Affine ratios are preserved by nonzero homotheties. -/
theorem affine_ratio_preserved {a b x y u v : ℂ}
    (ha : a ≠ 0) (huv : u - v ≠ 0) :
    (affineMap a b x - affineMap a b y) / (affineMap a b u - affineMap a b v) =
      (x - y) / (u - v) := by
  rw [affineMap_sub, affineMap_sub]
  field_simp [ha, huv]

/-! ## Projective cross-ratio -/

/-- Cross-ratio of four affine points on the projective line. -/
def crossRatio (a b c d : ℂ) : ℂ :=
  ((a - c) * (b - d)) / ((a - d) * (b - c))

/-- Fractional-linear/projective coordinate action. -/
def mobius (A B C D z : ℂ) : ℂ :=
  (A * z + B) / (C * z + D)

/-- Cross-ratio is invariant under affine maps, a directly proved subcase of
projective invariance. -/
theorem crossRatio_affine_invariant {A B a b c d : ℂ}
    (hA : A ≠ 0) (had : a - d ≠ 0) (hbc : b - c ≠ 0) :
    crossRatio (affineMap A B a) (affineMap A B b)
      (affineMap A B c) (affineMap A B d) = crossRatio a b c d := by
  unfold crossRatio
  rw [affineMap_sub, affineMap_sub, affineMap_sub, affineMap_sub]
  field_simp [hA, had, hbc]

/-- Projective scalar rescaling does not change a Möbius map. -/
theorem mobius_projective_rescale {lam A B C D z : ℂ}
    (hlam : lam ≠ 0) (hden : C * z + D ≠ 0) :
    mobius (lam*A) (lam*B) (lam*C) (lam*D) z = mobius A B C D z := by
  unfold mobius
  have hden' : lam * (C * z + D) ≠ 0 := mul_ne_zero hlam hden
  field_simp [hlam, hden, hden']

/-! ## PGA-style homogeneous point/line incidence -/

abbrev Vec3 := Fin 3 → ℝ

def dot3 (u v : Vec3) : ℝ := ∑ i, u i * v i

def cross3 (u v : Vec3) : Vec3
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- The line through `p` and `q` as homogeneous cross product `p ∧ q`. -/
def lineThrough (p q : Vec3) : Vec3 := cross3 p q

/-- A point lies on a line when the homogeneous dot product is zero. -/
def Incident (p line : Vec3) : Prop := dot3 p line = 0

/-- Exterior-product incidence: `p` lies on the line `p∧q`. -/
theorem incident_left_lineThrough (p q : Vec3) : Incident p (lineThrough p q) := by
  unfold Incident lineThrough dot3 cross3
  simp [Fin.sum_univ_three]
  ring

/-- Exterior-product incidence: `q` lies on the line `p∧q`. -/
theorem incident_right_lineThrough (p q : Vec3) : Incident q (lineThrough p q) := by
  unfold Incident lineThrough dot3 cross3
  simp [Fin.sum_univ_three]
  ring

end ProjectivePenrosePGA
