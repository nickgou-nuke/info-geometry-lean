import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Global split-Witt norm coordinates

The canonical affine carrier exposes the global `(4,4)` quadratic form.
This owner records its decomposition into four explicit `(1,1)` coordinate
planes; it does not identify that norm with an arbitrary raw octonion
multiplication square.
-/

namespace InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm

open ProjectiveAffineConformalClosure55

def splitCoordinates (x y : Fin 4 → ℝ) : PACSplit44 where
  x0 := x 0
  x1 := x 1
  x2 := x 2
  x3 := x 3
  y0 := y 0
  y1 := y 1
  y2 := y 2
  y3 := y 3

def splitPlaneQuadratic (x y : ℝ) : ℝ := x ^ 2 - y ^ 2

def splitPlanePolar (x₁ y₁ x₂ y₂ : ℝ) : ℝ :=
  x₁ * x₂ - y₁ * y₂

theorem splitPlaneQuadratic_add_polar (x₁ y₁ x₂ y₂ : ℝ) :
    splitPlaneQuadratic (x₁ + x₂) (y₁ + y₂) =
      splitPlaneQuadratic x₁ y₁ +
        splitPlaneQuadratic x₂ y₂ +
          2 * splitPlanePolar x₁ y₁ x₂ y₂ := by
  simp [splitPlaneQuadratic, splitPlanePolar]
  ring

theorem splitPlanePolar_symm (x₁ y₁ x₂ y₂ : ℝ) :
    splitPlanePolar x₁ y₁ x₂ y₂ =
      splitPlanePolar x₂ y₂ x₁ y₁ := by
  simp [splitPlanePolar]
  ring

theorem splitPlanePolar_nondegenerate (x y : ℝ) :
    (∀ z w : ℝ, splitPlanePolar x y z w = 0) ↔
      x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hx := h 1 0
    have hy := h 0 1
    constructor <;> simp [splitPlanePolar] at * <;> linarith
  · rintro ⟨rfl, rfl⟩
    intro z w
    simp [splitPlanePolar]

theorem splitPlaneQuadratic_null_plus (t : ℝ) :
    splitPlaneQuadratic t t = 0 := by
  simp [splitPlaneQuadratic]

theorem splitPlaneQuadratic_null_minus (t : ℝ) :
    splitPlaneQuadratic t (-t) = 0 := by
  simp [splitPlaneQuadratic]

theorem splitPlaneQuadratic_eq_zero_iff (x y : ℝ) :
    splitPlaneQuadratic x y = 0 ↔ x = y ∨ x = -y := by
  constructor
  · intro h
    have hfac : (x - y) * (x + y) = 0 := by
      dsimp [splitPlaneQuadratic] at h
      nlinarith
    rcases mul_eq_zero.mp hfac with hxy | hxy
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (hxy | hxy)
    · simp [hxy, splitPlaneQuadratic]
    · simp [hxy, splitPlaneQuadratic]

theorem splitPlaneQuadratic_eq_four_mul_null_coordinates (x y : ℝ) :
    splitPlaneQuadratic x y =
      4 * (((x + y) / 2) * ((x - y) / 2)) := by
  simp [splitPlaneQuadratic]
  ring

theorem splitPlaneQuadratic_eq_four_mul_null_coordinates' (x y : ℝ) :
    splitPlaneQuadratic x y =
      4 * (((x - y) / 2) * ((x + y) / 2)) := by
  simp [splitPlaneQuadratic]
  ring

/-! ## Hyperbolic Möbius/Cartan action on the four split planes -/

/-- The diagonal Cartan flow in null coordinates, written as a boost in the
orthogonal `(x_a,y_a)` coordinates of the four `(1,1)` planes. -/
noncomputable def mobiusCartanCarrierAction (η : ℝ) (X : PACSplit44) : PACSplit44 where
  x0 := Real.cosh η * X.x0 + Real.sinh η * X.y0
  x1 := Real.cosh η * X.x1 + Real.sinh η * X.y1
  x2 := Real.cosh η * X.x2 + Real.sinh η * X.y2
  x3 := Real.cosh η * X.x3 + Real.sinh η * X.y3
  y0 := Real.sinh η * X.x0 + Real.cosh η * X.y0
  y1 := Real.sinh η * X.x1 + Real.cosh η * X.y1
  y2 := Real.sinh η * X.x2 + Real.cosh η * X.y2
  y3 := Real.sinh η * X.x3 + Real.cosh η * X.y3

theorem mobiusCartanCarrierAction_preserves_Q44 (η : ℝ) (X : PACSplit44) :
    Q44 (mobiusCartanCarrierAction η X) = Q44 X := by
  cases X
  unfold Q44 mobiusCartanCarrierAction
  nlinarith [Real.cosh_sq_sub_sinh_sq η]

theorem mobiusCartanCarrierAction_zero (X : PACSplit44) :
    mobiusCartanCarrierAction 0 X = X := by
  cases X
  simp [mobiusCartanCarrierAction]



theorem splitCoordinates_Q44 (x y : Fin 4 → ℝ) :
    Q44 (splitCoordinates x y) =
      (x 0 ^ 2 - y 0 ^ 2) +
      (x 1 ^ 2 - y 1 ^ 2) +
      (x 2 ^ 2 - y 2 ^ 2) +
      (x 3 ^ 2 - y 3 ^ 2) := by
  simp [splitCoordinates, Q44]
  ring

theorem splitCoordinates_Q44_eq_sum_planeQuadratic (x y : Fin 4 → ℝ) :
    Q44 (splitCoordinates x y) =
      ∑ a : Fin 4, splitPlaneQuadratic (x a) (y a) := by
  simp [splitCoordinates, Q44, splitPlaneQuadratic, Fin.sum_univ_succ]
  ring

theorem splitCoordinates_Q44_eq_four_mul_sum_null_coordinates
    (x y : Fin 4 → ℝ) :
    Q44 (splitCoordinates x y) =
      4 * ∑ a : Fin 4,
        (((x a + y a) / 2) * ((x a - y a) / 2)) := by
  rw [splitCoordinates_Q44_eq_sum_planeQuadratic]
  simp_rw [splitPlaneQuadratic_eq_four_mul_null_coordinates]
  rw [← Finset.mul_sum]

theorem splitCoordinates_Q44_add_polar
    (x₁ y₁ x₂ y₂ : Fin 4 → ℝ) :
    Q44 (splitCoordinates (x₁ + x₂) (y₁ + y₂)) =
      Q44 (splitCoordinates x₁ y₁) +
        Q44 (splitCoordinates x₂ y₂) +
          2 * ∑ a : Fin 4, splitPlanePolar
            (x₁ a) (y₁ a) (x₂ a) (y₂ a) := by
  rw [splitCoordinates_Q44_eq_sum_planeQuadratic,
    splitCoordinates_Q44_eq_sum_planeQuadratic,
    splitCoordinates_Q44_eq_sum_planeQuadratic]
  simp only [Pi.add_apply]
  simp_rw [splitPlaneQuadratic_add_polar]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]

theorem splitCoordinates_is_four_split_planes (x y : Fin 4 → ℝ) :
    Q44 (splitCoordinates x y) =
      ((x 0 ^ 2 - y 0 ^ 2) + (x 1 ^ 2 - y 1 ^ 2)) +
      ((x 2 ^ 2 - y 2 ^ 2) + (x 3 ^ 2 - y 3 ^ 2)) := by
  rw [splitCoordinates_Q44]
  ring

end InfoGeometry.Algebra.Zorn.SplitOctonionGlobalWittNorm
