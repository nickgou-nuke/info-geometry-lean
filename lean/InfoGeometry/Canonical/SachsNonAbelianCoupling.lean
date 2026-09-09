import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Canonical.SachsNonAbelianCoupling

abbrev ScreenVec := Fin 2 → ℝ
abbrev ScreenMat := Fin 2 → Fin 2 → ℝ

def dot2 (x y : ScreenVec) : ℝ := x 0 * y 0 + x 1 * y 1

def detScreenMat (S : ScreenMat) : ℝ :=
  S 0 0 * S 1 1 - S 0 1 * S 1 0

noncomputable def sachsTheta (S : ScreenMat) : ℝ := (S 0 0 + S 1 1) / 2
noncomputable def sachsSigma1 (S : ScreenMat) : ℝ := (S 0 0 - S 1 1) / 2
noncomputable def sachsSigma2 (S : ScreenMat) : ℝ := (S 0 1 + S 1 0) / 2
noncomputable def sachsOmega (S : ScreenMat) : ℝ := (S 1 0 - S 0 1) / 2
def shearNormSq (s₁ s₂ : ℝ) : ℝ := s₁ ^ 2 + s₂ ^ 2

def crossProduct (u v : Fin 3 → ℝ) : Fin 3 → ℝ := fun i =>
  match i with
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | _ => u 0 * v 1 - u 1 * v 0

theorem crossProduct_self (u : Fin 3 → ℝ) : crossProduct u u = 0 := by
  funext i
  fin_cases i <;> simp [crossProduct] <;> ring

def sachsFromCross (C : Fin 3 → ℝ) : ScreenMat := fun i j =>
  match i, j with
  | 0, 0 => C 0
  | 0, 1 => C 1 - C 2
  | 1, 0 => C 1 + C 2
  | 1, 1 => -C 0

def minkowskiNorm21 (C : Fin 3 → ℝ) : ℝ :=
  (C 0) ^ 2 + (C 1) ^ 2 - (C 2) ^ 2

theorem sachsFromCross_isochoric (C : Fin 3 → ℝ) :
    sachsTheta (sachsFromCross C) = 0 := by
  dsimp [sachsTheta, sachsFromCross]
  ring

theorem sachsFromCross_sigma1 (C : Fin 3 → ℝ) :
    sachsSigma1 (sachsFromCross C) = C 0 := by
  dsimp [sachsSigma1, sachsFromCross]
  ring

theorem sachsFromCross_sigma2 (C : Fin 3 → ℝ) :
    sachsSigma2 (sachsFromCross C) = C 1 := by
  dsimp [sachsSigma2, sachsFromCross]
  ring

theorem sachsFromCross_omega (C : Fin 3 → ℝ) :
    sachsOmega (sachsFromCross C) = C 2 := by
  dsimp [sachsOmega, sachsFromCross]
  ring

theorem sachsFromCross_det (C : Fin 3 → ℝ) :
    detScreenMat (sachsFromCross C) = -minkowskiNorm21 C := by
  dsimp [detScreenMat, sachsFromCross, minkowskiNorm21]
  ring

theorem sachsFromCross_gain_invariant (C : Fin 3 → ℝ) :
    shearNormSq (sachsSigma1 (sachsFromCross C))
        (sachsSigma2 (sachsFromCross C)) -
      (sachsOmega (sachsFromCross C)) ^ 2 = minkowskiNorm21 C := by
  rw [sachsFromCross_sigma1, sachsFromCross_sigma2, sachsFromCross_omega]
  dsimp [shearNormSq, minkowskiNorm21]

theorem cross_self_screen_zero (u : Fin 3 → ℝ) :
    sachsFromCross (crossProduct u u) =
      (fun _ _ => 0) := by
  rw [crossProduct_self]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [sachsFromCross]

theorem transverse_collinearity_implies_twist_free
    (u v : Fin 3 → ℝ) (h : u 0 * v 1 = u 1 * v 0) :
    sachsOmega (sachsFromCross (crossProduct u v)) = 0 := by
  rw [sachsFromCross_omega]
  dsimp [crossProduct]
  linarith

theorem purely_transverse_vectors_zero_shear
    (u v : Fin 3 → ℝ) (hu : u 2 = 0) (hv : v 2 = 0) :
    sachsSigma1 (sachsFromCross (crossProduct u v)) = 0 ∧
      sachsSigma2 (sachsFromCross (crossProduct u v)) = 0 := by
  rw [sachsFromCross_sigma1, sachsFromCross_sigma2]
  dsimp [crossProduct]
  rw [hu, hv]
  constructor <;> ring

end InfoGeometry.Canonical.SachsNonAbelianCoupling
