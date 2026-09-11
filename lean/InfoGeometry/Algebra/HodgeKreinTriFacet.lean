import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

section HodgeKreinTriFacet

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

-- Generalized tri-facet operator O matching the Hodge-Krein Super-Laplacian
def P_ext (O : V →ₗ[ℝ] V) (half : ℝ) (x : V) : V := half • (O (O x) + O x)
def P_coext (O : V →ₗ[ℝ] V) (half : ℝ) (x : V) : V := half • (O (O x) - O x)
def P_harm (O : V →ₗ[ℝ] V) (x : V) : V := x - O (O x)
def P_core (O : V →ₗ[ℝ] V) (x : V) : V := O (O x)

lemma P_ext_add_P_coext (O : V →ₗ[ℝ] V) (half : ℝ) (h_half : half + half = 1) (x : V) :
    P_ext O half x + P_coext O half x = O (O x) := by
  dsimp [P_ext, P_coext]
  rw [smul_add, smul_sub]
  have h : half • O (O x) + half • O x + (half • O (O x) - half • O x) = half • O (O x) + half • O (O x) := by abel
  rw [h, ← add_smul, h_half, one_smul]

theorem tri_facet_sum (O : V →ₗ[ℝ] V) (half : ℝ) (h_half : half + half = 1) (x : V) :
    P_ext O half x + P_coext O half x + P_harm O x = x := by
  rw [P_ext_add_P_coext O half h_half x]
  dsimp [P_harm]
  abel

lemma P_harm_idempotent (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (x : V) :
    P_harm O (P_harm O x) = P_harm O x := by
  dsimp [P_harm]
  rw [LinearMap.map_sub, LinearMap.map_sub, hO3 x, show O (O x) - O (O x) = (0 : V) from sub_self _, sub_zero]

lemma O_O_P_ext (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    O (O (P_ext O half x)) = P_ext O half x := by
  dsimp [P_ext]
  rw [LinearMap.map_smul, LinearMap.map_smul]
  rw [LinearMap.map_add, LinearMap.map_add]
  have h1 : O (O (O (O x))) = O (O x) := hO3 (O x)
  rw [h1, hO3 x]

lemma O_P_ext (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    O (P_ext O half x) = P_ext O half x := by
  dsimp [P_ext]
  rw [LinearMap.map_smul, LinearMap.map_add]
  rw [hO3 x, add_comm]

lemma O_O_P_coext (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    O (O (P_coext O half x)) = P_coext O half x := by
  dsimp [P_coext]
  rw [LinearMap.map_smul, LinearMap.map_smul]
  rw [LinearMap.map_sub, LinearMap.map_sub]
  have h1 : O (O (O (O x))) = O (O x) := hO3 (O x)
  rw [h1, hO3 x]

lemma O_P_coext (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    O (P_coext O half x) = - P_coext O half x := by
  dsimp [P_coext]
  rw [LinearMap.map_smul, LinearMap.map_sub]
  rw [hO3 x]
  have h : O x - O (O x) = - (O (O x) - O x) := by abel
  rw [h, smul_neg]

theorem P_ext_idempotent (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (h_half : half + half = 1) (x : V) :
    P_ext O half (P_ext O half x) = P_ext O half x := by
  dsimp [P_ext]
  have hOO : O (O (half • (O (O x) + O x))) = half • (O (O x) + O x) := by
    simpa [P_ext] using O_O_P_ext O hO3 half x
  have hO : O (half • (O (O x) + O x)) = half • (O (O x) + O x) := by
    simpa [P_ext] using O_P_ext O hO3 half x
  rw [hOO, hO]
  set a := O (O x) + O x
  calc
    half • (half • a + half • a) = half • (half • a) + half • (half • a) := by rw [smul_add]
    _ = ((half : ℝ) * half) • a + ((half : ℝ) * half) • a := by simp [smul_smul]
    _ = ((half : ℝ) * half + half * half) • a := by rw [add_smul]
    _ = (half : ℝ) • a := by
      have h_sq : (half : ℝ) * half + half * half = half := by nlinarith
      rw [h_sq]
    _ = half • a := rfl

theorem P_coext_idempotent (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (h_half : half + half = 1) (x : V) :
    P_coext O half (P_coext O half x) = P_coext O half x := by
  dsimp [P_coext]
  have hOO : O (O (half • (O (O x) - O x))) = half • (O (O x) - O x) := by
    simpa [P_coext] using O_O_P_coext O hO3 half x
  have hO : O (half • (O (O x) - O x)) = -(half • (O (O x) - O x)) := by
    simpa [P_coext] using O_P_coext O hO3 half x
  rw [hOO, hO]
  set a := O (O x) - O x
  calc
    half • (half • a - (-(half • a))) = half • (half • a + half • a) := by abel
    _ = half • (half • a) + half • (half • a) := by rw [smul_add]
    _ = ((half : ℝ) * half) • a + ((half : ℝ) * half) • a := by simp [smul_smul]
    _ = ((half : ℝ) * half + half * half) • a := by rw [add_smul]
    _ = (half : ℝ) • a := by
      have h_sq : (half : ℝ) * half + half * half = half := by nlinarith
      rw [h_sq]
    _ = half • a := rfl

theorem P_harm_P_ext (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    P_harm O (P_ext O half x) = 0 := by
  dsimp [P_harm]
  rw [O_O_P_ext O hO3 half x, sub_self]

theorem P_harm_P_coext (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    P_harm O (P_coext O half x) = 0 := by
  dsimp [P_harm]
  rw [O_O_P_coext O hO3 half x, sub_self]

theorem P_ext_P_coext (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    P_ext O half (P_coext O half x) = 0 := by
  dsimp [P_ext]
  rw [O_O_P_coext O hO3 half x, O_P_coext O hO3 half x]
  have h : P_coext O half x + (-P_coext O half x) = 0 := by abel
  rw [h, smul_zero]

theorem P_coext_P_ext (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    P_coext O half (P_ext O half x) = 0 := by
  dsimp [P_coext]
  rw [O_O_P_ext O hO3 half x, O_P_ext O hO3 half x]
  have h : P_ext O half x - P_ext O half x = 0 := by abel
  rw [h, smul_zero]

lemma O_P_harm (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (x : V) :
    O (P_harm O x) = 0 := by
  dsimp [P_harm]
  rw [LinearMap.map_sub, hO3 x, sub_self]

lemma O_O_P_harm (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (x : V) :
    O (O (P_harm O x)) = 0 := by
  rw [O_P_harm O hO3 x, LinearMap.map_zero]

theorem P_ext_P_harm (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    P_ext O half (P_harm O x) = 0 := by
  dsimp [P_ext]
  rw [O_O_P_harm O hO3 x, O_P_harm O hO3 x, add_zero, smul_zero]

theorem P_coext_P_harm (O : V →ₗ[ℝ] V) (hO3 : ∀ x, O (O (O x)) = O x) (half : ℝ) (x : V) :
    P_coext O half (P_harm O x) = 0 := by
  dsimp [P_coext]
  rw [O_O_P_harm O hO3 x, O_P_harm O hO3 x, sub_zero, smul_zero]

theorem P_core_eq_ext_add_coext (O : V →ₗ[ℝ] V) (half : ℝ) (h_half : half + half = 1) (x : V) :
    P_core O x = P_ext O half x + P_coext O half x := by
  rw [P_ext_add_P_coext O half h_half x]
  rfl

theorem P_core_add_P_harm (O : V →ₗ[ℝ] V) (x : V) :
    P_core O x + P_harm O x = x := by
  dsimp [P_core, P_harm]
  abel

end HodgeKreinTriFacet
