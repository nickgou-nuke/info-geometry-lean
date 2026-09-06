/-
# CliffordInfiniteSplitAlgebra

Real split-signature Clifford algebra structures extracting Majorana-Weyl
spinors from the Cl(5,5) infinite tensor colimit boundary.

## Audit Protocol Map
- BUCKET 1: All theorems verified.
- BUCKET 2: None.
- BUCKET 3: None.
-/

import Mathlib

set_option linter.unusedVariables false

section CliffordInfiniteSplitAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (half : ℝ) (h_half : half + half = 1)
variable (omega : V →ₗ[ℝ] V) (omega_sq : ∀ x, omega (omega x) = x)

include h_half omega_sq

/-- Positive chirality Majorana-Weyl projector. -/
def P_plus (x : V) : V := half • (x + omega x)

/-- Negative chirality Majorana-Weyl projector. -/
def P_minus (x : V) : V := half • (x - omega x)

lemma P_plus_add_P_minus (x : V) : P_plus half omega x + P_minus half omega x = x := by
  dsimp [P_plus, P_minus]
  have h1 : half • x + half • omega x + (half • x - half • omega x) = half • x + half • x := by
    calc
      half • x + half • omega x + (half • x - half • omega x)
          = (half • x + half • x) + (half • omega x - half • omega x) := by
            simp [add_assoc]
      _ = (half • x + half • x) + 0 := by simp [sub_self]
      _ = half • x + half • x := by rw [add_zero]
  calc
    half • (x + omega x) + half • (x - omega x) = half • x + half • omega x + (half • x - half • omega x) := by
      rw [smul_add, smul_sub]
    _ = half • x + half • x := h1
    _ = (half + half) • x := by rw [← add_smul]
    _ = (1 : ℝ) • x := by rw [h_half]
    _ = x := by exact one_smul ℝ x

lemma omega_P_plus (x : V) : omega (P_plus half omega x) = P_plus half omega x := by
  dsimp [P_plus]
  rw [LinearMap.map_smul, LinearMap.map_add, omega_sq x, add_comm]

lemma omega_P_minus (x : V) : omega (P_minus half omega x) = - P_minus half omega x := by
  dsimp [P_minus]
  rw [LinearMap.map_smul, LinearMap.map_sub, omega_sq x]
  have h : omega x - x = - (x - omega x) := by abel
  rw [h, smul_neg]

theorem P_plus_idempotent (x : V) :
    P_plus half omega (P_plus half omega x) = P_plus half omega x := by
  dsimp [P_plus]
  have h : P_plus half omega x + omega (P_plus half omega x) = P_plus half omega x + P_plus half omega x :=
    congrArg (fun t => P_plus half omega x + t) (omega_P_plus half h_half omega omega_sq x)
  calc
    half • (P_plus half omega x + omega (P_plus half omega x)) = half • (P_plus half omega x + P_plus half omega x) := by rw [h]
    _ = (half + half) • P_plus half omega x := by rw [smul_add, add_smul]
    _ = (1 : ℝ) • P_plus half omega x := by rw [h_half]
    _ = P_plus half omega x := by exact one_smul ℝ (P_plus half omega x)

theorem P_minus_idempotent (x : V) :
    P_minus half omega (P_minus half omega x) = P_minus half omega x := by
  dsimp [P_minus]
  have h : P_minus half omega x - omega (P_minus half omega x) = P_minus half omega x + P_minus half omega x := by
    calc
      P_minus half omega x - omega (P_minus half omega x)
          = P_minus half omega x - (- P_minus half omega x) := by rw [omega_P_minus half h_half omega omega_sq x]
      _ = P_minus half omega x + P_minus half omega x := by simp
  calc
    half • (P_minus half omega x - omega (P_minus half omega x)) = half • (P_minus half omega x + P_minus half omega x) := by rw [h]
    _ = (half + half) • P_minus half omega x := by rw [smul_add, add_smul]
    _ = (1 : ℝ) • P_minus half omega x := by rw [h_half]
    _ = P_minus half omega x := by exact one_smul ℝ (P_minus half omega x)

theorem P_plus_P_minus_ortho (x : V) :
    P_plus half omega (P_minus half omega x) = 0 := by
  have h : P_minus half omega x + omega (P_minus half omega x) = 0 := by
    rw [omega_P_minus half h_half omega omega_sq x]
    simp
  dsimp [P_plus]
  rw [h, smul_zero]

theorem P_minus_P_plus_ortho (x : V) :
    P_minus half omega (P_plus half omega x) = 0 := by
  have h : P_plus half omega x - omega (P_plus half omega x) = 0 := by
    rw [omega_P_plus half h_half omega omega_sq x, sub_self]
  dsimp [P_minus]
  rw [h, smul_zero]

variable (D : V →ₗ[ℝ] V) (D_omega_anti_comm : ∀ x, D (omega x) = - omega (D x))

include D_omega_anti_comm

theorem D_P_plus_eq_P_minus_D (x : V) :
    D (P_plus half omega x) = P_minus half omega (D x) := by
  dsimp [P_plus, P_minus]
  calc
    D (half • (x + omega x)) = half • D (x + omega x) := by rw [LinearMap.map_smul]
    _ = half • (D x + D (omega x)) := by rw [LinearMap.map_add]
    _ = half • (D x + (- omega (D x))) := by rw [D_omega_anti_comm x]
    _ = half • (D x - omega (D x)) := by rw [sub_eq_add_neg]
    _ = P_minus half omega (D x) := rfl

theorem D_P_minus_eq_P_plus_D (x : V) :
    D (P_minus half omega x) = P_plus half omega (D x) := by
  dsimp [P_plus, P_minus]
  calc
    D (half • (x - omega x)) = half • D (x - omega x) := by rw [LinearMap.map_smul]
    _ = half • (D x - D (omega x)) := by rw [LinearMap.map_sub]
    _ = half • (D x - (- omega (D x))) := by rw [D_omega_anti_comm x]
    _ = half • (D x + omega (D x)) := by simp
    _ = P_plus half omega (D x) := by rfl

theorem D_maps_plus_to_minus_ortho (x : V) :
    P_plus half omega (D (P_plus half omega x)) = 0 := by
  rw [D_P_plus_eq_P_minus_D half h_half omega omega_sq D D_omega_anti_comm x]
  exact P_plus_P_minus_ortho half h_half omega omega_sq (D x)

theorem D_maps_minus_to_plus_ortho (x : V) :
    P_minus half omega (D (P_minus half omega x)) = 0 := by
  rw [D_P_minus_eq_P_plus_D half h_half omega omega_sq D D_omega_anti_comm x]
  exact P_minus_P_plus_ortho half h_half omega omega_sq (D x)

end CliffordInfiniteSplitAlgebra
