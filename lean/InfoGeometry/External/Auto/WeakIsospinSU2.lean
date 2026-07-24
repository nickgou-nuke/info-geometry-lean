import Mathlib
import InfoGeometry.Physics.ChiralCausalCone
/-!
# Weak Isospin SU(2) — Pauli algebra over ℂ

All commutators verified by `ext i j; fin_cases; ring_nf; simp [Complex.I_mul_I]`.
-/

namespace WeakIsospinSU2

open Matrix
open InfoGeometry.Physics.ChiralCausalCone

def I₁ : M2C := σPlus + σMinus
def I₂ : M2C := Complex.I • (σMinus - σPlus)
def I₃ : M2C := σ3c

theorem I₁_sq : I₁ * I₁ = (1 : M2C) := by
  dsimp [I₁, σPlus, σMinus]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

theorem I₂_sq : I₂ * I₂ = (1 : M2C) := by
  dsimp [I₂, σPlus, σMinus]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Complex.I_mul_I]

theorem I₃_sq : I₃ * I₃ = (1 : M2C) := by
  dsimp [I₃, σ3c]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

theorem I₁_comm_I₂ : I₁ * I₂ - I₂ * I₁ = (2 * Complex.I) • I₃ := by
  dsimp [I₁, I₂, I₃, σPlus, σMinus, σ3c]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring_nf

theorem I₂_comm_I₃ : I₂ * I₃ - I₃ * I₂ = (2 * Complex.I) • I₁ := by
  dsimp [I₁, I₂, I₃, σPlus, σMinus, σ3c]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring_nf

theorem I₃_comm_I₁ : I₃ * I₁ - I₁ * I₃ = (2 * Complex.I) • I₂ := by
  dsimp [I₁, I₂, I₃, σPlus, σMinus, σ3c]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp

theorem su2_lie_algebra_closed :
    (I₁ * I₁ = (1 : M2C)) ∧ (I₂ * I₂ = (1 : M2C)) ∧ (I₃ * I₃ = (1 : M2C)) ∧
    (I₁ * I₂ - I₂ * I₁ = (2 * Complex.I) • I₃) ∧
    (I₂ * I₃ - I₃ * I₂ = (2 * Complex.I) • I₁) ∧
    (I₃ * I₁ - I₁ * I₃ = (2 * Complex.I) • I₂) :=
  by
    constructor
    · exact I₁_sq
    constructor
    · exact I₂_sq
    constructor
    · exact I₃_sq
    constructor
    · exact I₁_comm_I₂
    constructor
    · exact I₂_comm_I₃
    · exact I₃_comm_I₁

end WeakIsospinSU2
