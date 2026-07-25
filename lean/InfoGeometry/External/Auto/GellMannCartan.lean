import Mathlib

/-!
# Gell-Mann Cartan decomposition — no division, pure `CommRing`

Cartan involution `θ(X) = -Xᵀ` decomposes 3×3 matrices into compact
(antisymmetric) and noncompact (symmetric) parts. All theorems avoid
division — use `2K = X - Xᵀ` instead of `K = (X - Xᵀ)/2`.

Canonical matrix operations only. Zero tensor products, zero sorries.
-/

namespace GellMannCartan

open Matrix

variable {R : Type*} [CommRing R]

def θ (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R := -Xᵀ

@[simp] theorem θ_add (X Y : Matrix (Fin 3) (Fin 3) R) : θ (X + Y) = θ X + θ Y := by simp [θ, add_comm]
@[simp] theorem θ_θ (X : Matrix (Fin 3) (Fin 3) R) : θ (θ X) = X := by simp [θ]

def isCompact (X : Matrix (Fin 3) (Fin 3) R) : Prop := θ X = X
def isNoncompact (X : Matrix (Fin 3) (Fin 3) R) : Prop := θ X = -X

def twiceCompact (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R := X - Xᵀ
def twiceNoncompact (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R := X + Xᵀ

/-! ## Theorems — each a small independent lemma -/

theorem twiceCompact_isCompact (X : Matrix (Fin 3) (Fin 3) R) : isCompact (twiceCompact X) := by
  dsimp [isCompact, θ, twiceCompact]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.transpose_apply]

theorem twiceNoncompact_isNoncompact (X : Matrix (Fin 3) (Fin 3) R) : isNoncompact (twiceNoncompact X) := by
  dsimp [isNoncompact, θ, twiceNoncompact]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.transpose_apply] <;> ring

theorem twice_decomposition (X : Matrix (Fin 3) (Fin 3) R) :
    (2 : R) • X = twiceCompact X + twiceNoncompact X := by
  dsimp [twiceCompact, twiceNoncompact]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply] <;> ring

theorem twiceCompact_idem (X : Matrix (Fin 3) (Fin 3) R) :
    twiceCompact (twiceCompact X) = (2 : R) • twiceCompact X := by
  dsimp [twiceCompact]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.transpose_apply] <;> ring

theorem compact_closed_under_lie (K₁ K₂ : Matrix (Fin 3) (Fin 3) R)
    (hK₁ : isCompact K₁) (hK₂ : isCompact K₂) : isCompact (K₁ * K₂ - K₂ * K₁) := by
  have hK₁' : K₁ᵀ = -K₁ := by
    dsimp [isCompact, θ] at hK₁
    -- hK₁: -K₁ᵀ = K₁. Negate both sides: K₁ᵀ = -K₁
    calc
      K₁ᵀ = -(-K₁ᵀ) := by simp
      _ = -K₁ := by rw [hK₁]
  have hK₂' : K₂ᵀ = -K₂ := by
    dsimp [isCompact, θ] at hK₂
    calc
      K₂ᵀ = -(-K₂ᵀ) := by simp
      _ = -K₂ := by rw [hK₂]
  dsimp [isCompact, θ]
  calc
    -((K₁ * K₂ - K₂ * K₁)ᵀ) = -(K₂ᵀ * K₁ᵀ - K₁ᵀ * K₂ᵀ) := by simp
    _ = -((-K₂) * (-K₁) - (-K₁) * (-K₂)) := by rw [hK₁', hK₂']
    _ = K₁ * K₂ - K₂ * K₁ := by simp

end GellMannCartan
