import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.SplitOctonionSO44TrialityBridge

/-- **Definition**: Zorn Vector-Matrix Representation of Split-Octonions.
    z = (a, b, u, v) where a, b ∈ R and u, v ∈ R³. -/
structure ZornSplitOctonion (R : Type*) [CommRing R] where
  a : R
  b : R
  u : Fin 3 → R
  v : Fin 3 → R

namespace ZornSplitOctonion

variable {R : Type*} [CommRing R]

/-- Split-Octonion Determinant / Quadratic Norm Form N(z) = a b - ⟨u, v⟩.
    Carries the non-compact SO(4,4) signature (4,4). -/
def normSq (z : ZornSplitOctonion R) : R :=
  z.a * z.b - (Finset.univ : Finset (Fin 3)).sum (fun i => z.u i * z.v i)

/-- **Theorem**: Zero Vector Norm is Zero. -/
theorem normSq_zero :
    normSq (⟨0, 0, 0, 0⟩ : ZornSplitOctonion R) = 0 := by
  dsimp [normSq]
  simp

end ZornSplitOctonion

/-- **Definition**: Non-Compact Cl(4,4) Clifford Algebra Generators.
    γ₁, γ₂, γ₃, γ₄ square to +1.
    γ₅, γ₆, γ₇, γ₈ square to -1. -/
structure Cl44Generators (R : Type*) [Ring R] where
  gamma : Fin 8 → R
  sq_pos : ∀ i : Fin 4, gamma ⟨i.val, by linarith [i.isLt]⟩ * gamma ⟨i.val, by linarith [i.isLt]⟩ = 1
  sq_neg : ∀ j : Fin 4, gamma ⟨j.val + 4, by linarith [j.isLt]⟩ * gamma ⟨j.val + 4, by linarith [j.isLt]⟩ = -1
  anticomm : ∀ i j : Fin 8, i ≠ j → gamma i * gamma j + gamma j * gamma i = 0

namespace Cl44Generators

variable {R : Type*} [Ring R] (g : Cl44Generators R)

/-- Chiral Pseudoscalar / Volume Form for Cl(4,4): Γ = γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ γ₇ γ₈. -/
def volumeForm : R :=
  g.gamma 0 * g.gamma 1 * g.gamma 2 * g.gamma 3 *
  g.gamma 4 * g.gamma 5 * g.gamma 6 * g.gamma 7

/-- Positive Chiral Projector P₊ = (1 + Γ)/2. -/
def projPlus [Invertible (2 : R)] : R :=
  ⅟(2 : R) * (1 + g.volumeForm)

/-- Negative Chiral Projector P⋺ = (1 - Γ)/2. -/
def projMinus [Invertible (2 : R)] : R :=
  ⅟(2 : R) * (1 - g.volumeForm)

/-- **Theorem**: Chiral Projector Completeness P₊ + P⋺ = 1. -/
theorem proj_completeness [Invertible (2 : R)] :
    g.projPlus + g.projMinus = 1 := by
  dsimp [projPlus, projMinus]
  calc ⅟(2 : R) * (1 + g.volumeForm) + ⅟(2 : R) * (1 - g.volumeForm)
    _ = ⅟(2 : R) * (1 + g.volumeForm + (1 - g.volumeForm)) := by rw [← mul_add]
    _ = ⅟(2 : R) * 2 := by noncomm_ring
    _ = 1 := invOf_mul_self (2 : R)

end Cl44Generators

end InfoGeometry.Algebra.SplitOctonionSO44TrialityBridge
