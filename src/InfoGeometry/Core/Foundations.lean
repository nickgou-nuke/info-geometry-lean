import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import InfoGeometry.Core.TitsExhaustion

namespace InfoGeometry.Foundations

/-! The regular commutant is owned by
`InfoGeometry.Algebra.AssociativeRegularCommutant`; it is not duplicated here. -/

section LinearExtraction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem degree_four_linear_coefficient
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : V}
    (h : ∀ t : ℝ,
      a₀ + t • a₁ + (t^2) • a₂ + (t^3) • a₃ + (t^4) • a₄ =
        b₀ + t • b₁ + (t^2) • b₂ + (t^3) • b₃ + (t^4) • b₄) :
    a₁ = b₁ := by
  let P : ℝ → V := fun t =>
    a₀ + t • a₁ + (t^2) • a₂ + (t^3) • a₃ + (t^4) • a₄
  let Q : ℝ → V := fun t =>
    b₀ + t • b₁ + (t^2) • b₂ + (t^3) • b₃ + (t^4) • b₄
  have hPQ : ∀ t : ℝ, P t = Q t := fun t => h t
  have ha : a₁ = (2 / 3 : ℝ) • (P 1 - P (-1)) -
      (1 / 12 : ℝ) • (P 2 - P (-2)) := by
    dsimp [P]
    norm_num
    module
  have hb : b₁ = (2 / 3 : ℝ) • (Q 1 - Q (-1)) -
      (1 / 12 : ℝ) • (Q 2 - Q (-2)) := by
    dsimp [Q]
    norm_num
    module
  calc
    a₁ = (2 / 3 : ℝ) • (P 1 - P (-1)) -
        (1 / 12 : ℝ) • (P 2 - P (-2)) := ha
    _ = (2 / 3 : ℝ) • (Q 1 - Q (-1)) -
        (1 / 12 : ℝ) • (Q 2 - Q (-2)) := by
      rw [hPQ 1, hPQ (-1), hPQ 2, hPQ (-2)]
    _ = b₁ := hb.symm

theorem degree_four_odd_difference_one
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : V}
    (h : ∀ t : ℝ,
      a₀ + t • a₁ + (t ^ 2) • a₂ + (t ^ 3) • a₃ + (t ^ 4) • a₄ =
        b₀ + t • b₁ + (t ^ 2) • b₂ + (t ^ 3) • b₃ + (t ^ 4) • b₄) :
    (2 : ℝ) • (a₁ - b₁) + (2 : ℝ) • (a₃ - b₃) = 0 := by
  have h₁ := h (1 : ℝ)
  have hm1 := h (-1 : ℝ)
  have h₁z := sub_eq_zero.mpr h₁
  have hm1z := sub_eq_zero.mpr hm1
  norm_num at h₁z hm1z
  calc
    (2 : ℝ) • (a₁ - b₁) + (2 : ℝ) • (a₃ - b₃) =
        (a₀ + a₁ + a₂ + a₃ + a₄ - (b₀ + b₁ + b₂ + b₃ + b₄)) -
          (a₀ + -a₁ + a₂ + -a₃ + a₄ -
            (b₀ + -b₁ + b₂ + -b₃ + b₄)) := by module
    _ = 0 - 0 := by rw [h₁z, hm1z]
    _ = 0 := by simp

theorem degree_four_odd_difference_two
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : V}
    (h : ∀ t : ℝ,
      a₀ + t • a₁ + (t ^ 2) • a₂ + (t ^ 3) • a₃ + (t ^ 4) • a₄ =
        b₀ + t • b₁ + (t ^ 2) • b₂ + (t ^ 3) • b₃ + (t ^ 4) • b₄) :
    (4 : ℝ) • (a₁ - b₁) + (16 : ℝ) • (a₃ - b₃) = 0 := by
  have h₂ := h (2 : ℝ)
  have hm2 := h (-2 : ℝ)
  have h₂z := sub_eq_zero.mpr h₂
  have hm2z := sub_eq_zero.mpr hm2
  norm_num at h₂z hm2z
  have hd := congrArg₂ Sub.sub h₂z hm2z
  calc
    (4 : ℝ) • (a₁ - b₁) + (16 : ℝ) • (a₃ - b₃) =
        (a₀ + 2 • a₁ + 4 • a₂ + 8 • a₃ + 16 • a₄ -
            (b₀ + 2 • b₁ + 4 • b₂ + 8 • b₃ + 16 • b₄)) -
          (a₀ + -(2 • a₁) + 4 • a₂ + -(8 • a₃) + 16 • a₄ -
            (b₀ + -(2 • b₁) + 4 • b₂ + -(8 • b₃) + 16 • b₄)) := by module
    _ = 0 - 0 := hd
    _ = 0 := by simp

theorem degree_four_linear_elimination
    {a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ : V}
    (h : ∀ t : ℝ,
      a₀ + t • a₁ + (t ^ 2) • a₂ + (t ^ 3) • a₃ + (t ^ 4) • a₄ =
        b₀ + t • b₁ + (t ^ 2) • b₂ + (t ^ 3) • b₃ + (t ^ 4) • b₄) :
    (12 : ℝ) • (a₁ - b₁) = 0 := by
  have hab := degree_four_linear_coefficient h
  rw [hab]
  simp

end LinearExtraction

section IdempotentCorner

variable {A : Type*} [Semigroup A]

def principalLeftIdeal (f : A) : Set A := {x | ∃ a, x = a * f}
def principalRightIdeal (f : A) : Set A := {x | ∃ a, x = f * a}
def cornerSet (f : A) : Set A := {x | ∃ a, x = f * a * f}

theorem right_ideal_mul_left_ideal_in_corner (f : A) {φ ψ : A}
    (hφ : φ ∈ principalRightIdeal f) (hψ : ψ ∈ principalLeftIdeal f) :
    φ * ψ ∈ cornerSet f := by
  rcases hφ with ⟨a, rfl⟩
  rcases hψ with ⟨b, rfl⟩
  exact ⟨a * b, by simp only [mul_assoc]⟩

theorem idempotent_absorb_left (f : A) (hf : f * f = f) {x : A}
    (hx : x ∈ principalLeftIdeal f) : x * f = x := by
  rcases hx with ⟨a, rfl⟩
  rw [mul_assoc, hf]

theorem idempotent_absorb_right (f : A) (hf : f * f = f) {x : A}
    (hx : x ∈ principalRightIdeal f) : f * x = x := by
  rcases hx with ⟨a, rfl⟩
  rw [← mul_assoc, hf]

theorem idempotent_corner_absorb_left (f : A) (hf : f * f = f) {x : A}
    (hx : x ∈ cornerSet f) : f * x = x := by
  rcases hx with ⟨a, rfl⟩
  calc
    f * (f * a * f) = (f * f) * a * f := by simp only [mul_assoc]
    _ = f * a * f := by rw [hf]

theorem idempotent_corner_absorb_right (f : A) (hf : f * f = f) {x : A}
    (hx : x ∈ cornerSet f) : x * f = x := by
  rcases hx with ⟨a, rfl⟩
  calc
    (f * a * f) * f = f * a * (f * f) := by simp only [mul_assoc]
    _ = f * a * f := by rw [hf]

end IdempotentCorner

end InfoGeometry.Foundations
