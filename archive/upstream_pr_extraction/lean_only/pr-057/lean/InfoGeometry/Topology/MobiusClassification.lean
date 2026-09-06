import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith

open Matrix

namespace InfoGeometry

/-- A 2x2 matrix over ℂ. -/
abbrev MobiusMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- SL(2, ℂ) type as a subtype of matrices. -/
def SL2C := { M : MobiusMatrix // M.det = 1 }

instance : Coe SL2C MobiusMatrix := ⟨Subtype.val⟩

/-- The squared trace of a matrix in SL(2, ℂ). -/
noncomputable def traceSq (M : SL2C) : ℂ :=
  (M.val.trace) ^ 2

/-- Predicate for a Parabolic Möbius transformation.
    A transformation is parabolic if its squared trace is 4,
    but it is not the identity transformation (M ≠ ±I). -/
def IsParabolic (M : SL2C) : Prop :=
  traceSq M = 4 ∧ M.val ≠ 1 ∧ M.val ≠ -1

/-- Predicate for an Elliptic Möbius transformation.
    A transformation is elliptic if its squared trace is real and in [0, 4). -/
def IsElliptic (M : SL2C) : Prop :=
  ∃ (r : ℝ), 0 ≤ r ∧ r < 4 ∧ traceSq M = ↑r

/-- Predicate for a Hyperbolic Möbius transformation.
    A transformation is hyperbolic if its squared trace is real and > 4. -/
def IsHyperbolic (M : SL2C) : Prop :=
  ∃ (r : ℝ), r > 4 ∧ traceSq M = ↑r

/-- Predicate for a Loxodromic Möbius transformation.
    A transformation is loxodromic if its squared trace is not in [0, ∞).
    We define it as the complement of the other categories (including identity). -/
def IsLoxodromic (M : SL2C) : Prop :=
  ¬ (traceSq M = 4) ∧ ¬ (IsElliptic M) ∧ ¬ (IsHyperbolic M)

/-- The identity matrix has trace squared 4. -/
lemma traceSq_one_eq_four : traceSq ⟨1, by simp⟩ = 4 := by
  dsimp [traceSq]
  simp
  norm_num

/-- A Parabolic transformation is never Elliptic. -/
lemma not_elliptic_of_parabolic {M : SL2C} (h : IsParabolic M) : ¬ IsElliptic M := by
  intro h_ell
  obtain ⟨r, _hr_nonneg, hr_lt, hr_trace⟩ := h_ell
  have hr_complex : (r : ℂ) = 4 := by
    calc
      (r : ℂ) = traceSq M := by simp [hr_trace]
      _ = 4 := h.1
  have hr : r = 4 := by exact_mod_cast hr_complex
  linarith

/-- A Parabolic transformation is never Hyperbolic. -/
lemma not_hyperbolic_of_parabolic {M : SL2C} (h : IsParabolic M) : ¬ IsHyperbolic M := by
  intro h_hyp
  obtain ⟨r, hr_gt, hr_trace⟩ := h_hyp
  have hr_complex : (r : ℂ) = 4 := by
    calc
      (r : ℂ) = traceSq M := hr_trace.symm
      _ = 4 := h.1
  have hr : r = 4 := Complex.ofReal_injective hr_complex
  linarith

/-- An Elliptic transformation is never Hyperbolic. -/
lemma not_hyperbolic_of_elliptic {M : SL2C} (h : IsElliptic M) : ¬ IsHyperbolic M := by
  intro h_hyp
  obtain ⟨r₁, _, hr₁₂, hr₁₃⟩ := h
  obtain ⟨r₂, hr₂₁, hr₂₂⟩ := h_hyp
  have h₁ : traceSq M = (r₁ : ℂ) := by rw [hr₁₃]
  have h₂ : traceSq M = (r₂ : ℂ) := by rw [hr₂₂]
  have h₃ : (r₁ : ℂ) = (r₂ : ℂ) := by rw [← h₁, h₂]
  -- The coercion from ℝ to ℂ is injective, so r₁ = r₂
  have h₄ : r₁ = r₂ := by norm_cast at h₃ ⊢
  -- But r₁ < 4 and r₂ > 4, contradiction
  have h₅ : r₁ < 4 := hr₁₂
  have h₆ : r₂ > 4 := hr₂₁
  linarith

end InfoGeometry
