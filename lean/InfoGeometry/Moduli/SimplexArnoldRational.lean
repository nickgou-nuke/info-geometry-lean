import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! Rational identities for the two-point simplex chart.

This owner records the algebraic core of the simplex/three-puncture chart.  It
does not assert an identification with a moduli space or a metric theorem.
-/

namespace InfoGeometry.Moduli.SimplexArnoldRational

variable {K : Type*} [Field K]

def simplexPoint (x : ℝ) : ℝ × ℝ := (x, 1 - x)

theorem simplexPoint_normalized (x : ℝ) :
    (simplexPoint x).1 + (simplexPoint x).2 = 1 := by
  simp [simplexPoint]

theorem simplexPoint_positive (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    0 < (simplexPoint x).1 ∧ 0 < (simplexPoint x).2 := by
  simp only [simplexPoint]
  exact ⟨hx, sub_pos.mpr hx1⟩

theorem simplexPoint_injective : Function.Injective simplexPoint := by
  intro x y h
  exact congrArg Prod.fst h

theorem odds_identity (x : K) (h₀ : x ≠ 0) (h₁ : 1 - x ≠ 0) :
    1 / x + 1 / (1 - x) = 1 / (x * (1 - x)) := by
  field_simp [h₀, h₁]
  ring

def complement {K : Type*} [Ring K] (x : K) : K := 1 - x

def inverse {K : Type*} [DivisionRing K] (x : K) : K := x⁻¹

theorem complement_involution {K : Type*} [Ring K] (x : K) :
    complement (complement x) = x := by
  simp [complement]

theorem inverse_involution {K : Type*} [DivisionRing K] (x : K) :
    inverse (inverse x) = x := by
  simp [inverse]

theorem cycle_identity {K : Type*} [DivisionRing K] (x : K) (h₀ : x ≠ 0) :
    1 - x⁻¹ = (x - 1) / x := by
  rw [sub_div, div_self h₀, one_div]

theorem complement_mem_open_unit_interval (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    0 < complement x ∧ complement x < 1 := by
  constructor <;> dsimp [complement] <;> linarith

theorem odds_pos_on_open_chamber (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    0 < x / (1 - x) := by
  exact div_pos hx (sub_pos.mpr hx1)

end InfoGeometry.Moduli.SimplexArnoldRational
