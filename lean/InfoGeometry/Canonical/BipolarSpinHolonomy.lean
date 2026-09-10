import InfoGeometry.Analysis.BipolarWindingPeriodLattice
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Spinorial holonomy of the bipolar winding lattice

The logarithmic differential has period `(m-n) * 2πi` on the explicit
winding lattice `ℤ × ℤ`.  Applying the half-Cartan character gives the diagonal
matrix

`diag(exp(period/2), exp(-period/2))`.

This file proves purely algebraically that either elementary puncture winding
has central holonomy `-I₂`, while the combined winding has holonomy `I₂`.
Thus two elementary half-Cartan monodromies close after two turns.

No contour-integral construction, gauge bundle, Aharonov--Bohm experiment, or
Riemann-zero interpretation is asserted.  The input period map is the explicit
algebraic owner in `BipolarWindingPeriodLattice`.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarSpinHolonomy

open InfoGeometry.Analysis.BipolarWindingPeriodLattice

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Half-Cartan holonomy associated with an algebraic winding pair. -/
def spinHolonomy (w : WindingPair) : M2C :=
  !![Complex.exp (circulationPeriod w / 2), 0;
     0, Complex.exp (-circulationPeriod w / 2)]

/-- Every half-Cartan holonomy has determinant one. -/
theorem spinHolonomy_det (w : WindingPair) :
    Matrix.det (spinHolonomy w) = 1 := by
  rw [Matrix.det_fin_two]
  change
    Complex.exp (circulationPeriod w / 2) *
        Complex.exp (-circulationPeriod w / 2) - 0 * 0 = 1
  rw [zero_mul, sub_zero, ← Complex.exp_add]
  have hzero : circulationPeriod w / 2 + -circulationPeriod w / 2 = 0 := by
    ring
  rw [hzero, Complex.exp_zero]

/-- Additivity of the period map in native product-addition notation. -/
theorem circulationPeriod_add_pair (u v : WindingPair) :
    circulationPeriod (u + v) = circulationPeriod u + circulationPeriod v := by
  rcases u with ⟨u₀, u₁⟩
  rcases v with ⟨v₀, v₁⟩
  simpa using circulationPeriod_add (u₀, u₁) (v₀, v₁)

/-- The half-Cartan holonomy is multiplicative on the winding lattice. -/
theorem spinHolonomy_add (u v : WindingPair) :
    spinHolonomy (u + v) = spinHolonomy u * spinHolonomy v := by
  have hp :
      circulationPeriod (u + v) / 2 =
        circulationPeriod u / 2 + circulationPeriod v / 2 := by
    rw [circulationPeriod_add_pair]
    ring
  have hm :
      -circulationPeriod (u + v) / 2 =
        -circulationPeriod u / 2 + -circulationPeriod v / 2 := by
    rw [circulationPeriod_add_pair]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHolonomy, Matrix.mul_apply, Fin.sum_univ_two,
      hp, hm, Complex.exp_add]

lemma exp_origin_half_period :
    Complex.exp (circulationPeriod originWinding / 2) = -1 := by
  rw [circulationPeriod_origin]
  have harg :
      (2 * Real.pi * Complex.I : ℂ) / 2 = Real.pi * Complex.I := by
    ring
  rw [harg]
  exact Complex.exp_pi_mul_I

lemma exp_neg_origin_half_period :
    Complex.exp (-circulationPeriod originWinding / 2) = -1 := by
  rw [circulationPeriod_origin]
  have harg :
      -(2 * Real.pi * Complex.I : ℂ) / 2 = -(Real.pi * Complex.I) := by
    ring
  rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I]
  simp

lemma exp_one_half_period :
    Complex.exp (circulationPeriod oneWinding / 2) = -1 := by
  rw [circulationPeriod_one]
  have harg :
      -(2 * Real.pi * Complex.I : ℂ) / 2 = -(Real.pi * Complex.I) := by
    ring
  rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I]
  simp

lemma exp_neg_one_half_period :
    Complex.exp (-circulationPeriod oneWinding / 2) = -1 := by
  rw [circulationPeriod_one]
  have harg :
      -(-(2 * Real.pi * Complex.I : ℂ)) / 2 = Real.pi * Complex.I := by
    ring
  rw [harg]
  exact Complex.exp_pi_mul_I

/-- A loop around the origin has the central spinorial sign `-I₂`. -/
theorem spinHolonomy_origin :
    spinHolonomy originWinding = -(1 : M2C) := by
  have hplus : Complex.exp (2 * Real.pi * Complex.I / 2) = (-1 : ℂ) := by
    rw [show 2 * Real.pi * Complex.I / 2 = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have hminus : Complex.exp (-(2 * Real.pi * Complex.I) / 2) = (-1 : ℂ) := by
    rw [show -(2 * Real.pi * Complex.I) / 2 = -(Real.pi * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHolonomy, hplus, hminus]

/-- A loop around the second puncture has the same central sign. -/
theorem spinHolonomy_one :
    spinHolonomy oneWinding = -(1 : M2C) := by
  have hplus : Complex.exp (2 * Real.pi * Complex.I / 2) = (-1 : ℂ) := by
    rw [show 2 * Real.pi * Complex.I / 2 = Real.pi * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  have hminus : Complex.exp (-(2 * Real.pi * Complex.I) / 2) = (-1 : ℂ) := by
    rw [show -(2 * Real.pi * Complex.I) / 2 = -(Real.pi * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHolonomy, hplus, hminus]

/-- Equal winding around both punctures has trivial half-Cartan holonomy because
this residue-difference form has zero diagonal period. -/
theorem spinHolonomy_diagonal (n : ℤ) :
    spinHolonomy (diagonalWinding n) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinHolonomy, circulationPeriod_diagonal]

/-- The sum of the two elementary windings is the unit diagonal winding. -/
theorem origin_add_one_eq_diagonal :
    originWinding + oneWinding = diagonalWinding 1 := by
  norm_num [originWinding, oneWinding, diagonalWinding]

/-- Encircling both finite punctures therefore has trivial holonomy. -/
theorem spinHolonomy_origin_add_one :
    spinHolonomy (originWinding + oneWinding) = 1 := by
  rw [origin_add_one_eq_diagonal, spinHolonomy_diagonal]

/-- Two turns around either elementary puncture return to the identity. -/
theorem spinHolonomy_origin_sq :
    spinHolonomy originWinding * spinHolonomy originWinding = 1 := by
  rw [spinHolonomy_origin]
  simp

/-- The corresponding two-turn theorem for the second puncture. -/
theorem spinHolonomy_one_sq :
    spinHolonomy oneWinding * spinHolonomy oneWinding = 1 := by
  rw [spinHolonomy_one]
  simp

/-- The one-turn sign is genuinely nontrivial over `ℂ`. -/
theorem spinHolonomy_origin_ne_one :
    spinHolonomy originWinding ≠ (1 : M2C) := by
  rw [spinHolonomy_origin]
  intro h
  have h00 := congrArg (fun M : M2C => M 0 0) h
  norm_num at h00

/-- Compact holonomy packet. -/
theorem bipolar_spin_holonomy_packet :
    spinHolonomy originWinding = -(1 : M2C) ∧
      spinHolonomy oneWinding = -(1 : M2C) ∧
      spinHolonomy (originWinding + oneWinding) = 1 ∧
      spinHolonomy originWinding * spinHolonomy originWinding = 1 := by
  exact ⟨spinHolonomy_origin, spinHolonomy_one,
    spinHolonomy_origin_add_one, spinHolonomy_origin_sq⟩

end InfoGeometry.Canonical.BipolarSpinHolonomy
