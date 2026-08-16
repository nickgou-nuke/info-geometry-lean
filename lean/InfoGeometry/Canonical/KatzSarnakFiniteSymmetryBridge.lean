import Mathlib.Tactic

/-!
# Katz--Sarnak Finite Symmetry Bridge

This module records the finite, kernel-checkable algebra behind the classical
compact symmetry labels that appear in Katz--Sarnak random-matrix heuristics.

It proves only the closed finite corridor:

* a real two-dimensional rotation matrix with `a^2 + b^2 = 1` is orthogonal;
* the same matrix preserves the standard symplectic form in dimension two;
* the associated complex phase has norm square one.

#### BUCKET 1: CLOSED FINITE THEOREMS
`rotation2_orthogonal`, `rotation2_symplectic`, and `complexPhase_normSq`
are closed finite algebraic identities.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
All three main theorems depend on the explicit normalization premise
`a * a + b * b = 1`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove Katz--Sarnak density conjectures, GUE universality,
low-lying zero statistics, Frobenius equidistribution, monodromy theorems,
or any Riemann-zeta zero statement.
-/

noncomputable section

namespace InfoGeometry.Canonical.KatzSarnakFiniteSymmetryBridge

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- The standard real `2 × 2` rotation atom. -/
def rotation2 (a b : ℝ) : M2R :=
  !![a, -b;
     b, a]

/-- The standard symplectic form on `ℝ²`. -/
def symplecticJ : M2R :=
  !![0, -1;
     1, 0]

/-- The complex phase corresponding to the same real coordinates. -/
def complexPhase (a b : ℝ) : ℂ :=
  ⟨a, b⟩

/-- Composition law for the finite real rotation atoms. -/
theorem rotation2_mul (a b c d : ℝ) :
    rotation2 a b * rotation2 c d =
      rotation2 (a * c - b * d) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Explicit coordinate form of the transpose rotation. -/
theorem rotation2_transpose (a b : ℝ) :
    (rotation2 a b)ᵀ = rotation2 a (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation2]

/-- The transpose is the inverse rotation on the unit circle. -/
theorem rotation2_mul_transpose {a b : ℝ} (h : a * a + b * b = 1) :
    rotation2 a b * (rotation2 a b)ᵀ = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals nlinarith [h]

/--
The finite unitary readout: `a + ib` has norm square one whenever
`a^2 + b^2 = 1`.
-/
theorem complexPhase_normSq {a b : ℝ} (h : a * a + b * b = 1) :
    Complex.normSq (complexPhase a b) = 1 := by
  simp [complexPhase, Complex.normSq]
  exact h

/--
The real rotation atom is orthogonal under the same unit-circle premise.
-/
theorem rotation2_orthogonal {a b : ℝ} (h : a * a + b * b = 1) :
    (rotation2 a b)ᵀ * rotation2 a b = (1 : M2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation2, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [h]

/--
In dimension two the same rotation atom preserves the standard symplectic
form.  This is the finite `SO(2) = Sp(2,ℝ) ∩ O(2)` shadow used here as a
compact-symmetry property.
-/
theorem rotation2_symplectic {a b : ℝ} (h : a * a + b * b = 1) :
    (rotation2 a b)ᵀ * symplecticJ * rotation2 a b = symplecticJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation2, symplecticJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [h]

end InfoGeometry.Canonical.KatzSarnakFiniteSymmetryBridge
