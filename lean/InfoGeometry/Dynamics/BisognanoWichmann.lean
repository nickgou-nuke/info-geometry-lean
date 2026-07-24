import InfoGeometry.Dynamics.TomitaTakesaki
import InfoGeometry.Dynamics.KanDecomposition
import Mathlib.Tactic

noncomputable section

/-!
# BisognanoWichmann

Finite `2 × 2` bridge between the matrix Tomita data and the geometric boost
lane.

This is a controlled finite-dimensional model of the Bisognano--Wichmann
dictionary: the complexified modular flow is identified with the complex `A`
component at imaginary rapidity, and the Rindler/Unruh scale is recorded by the
factor `2π`.

The file does not claim the analytic Bisognano--Wichmann theorem for local
algebras in QFT.  It proves the exact matrix identities used by this
repository's finite Rindler model.
-/

namespace InfoGeometry.Dynamics.BisognanoWichmann

open Matrix
open InfoGeometry.Dynamics.KmsBoundary
open InfoGeometry.Dynamics.TomitaTakesaki
open InfoGeometry.Dynamics.KanDecomposition

/-- Two-component complex state vectors for the finite modular model. -/
abbrev Vec2C := Fin 2 → ℂ

/--
Anti-linear modular conjugation on vectors: apply the Pauli-X matrix part and
then entrywise complex conjugation.
-/
def modularConjugationAnti (ψ : Vec2C) : Vec2C :=
  fun
    | 0 => star (ψ 1)
    | 1 => star (ψ 0)

/-- Top coordinate of the finite anti-linear modular conjugation. -/
@[simp] theorem modularConjugationAnti_zero (ψ : Vec2C) :
    modularConjugationAnti ψ 0 = star (ψ 1) := by
  rfl

/-- Bottom coordinate of the finite anti-linear modular conjugation. -/
@[simp] theorem modularConjugationAnti_one (ψ : Vec2C) :
    modularConjugationAnti ψ 1 = star (ψ 0) := by
  rfl

/--
The coordinate definition is the Pauli-X matrix action followed by coordinate
conjugation.
-/
theorem modularConjugationAnti_eq_star_mulVec (ψ : Vec2C) :
    modularConjugationAnti ψ = fun i => star ((modularConjugation *ᵥ ψ) i) := by
  ext i
  fin_cases i
  · simp [modularConjugationAnti, modularConjugation, Matrix.mulVec]
    change star (ψ 1) = star (ψ 1)
    rfl
  · simp [modularConjugationAnti, modularConjugation, Matrix.mulVec]
    change star (ψ 0) = star (ψ 0)
    rfl

/-- The anti-linear modular conjugation is involutive on vectors. -/
@[simp] theorem modularConjugationAnti_involutive (ψ : Vec2C) :
    modularConjugationAnti (modularConjugationAnti ψ) = ψ := by
  ext i
  fin_cases i <;> simp

/-- Additivity part of anti-linearity for the finite modular conjugation. -/
theorem modularConjugationAnti_add (ψ φ : Vec2C) :
    modularConjugationAnti (ψ + φ) =
      modularConjugationAnti ψ + modularConjugationAnti φ := by
  ext i
  fin_cases i <;> simp

/-- Scalar conjugation part of anti-linearity for the finite modular conjugation. -/
theorem modularConjugationAnti_smul (c : ℂ) (ψ : Vec2C) :
    modularConjugationAnti (c • ψ) = star c • modularConjugationAnti ψ := by
  ext i
  fin_cases i <;> simp

/--
Matrix-level anti-conjugation induced by the vector anti-linear `J`.

This is the explicit coordinate form of conjugating entries and swapping the
two eigenspaces by the Pauli-X matrix part.
-/
def modularAntiConjugateMatrix (A : Mat2C) : Mat2C :=
  !![star (A 1 1), star (A 1 0);
     star (A 0 1), star (A 0 0)]

/--
The anti-linear matrix conjugation reflects a diagonal boost generator and
conjugates its scalar parameter.
-/
theorem modularAntiConjugateMatrix_diagonal (lam : ℂ) :
    modularAntiConjugateMatrix !![lam, 0; 0, -lam] =
      !![-star lam, 0; 0, star lam] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modularAntiConjugateMatrix]

/--
Tomita's complexified finite flow is the complex `A` component at imaginary
rapidity.
-/
theorem tomita_flow_eq_componentA (t : ℝ) :
    finiteTomitaFlow t = componentA (Complex.I * (t : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteTomitaFlow, imaginaryTimeEvolution, componentA]

/-- The finite Bisognano--Wichmann imaginary rapidity parameter `2π i t`. -/
def bwRapidity (t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) * Complex.I * (t : ℂ)

/--
Finite Bisognano--Wichmann bridge.

The modular flow with inverse-temperature-scaled imaginary time agrees with the
geometric `A`-component boost at rapidity `2π i t`.
-/
theorem bisognano_wichmann_flow (t : ℝ) :
    imaginaryTimeEvolution (-(bwRapidity t)) = componentA (bwRapidity t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bwRapidity, imaginaryTimeEvolution, componentA]

/-- At one full imaginary Rindler period, the finite BW flow is the identity. -/
theorem bisognano_wichmann_period_one :
    componentA (bwRapidity 1) = (1 : Mat2C) := by
  have hpos : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    simp [Complex.exp_two_pi_mul_I]
  have hneg : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_neg, hpos, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bwRapidity, componentA, hpos, hneg]

end InfoGeometry.Dynamics.BisognanoWichmann
