import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Souriau Beta Vectors, Hestenes Bivectors, and Krein Determinant Sectors

Finite algebraic model for replacing the scalar complex unit by an operator
generator.

* elliptic unit: `J² = -I`, the ordinary complex/bivector rotor;
* hyperbolic unit: `K² = I`, the split/Krein rotor;
* parabolic unit: `N² = 0`, the nilpotent boundary generator;
* determinant sign classifies the finite paravector model;
* a tripotent operator `OP` satisfies `OP³ = OP`, with determinant in
  `{1,0,-1}` for the three sector labels.

The zeta connection is kept theorem-honest: poles of the graded arithmetic
supertrace are represented by the predicate that the reciprocal determinant
denominator vanishes.
-/

noncomputable section

namespace SouriauHestenesKrein

open Matrix

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

def ellipticUnit : M2R :=
  !![0, -1; 1, 0]

def hyperbolicUnit : M2R :=
  !![0, 1; 1, 0]

def parabolicUnit : M2R :=
  !![0, 1; 0, 0]

def ellipticTemperatureOperator (β τ : ℝ) : M2R :=
  !![β, -τ; τ, β]

def hyperbolicTemperatureOperator (β τ : ℝ) : M2R :=
  !![β, τ; τ, β]

def parabolicTemperatureOperator (β τ : ℝ) : M2R :=
  !![β, τ; 0, β]

def sectorTripotentOperator (q : ℝ) : M2R :=
  !![q, 0; 0, 1]

inductive DeterminantSector where
  | elliptic
  | hyperbolic
  | parabolic
deriving DecidableEq, Repr

def determinantSector (d : ℝ) : DeterminantSector :=
  if 0 < d then DeterminantSector.elliptic
  else if d < 0 then DeterminantSector.hyperbolic
  else DeterminantSector.parabolic

theorem ellipticUnit_sq :
    ellipticUnit * ellipticUnit = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticUnit, Matrix.mul_apply, Fin.sum_univ_two]

theorem hyperbolicUnit_sq :
    hyperbolicUnit * hyperbolicUnit = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hyperbolicUnit, Matrix.mul_apply, Fin.sum_univ_two]

theorem parabolicUnit_sq :
    parabolicUnit * parabolicUnit = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parabolicUnit, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_ellipticTemperatureOperator (β τ : ℝ) :
    (ellipticTemperatureOperator β τ).det = β ^ 2 + τ ^ 2 := by
  simp [ellipticTemperatureOperator, Matrix.det_fin_two]
  ring

theorem det_hyperbolicTemperatureOperator (β τ : ℝ) :
    (hyperbolicTemperatureOperator β τ).det = β ^ 2 - τ ^ 2 := by
  simp [hyperbolicTemperatureOperator, Matrix.det_fin_two]
  ring

theorem det_parabolicTemperatureOperator (β τ : ℝ) :
    (parabolicTemperatureOperator β τ).det = β ^ 2 := by
  simp [parabolicTemperatureOperator, Matrix.det_fin_two]
  ring

theorem sectorTripotentOperator_cube
    {q : ℝ} (hq : q ^ 3 = q) :
    sectorTripotentOperator q * sectorTripotentOperator q *
      sectorTripotentOperator q = sectorTripotentOperator q := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [sectorTripotentOperator, Matrix.mul_apply, Fin.sum_univ_two]
    nlinarith [hq]
  · simp [sectorTripotentOperator, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [sectorTripotentOperator, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [sectorTripotentOperator, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_sectorTripotentOperator (q : ℝ) :
    (sectorTripotentOperator q).det = q := by
  simp [sectorTripotentOperator, Matrix.det_fin_two]

theorem sectorTripotent_positive :
    determinantSector (sectorTripotentOperator 1).det = DeterminantSector.elliptic := by
  simp [determinantSector, det_sectorTripotentOperator]

theorem sectorTripotent_zero :
    determinantSector (sectorTripotentOperator 0).det = DeterminantSector.parabolic := by
  simp [determinantSector, det_sectorTripotentOperator]

theorem sectorTripotent_negative :
    determinantSector (sectorTripotentOperator (-1)).det = DeterminantSector.hyperbolic := by
  simp [determinantSector, det_sectorTripotentOperator]

/-- Graded arithmetic supertrace pole: reciprocal determinant denominator vanishes. -/
def gradedSupertracePole (denominator : ℂ) : Prop :=
  denominator = 0

/-- Poles of the graded reciprocal determinant are exactly denominator zeros. -/
theorem gradedSupertracePole_iff_denominator_zero (z : ℂ) :
    gradedSupertracePole z ↔ z = 0 := by
  rfl

/-- Consolidated Souriau-Hestenes-Krein finite matrix package. -/
theorem souriau_hestenes_krein_synthesis :
    ellipticUnit * ellipticUnit = -1 ∧
    hyperbolicUnit * hyperbolicUnit = 1 ∧
    parabolicUnit * parabolicUnit = 0 ∧
    (∀ β τ, (ellipticTemperatureOperator β τ).det = β ^ 2 + τ ^ 2) ∧
    (∀ β τ, (hyperbolicTemperatureOperator β τ).det = β ^ 2 - τ ^ 2) ∧
    (∀ β τ, (parabolicTemperatureOperator β τ).det = β ^ 2) ∧
    (∀ q, q ^ 3 = q →
      sectorTripotentOperator q * sectorTripotentOperator q *
        sectorTripotentOperator q = sectorTripotentOperator q) ∧
    determinantSector (sectorTripotentOperator 1).det = DeterminantSector.elliptic ∧
    determinantSector (sectorTripotentOperator 0).det = DeterminantSector.parabolic ∧
    determinantSector (sectorTripotentOperator (-1)).det = DeterminantSector.hyperbolic ∧
    (∀ z : ℂ, gradedSupertracePole z ↔ z = 0) := by
  exact ⟨ellipticUnit_sq, hyperbolicUnit_sq, parabolicUnit_sq,
    det_ellipticTemperatureOperator, det_hyperbolicTemperatureOperator,
    det_parabolicTemperatureOperator,
    fun q hq => sectorTripotentOperator_cube hq,
    sectorTripotent_positive, sectorTripotent_zero, sectorTripotent_negative,
    gradedSupertracePole_iff_denominator_zero⟩

end SouriauHestenesKrein

end noncomputable section
