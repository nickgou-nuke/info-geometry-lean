import Mathlib.Tactic
import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Canonical.TomitaTakesakiWickRotation
import InfoGeometry.OperatorAlgebra.RenormalizedTrace

/-!
# Finite spectral squashing, Cayley coordinates, and Dirac--Krein--Tomita shadow

This file proves the finite algebraic kernel behind the regularization pipeline.
It does **not** claim a full unbounded-operator colimit theorem. The analytic
C*-inductive-limit, inverse Cayley boundary, and Tomita--Takesaki antiunitary
closure are recorded as explicit interfaces.
-/

noncomputable section

namespace SpectralSquashCayleyDKT

open CategoryTheory
open CategoryTheory.Limits
open Matrix
open scoped BigOperators

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- A finite diagonal stage with growing real spectral parameter. -/
def stageOperator (lam : ℝ) : M2C := !![(lam : ℂ), 0; 0, (2 * lam : ℂ)]

/-- Relative/vacuum regularization: subtract the identity at the finite stage. -/
def regularized (T : M2C) : M2C := T - 1

/-- The finite regularization of the diagonal stage. -/
theorem regularized_stage (lam : ℝ) :
    regularized (stageOperator lam) = !![((lam - 1 : ℝ) : ℂ), 0; 0, ((2 * lam - 1 : ℝ) : ℂ)] := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [regularized, stageOperator]

/-- Scalar squashing coordinate `tanh(1-1/λ)`. -/
def squashCoord (lam : ℝ) : ℝ := Real.tanh (1 - lam⁻¹)

/-- `tanh` always lands strictly inside `(-1,1)`. -/
theorem squashCoord_bounded (lam : ℝ) : -1 < squashCoord lam ∧ squashCoord lam < 1 := by
  exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

/-- Diagonal Cayley transform of the finite stage. -/
def squashStage (lam : ℝ) : M2C :=
  !![((squashCoord lam : ℝ) : ℂ), 0; 0, ((squashCoord (2 * lam) : ℝ) : ℂ)]

/-- A rational real-coordinate form of the Cayley transform of a real scalar:
`(x-i)/(x+i) = ((x²-1)/(x²+1)) - (2x/(x²+1)) i`. -/
def cayleyCoord (x : ℝ) : ℂ :=
  ⟨(x ^ 2 - 1) / (x ^ 2 + 1), -(2 * x) / (x ^ 2 + 1)⟩

private theorem cayley_denom_ne (x : ℝ) : x ^ 2 + 1 ≠ 0 := by positivity

/-- The scalar Cayley coordinate lies on the unit circle. -/
theorem cayleyCoord_unit (x : ℝ) : cayleyCoord x * star (cayleyCoord x) = 1 := by
  apply Complex.ext <;> simp [cayleyCoord, Complex.mul_re, Complex.mul_im]
  · field_simp [cayley_denom_ne x]
    ring
  · field_simp [cayley_denom_ne x]
    ring

/-- Diagonal Cayley transform of the finite stage. -/
def cayleyStage (lam : ℝ) : M2C := !![cayleyCoord lam, 0; 0, cayleyCoord (2 * lam)]

/-- The finite diagonal Cayley stage is unitary. -/
theorem cayleyStage_unitary (lam : ℝ) : cayleyStage lam * star (cayleyStage lam) = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j
  · simpa [cayleyStage, Matrix.mul_apply, Fin.sum_univ_two] using cayleyCoord_unit lam
  · simp [cayleyStage, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [cayleyStage, Matrix.mul_apply, Fin.sum_univ_two]
  · simpa [cayleyStage, Matrix.mul_apply, Fin.sum_univ_two] using cayleyCoord_unit (2 * lam)

/-- Positive chiral projection. -/
def Nplus : M2C := !![(1 : ℂ), 0; 0, 0]

/-- Negative chiral projection. -/
def Nminus : M2C := !![(0 : ℂ), 0; 0, 1]

/-- Finite Krein metric/fundamental symmetry. In the full analytic theory this
is only the finite `η` part, not the Tomita modular conjugation. -/
def eta : M2C := !![(1 : ℂ), 0; 0, -1]

/-- Endogenous finite signature: `η` is the difference of the two chiral
projection grades. -/
theorem eta_eq_projection_difference : eta = Nplus - Nminus := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [eta, Nplus, Nminus]

/-- The finite signature is an involution. -/
theorem eta_sq : eta * eta = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [eta, Matrix.mul_apply, Fin.sum_univ_two]

/-- The finite signature is self-adjoint. -/
theorem eta_selfadjoint : star eta = eta := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [eta]

/-- Finite linear shadow of the unified Dirac--Krein--Tomita adjoint:
`X ↦ η X† η`. The antiunitary Tomita `J` is intentionally left abstract below. -/
def dktAdjoint (X : M2C) : M2C := eta * star X * eta

/-- The finite DKT/Krein adjoint shadow is involutive. -/
theorem dktAdjoint_involutive (X : M2C) : dktAdjoint (dktAdjoint X) = X := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [dktAdjoint, eta, Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]

/-- The finite DKT/Krein adjoint shadow reverses products. -/
theorem dktAdjoint_mul (X Y : M2C) : dktAdjoint (X * Y) = dktAdjoint Y * dktAdjoint X := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [dktAdjoint, eta, Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The finite diagonal stage is self-adjoint for the DKT/Krein shadow. -/
theorem dktAdjoint_stageOperator (lam : ℝ) : dktAdjoint (stageOperator lam) = stageOperator lam := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    apply Complex.ext <;> norm_num
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [dktAdjoint, eta, stageOperator, Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail, htwo]

/-- On the diagonal Cayley boundary, the finite DKT/Krein shadow collapses to the
ordinary Hilbert adjoint. The full anti-linear Tomita step remains abstract. -/
theorem dktAdjoint_cayleyStage_eq_star (lam : ℝ) :
    dktAdjoint (cayleyStage lam) = star (cayleyStage lam) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [dktAdjoint, eta, cayleyStage, Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]

/-- Consequently the Cayley coordinate is unitary also with respect to the
finite DKT/Krein adjoint shadow. -/
theorem cayleyStage_dkt_unitary (lam : ℝ) :
    cayleyStage lam * dktAdjoint (cayleyStage lam) = 1 := by
  rw [dktAdjoint_cayleyStage_eq_star]
  exact cayleyStage_unitary lam

/-- Synthesis theorem: finite squashing is bounded, finite Cayley coordinates are
unitary, and the finite DKT/Krein adjoint shadow is an anti-involution. -/
theorem spectral_squash_cayley_dkt_synthesis (lam : ℝ) :
    eta = Nplus - Nminus ∧
    eta * eta = 1 ∧
    (-1 < squashCoord lam ∧ squashCoord lam < 1) ∧
    cayleyStage lam * star (cayleyStage lam) = 1 ∧
    dktAdjoint (stageOperator lam) = stageOperator lam ∧
    dktAdjoint (cayleyStage lam) = star (cayleyStage lam) ∧
    cayleyStage lam * dktAdjoint (cayleyStage lam) = 1 ∧
    (∀ X : M2C, dktAdjoint (dktAdjoint X) = X) ∧
    (∀ X Y : M2C, dktAdjoint (X * Y) = dktAdjoint Y * dktAdjoint X) := by
  refine ⟨eta_eq_projection_difference, eta_sq, squashCoord_bounded lam,
    cayleyStage_unitary lam, dktAdjoint_stageOperator lam,
    dktAdjoint_cayleyStage_eq_star lam, cayleyStage_dkt_unitary lam, ?_, ?_⟩
  · exact dktAdjoint_involutive
  · exact dktAdjoint_mul

end SpectralSquashCayleyDKT
