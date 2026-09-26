import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

import InfoGeometry.Algebra.PeirceDeWittChiralSplit

namespace InfoGeometry.Algebra.ModularDeWittFlow

open InfoGeometry.Algebra.PeirceDeWittChiralSplit

/-!
# Abstract Peirce-scaling specification (not a constructed modular flow)
This section records hypotheses for a map acting on Peirce corners. It does
not construct a flow, assert a group law, or derive the action from a state.
The explicit finite-dimensional inner action is constructed and proved below.
-/

section ModularFlow

variable {A : Type*} [Ring A] [Algebra ℝ A] [S : PeirceIdempotentSystem A]

/-- Conditional corner-action data. Its fields are hypotheses, not consequences
of Peirce idempotency or a state-derived Tomita--Takesaki construction. -/
structure PeirceScalingSpecification (a : ℝ) where
  σ : A → A
  -- It is an exact linear map over ℝ
  map_add : ∀ X Y, σ (X + Y) = σ X + σ Y
  map_smul : ∀ (c : ℝ) X, σ (c • X) = c • σ X

  -- The Chiral Idempotents are strictly stationary (Macroscopic Background Independence)
  h_σ_P1 : σ S.P1 = S.P1
  h_σ_P2 : σ S.P2 = S.P2

  -- Action on the Peirce Components:
  -- The Body (diagonal) is stationary
  h_σ_11 : ∀ X, σ (S.P1 * X * S.P1) = S.P1 * X * S.P1
  h_σ_22 : ∀ X, σ (S.P2 * X * S.P2) = S.P2 * X * S.P2

  -- The Soul (off-diagonal) undergoes Loxodromic Scaling (Time Evolution)
  h_σ_12 : ∀ X, σ (S.P1 * X * S.P2) = (algebraMap ℝ A a) * (S.P1 * X * S.P2)
  h_σ_21 : ∀ X, σ (S.P2 * X * S.P1) = (algebraMap ℝ A a⁻¹) * (S.P2 * X * S.P1)

variable (a : ℝ) (ha : a ≠ 0) (mod_flow : PeirceScalingSpecification a)

/-!
# Archetype 708: Stationarity of the Classical Body
-/

/-- Under the stated corner-fixing hypotheses, the diagonal part is fixed. -/
theorem body_is_stationary (X : A) :
    mod_flow.σ (diagonal X) = diagonal X := by
  dsimp [diagonal]
  rw [mod_flow.map_add]
  rw [mod_flow.h_σ_11, mod_flow.h_σ_22]


/-!
# Archetype 709: Loxodromic Zitterbewegung of the Soul
-/

/-- Under the stated corner-scaling hypotheses, the two off-diagonal terms
transform with reciprocal scalar weights. -/
theorem soul_evolves (X : A) :
    mod_flow.σ (off_diagonal X) =
      (algebraMap ℝ A a) * (S.P1 * X * S.P2) +
      (algebraMap ℝ A a⁻¹) * (S.P2 * X * S.P1) := by
  dsimp [off_diagonal]
  rw [mod_flow.map_add]
  rw [mod_flow.h_σ_12, mod_flow.h_σ_21]

/-!
# Archetype 710: Covariance of the Dirac Mass Shell
-/

/-- The paired corner product is invariant under the stated reciprocal scaling
hypotheses. This is an algebraic corner identity, not a Dirac mass-shell result. -/
theorem evolved_soul_squared_invariant (X : A) :
    mod_flow.σ (S.P1 * X * S.P2) * mod_flow.σ (S.P2 * X * S.P1) =
      (S.P1 * X * S.P2) * (S.P2 * X * S.P1) := by
  -- Evaluate the flowed components
  have h_12 : mod_flow.σ (S.P1 * X * S.P2) = (algebraMap ℝ A a) * (S.P1 * X * S.P2) := mod_flow.h_σ_12 X
  have h_21 : mod_flow.σ (S.P2 * X * S.P1) = (algebraMap ℝ A a⁻¹) * (S.P2 * X * S.P1) := mod_flow.h_σ_21 X

  calc mod_flow.σ (S.P1 * X * S.P2) * mod_flow.σ (S.P2 * X * S.P1)
    _ = ((algebraMap ℝ A a) * (S.P1 * X * S.P2)) * ((algebraMap ℝ A a⁻¹) * (S.P2 * X * S.P1)) := by rw [h_12, h_21]
    _ = (algebraMap ℝ A a) * ((S.P1 * X * S.P2) * (algebraMap ℝ A a⁻¹)) * (S.P2 * X * S.P1) := by
        repeat rw [mul_assoc]
    _ = (algebraMap ℝ A a) * ((algebraMap ℝ A a⁻¹) * (S.P1 * X * S.P2)) * (S.P2 * X * S.P1) := by
        have h_comm : ∀ x : A, x * (algebraMap ℝ A a⁻¹) = (algebraMap ℝ A a⁻¹) * x :=
          fun x => (Algebra.commutes _ x).symm
        rw [h_comm (S.P1 * X * S.P2)]
    _ = ((algebraMap ℝ A a) * (algebraMap ℝ A a⁻¹)) * ((S.P1 * X * S.P2) * (S.P2 * X * S.P1)) := by
        simp only [mul_assoc]
    _ = (algebraMap ℝ A (a * a⁻¹)) * ((S.P1 * X * S.P2) * (S.P2 * X * S.P1)) := by rw [← map_mul]
    _ = (algebraMap ℝ A 1) * ((S.P1 * X * S.P2) * (S.P2 * X * S.P1)) := by
        have h_cancel : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
        rw [h_cancel]
    _ = 1 * ((S.P1 * X * S.P2) * (S.P2 * X * S.P1)) := by rw [map_one]
    _ = (S.P1 * X * S.P2) * (S.P2 * X * S.P1) := one_mul _

end ModularFlow

end InfoGeometry.Algebra.ModularDeWittFlow

/-!
## A concrete finite-dimensional real flow

The generic commutator results above are parity statements, not a
Tomita--Takesaki theorem.  This finite model makes the additional dynamics
explicit: conjugation by `diag(a,1)` fixes diagonal entries and rescales the
two off-diagonal matrix units by reciprocal factors.  The parameter `a` is
required to be nonzero.  No state, KMS condition, or origin of time is inferred.
-/

namespace InfoGeometry.Algebra.ModularDeWittFlow.FiniteMatrix

open Matrix

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The diagonal gauge with eigenvalues `a` and `1`. -/
def gauge (a : ℝ) : M2 := !![a, 0; 0, 1]

/-- The explicit inverse diagonal gauge. -/
def gaugeInv (a : ℝ) : M2 := !![a⁻¹, 0; 0, 1]

/-- Inner conjugation by the diagonal gauge. -/
def flow (a : ℝ) (X : M2) : M2 := gauge a * X * gaugeInv a

private theorem gauge_mul_gaugeInv (a : ℝ) (ha : a ≠ 0) :
    gauge a * gaugeInv a = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gauge, gaugeInv, Matrix.mul_apply, Fin.sum_univ_two, ha]

private theorem gaugeInv_mul_gauge (a : ℝ) (ha : a ≠ 0) :
    gaugeInv a * gauge a = (1 : M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gauge, gaugeInv, Matrix.mul_apply, Fin.sum_univ_two, ha]

/-- Entrywise formula for the finite inner flow. -/
theorem flow_entries (a : ℝ) (ha : a ≠ 0) (X : M2) :
    flow a X = !![X 0 0, a * X 0 1; a⁻¹ * X 1 0, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flow, gauge, gaugeInv, Matrix.mul_apply, Fin.sum_univ_two, ha] <;> ring

/-- The diagonal (even) matrix part is fixed by the gauge flow. -/
theorem flow_diagonal_part (a : ℝ) (ha : a ≠ 0) (x y : ℝ) :
    flow a (!![x, 0; 0, y] : M2) = !![x, 0; 0, y] := by
  rw [flow_entries a ha]
  simp

/-- The `0 → 1` matrix unit has weight `a`. -/
theorem flow_upper_matrix_unit (a : ℝ) (ha : a ≠ 0) :
    flow a (!![0, 1; 0, 0] : M2) = !![0, a; 0, 0] := by
  rw [flow_entries a ha]
  simp

/-- The `1 → 0` matrix unit has the reciprocal weight. -/
theorem flow_lower_matrix_unit (a : ℝ) (ha : a ≠ 0) :
    flow a (!![0, 0; 1, 0] : M2) = !![0, 0; a⁻¹, 0] := by
  rw [flow_entries a ha]
  simp

/-- Conjugation by the gauge respects multiplication. -/
theorem flow_mul (a : ℝ) (ha : a ≠ 0) (X Y : M2) :
    flow a (X * Y) = flow a X * flow a Y := by
  dsimp [flow]
  noncomm_ring [gaugeInv_mul_gauge a ha]

/-- Successive gauge flows compose by multiplying their parameters. -/
theorem flow_comp (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (X : M2) :
    flow a (flow b X) = flow (a * b) X := by
  rw [flow_entries a ha, flow_entries b hb, flow_entries (a * b) (mul_ne_zero ha hb)]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring

end InfoGeometry.Algebra.ModularDeWittFlow.FiniteMatrix
