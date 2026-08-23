import InfoGeometry.Canonical.BoundaryBraidRepresentation
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Physics.B3PresentedGroup
import Mathlib.Tactic

/-!
# Direct boundary/Fibonacci intertwiner obstruction

The native eight-dimensional boundary braid representation and the native
Fibonacci two-dimensional representation are not identified here.

This owner records the first compatibility condition for a candidate direct
intertwiner.  If a matrix `Φ : ℂ⁸ → ℂ²` intertwines the first Artin generator,
`Φ s₀ = R Φ`, then the relation `s₀² = -I` forces
`(R² + I) Φ = 0`.

No projection, fibre equivalence, or nonzero intertwiner is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction

#check InfoGeometry.Canonical.YangBaxterProof.det_R_sq_add_one_ne_zero

open Matrix
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Canonical.YangBaxterProof

local notation "s₀" => _root_.InfoGeometry.Physics.JonesBraidB3.s0
local notation "R_Fib" => _root_.InfoGeometry.Canonical.YangBaxterProof.R

/-- Matrix form of intertwining the first Artin generator. -/
def IntertwinesFirstGenerator (Φ : Matrix (Fin 2) (Fin 8) ℂ) : Prop :=
  Φ * s₀ = R_Fib * Φ

/-- Any direct first-generator intertwiner is annihilated by `R² + I`.
This is the spectral obstruction forced by `s₀² = -I`. -/
theorem fibonacci_square_obstruction
    (Φ : Matrix (Fin 2) (Fin 8) ℂ)
    (hΦ : IntertwinesFirstGenerator Φ) :
    (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ = 0 := by
  have hstep :
      Φ * (s₀ * s₀) =
        (R_Fib * R_Fib) * Φ := by
    calc
      Φ * (s₀ * s₀)
          = (Φ * s₀) * s₀ := by
              rw [Matrix.mul_assoc]
      _ = (R_Fib * Φ) * s₀ := by rw [hΦ]
      _ = R_Fib * (Φ * s₀) := by rw [Matrix.mul_assoc]
      _ = R_Fib * (R_Fib * Φ) := by rw [hΦ]
      _ = (R_Fib * R_Fib) * Φ := by rw [Matrix.mul_assoc]
  have hneg : -(Φ : Matrix (Fin 2) (Fin 8) ℂ) = (R_Fib * R_Fib) * Φ := by
    calc
      -Φ = Φ * (-(1 : Matrix (Fin 8) (Fin 8) ℂ)) := by simp
      _ = Φ * (s₀ * s₀) := by
            rw [s0_sq_eq_neg_one]
      _ = (R_Fib * R_Fib) * Φ := hstep
  calc
    (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ
        = (R_Fib * R_Fib) * Φ + Φ := by
            rw [Matrix.add_mul, Matrix.one_mul]
    _ = -Φ + Φ := by rw [← hneg]
    _ = 0 := by simp

/-- A left inverse for `R² + I` forces every direct candidate intertwiner to
vanish. -/
theorem direct_intertwiner_eq_zero_of_left_inverse
    (Φ : Matrix (Fin 2) (Fin 8) ℂ)
    (hΦ : IntertwinesFirstGenerator Φ)
    (L : Matrix (Fin 2) (Fin 2) ℂ)
    (hL : L * (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1) :
    Φ = 0 := by
  have hobs := fibonacci_square_obstruction Φ hΦ
  calc
    Φ = (1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ := by simp
    _ = (L * (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ))) * Φ := by rw [hL]
    _ = L * ((R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ) := by
          rw [Matrix.mul_assoc]
    _ = L * (0 : Matrix (Fin 2) (Fin 8) ℂ) := by rw [hobs]
    _ = (0 : Matrix (Fin 2) (Fin 8) ℂ) := by simp

/-- The concrete Fibonacci phase has a nonsingular spectral obstruction. -/
theorem obstruction_det_ne_zero :
    Matrix.det (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ)) ≠ 0 := by
  exact det_R_sq_add_one_ne_zero

/-- No nonzero direct intertwiner exists for the concrete first-generator
representations. -/
theorem direct_intertwiner_eq_zero
    (Φ : Matrix (Fin 2) (Fin 8) ℂ)
    (hΦ : IntertwinesFirstGenerator Φ) :
    Φ = 0 := by
  apply direct_intertwiner_eq_zero_of_left_inverse Φ hΦ
    (R_Fib * R_Fib + (1 : Matrix (Fin 2) (Fin 2) ℂ))⁻¹
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr obstruction_det_ne_zero)

end InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
