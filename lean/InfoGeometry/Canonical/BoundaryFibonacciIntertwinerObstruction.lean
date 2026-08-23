import InfoGeometry.Canonical.BoundaryBraidRepresentation
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Physics.B3PresentedGroup
import Mathlib.Tactic

/-!
# Direct boundary/Fibonacci intertwiner obstruction

The native eight-dimensional boundary braid representation and the native
Fibonacci two-dimensional representation are not identified here.

This owner records the first unavoidable compatibility condition for any
candidate direct intertwiner.  If a matrix `Φ : ℂ⁸ → ℂ²` intertwines the first
Artin generator,

`Φ s₀ = R Φ`,

then, because the boundary generator satisfies `s₀² = -I`, one must have

`(R² + I) Φ = 0`.

Thus a direct intertwiner can exist only on the `(-1)` eigenspace of `R²`.
A later owner may close the question by proving that `R² + I` is nonsingular
for the concrete Fibonacci phase convention, or by constructing a genuine
invariant subquotient if the direct Hom-space vanishes.

No projection, fiber equivalence, or nonzero intertwiner is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction

open Matrix
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Physics.JonesBraidB3
open InfoGeometry.Canonical.YangBaxterProof

abbrev BoundaryState := Fin 8 → ℂ
abbrev FibonacciState := Fin 2 → ℂ
abbrev BoundaryToFibonacci := Matrix (Fin 2) (Fin 8) ℂ

/-- Matrix form of intertwining the first Artin generator. -/
def IntertwinesFirstGenerator (Φ : BoundaryToFibonacci) : Prop :=
  Φ * JonesBraidB3.s0 = R * Φ

/-- Any direct first-generator intertwiner is annihilated by `R² + I`.
This is the spectral obstruction forced by `s₀² = -I`. -/
theorem fibonacci_square_obstruction
    (Φ : BoundaryToFibonacci)
    (hΦ : IntertwinesFirstGenerator Φ) :
    (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ = 0 := by
  have hstep :
      Φ * (JonesBraidB3.s0 * JonesBraidB3.s0) =
        (R * R) * Φ := by
    calc
      Φ * (JonesBraidB3.s0 * JonesBraidB3.s0)
          = (Φ * JonesBraidB3.s0) * JonesBraidB3.s0 := by
              rw [Matrix.mul_assoc]
      _ = (R * Φ) * JonesBraidB3.s0 := by rw [hΦ]
      _ = R * (Φ * JonesBraidB3.s0) := by rw [Matrix.mul_assoc]
      _ = R * (R * Φ) := by rw [hΦ]
      _ = (R * R) * Φ := by rw [Matrix.mul_assoc]
  have hneg : -(Φ : BoundaryToFibonacci) = (R * R) * Φ := by
    calc
      -Φ = Φ * (-(1 : Matrix (Fin 8) (Fin 8) ℂ)) := by simp
      _ = Φ * (JonesBraidB3.s0 * JonesBraidB3.s0) := by
            rw [s0_sq_eq_neg_one]
      _ = (R * R) * Φ := hstep
  calc
    (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ
        = (R * R) * Φ + Φ := by
            rw [Matrix.add_mul, Matrix.one_mul]
    _ = -Φ + Φ := by rw [← hneg]
    _ = 0 := by simp

/-- Consequently, if `R² + I` has a left inverse, every direct candidate
intertwiner for the first generator is zero. -/
theorem direct_intertwiner_eq_zero_of_left_inverse
    (Φ : BoundaryToFibonacci)
    (hΦ : IntertwinesFirstGenerator Φ)
    (L : Matrix (Fin 2) (Fin 2) ℂ)
    (hL : L * (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1) :
    Φ = 0 := by
  have hobs := fibonacci_square_obstruction Φ hΦ
  calc
    Φ = (1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ := by simp
    _ = (L * (R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ))) * Φ := by rw [hL]
    _ = L * ((R * R + (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Φ) := by
          rw [Matrix.mul_assoc]
    _ = L * 0 := by rw [hobs]
    _ = 0 := by simp

end InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
