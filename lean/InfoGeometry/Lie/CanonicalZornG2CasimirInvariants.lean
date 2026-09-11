import InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Rank-two `G₂` Weyl invariants

This owner records the quadratic invariant for the already established
parameter reflection representation.  The carrier is the explicit rank-two
real parameter space; no identification with a root-star coordinate carrier
is assumed here.
-/

namespace InfoGeometry.Lie.CanonicalZornG2CasimirInvariants

open InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariant

def quadraticCasimir (x : Fin 2 → ℝ) : ℝ :=
  3 * (x 0) ^ 2 + 3 * x 0 * x 1 + (x 1) ^ 2

theorem quadraticCasimir_short_invariant (x : Fin 2 → ℝ) :
    quadraticCasimir (canonicalShortReflectionChargeReal x) =
      quadraticCasimir x := by
  unfold quadraticCasimir canonicalShortReflectionChargeReal
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem quadraticCasimir_long_invariant (x : Fin 2 → ℝ) :
    quadraticCasimir (canonicalLongReflectionChargeReal x) =
      quadraticCasimir x := by
  unfold quadraticCasimir canonicalLongReflectionChargeReal
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def dualQuadraticCasimir (x : Fin 2 → ℝ) : ℝ :=
  (x 0) ^ 2 - 3 * (x 0) * x 1 + 3 * (x 1) ^ 2

theorem dualQuadraticCasimir_short_invariant (x : Fin 2 → ℝ) :
    dualQuadraticCasimir (canonicalShortReflectionDualReal x) =
      dualQuadraticCasimir x := by
  unfold dualQuadraticCasimir canonicalShortReflectionDualReal
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem dualQuadraticCasimir_long_invariant (x : Fin 2 → ℝ) :
    dualQuadraticCasimir (canonicalLongReflectionDualReal x) =
      dualQuadraticCasimir x := by
  unfold dualQuadraticCasimir canonicalLongReflectionDualReal
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def dualSexticCasimir (x : Fin 2 → ℝ) : ℝ :=
  (x 0 - 3 * x 1) ^ 2 * (x 0) ^ 2 * (2 * x 0 - 3 * x 1) ^ 2

theorem dualSexticCasimir_short_invariant (x : Fin 2 → ℝ) :
    dualSexticCasimir (canonicalShortReflectionDualReal x) =
      dualSexticCasimir x := by
  unfold dualSexticCasimir canonicalShortReflectionDualReal
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem dualSexticCasimir_long_invariant (x : Fin 2 → ℝ) :
    dualSexticCasimir (canonicalLongReflectionDualReal x) =
      dualSexticCasimir x := by
  unfold dualSexticCasimir canonicalLongReflectionDualReal
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem dualQuadraticCasimir_nonneg (x : Fin 2 → ℝ) :
    0 ≤ dualQuadraticCasimir x := by
  unfold dualQuadraticCasimir
  have h₁ : 0 ≤ (x 0 - (3 / 2 : ℝ) * x 1) ^ 2 := sq_nonneg _
  have h₂ : 0 ≤ (x 1) ^ 2 := sq_nonneg _
  nlinarith

theorem dualSexticCasimir_nonneg (x : Fin 2 → ℝ) :
    0 ≤ dualSexticCasimir x := by
  unfold dualSexticCasimir
  positivity

def sexticCasimir (x : Fin 2 → ℝ) : ℝ :=
  (x 0) ^ 2 * (x 0 + x 1) ^ 2 * (2 * x 0 + x 1) ^ 2

theorem sexticCasimir_short_invariant (x : Fin 2 → ℝ) :
    sexticCasimir (canonicalShortReflectionChargeReal x) =
      sexticCasimir x := by
  unfold sexticCasimir canonicalShortReflectionChargeReal
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem sexticCasimir_long_invariant (x : Fin 2 → ℝ) :
    sexticCasimir (canonicalLongReflectionChargeReal x) =
      sexticCasimir x := by
  unfold sexticCasimir canonicalLongReflectionChargeReal
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem quadraticCasimir_nonneg (x : Fin 2 → ℝ) :
    0 ≤ quadraticCasimir x := by
  unfold quadraticCasimir
  have h₁ : 0 ≤ (x 0 + (x 1) / 2) ^ 2 := sq_nonneg _
  have h₂ : 0 ≤ (x 1) ^ 2 := sq_nonneg _
  nlinarith

theorem sexticCasimir_nonneg (x : Fin 2 → ℝ) :
    0 ≤ sexticCasimir x := by
  unfold sexticCasimir
  positivity

end InfoGeometry.Lie.CanonicalZornG2CasimirInvariants
