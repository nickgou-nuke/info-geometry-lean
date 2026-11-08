import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# KL Symmetric/Antisymmetric Decomposition

Theorem-safe algebraic decomposition of an asymmetric divergence into its
symmetric (Jeffreys/traffic) and antisymmetric (current/affinity) parts.

No analytic KL integrability, Fisher-Hessian theorem, Araki entropy theorem, or
de Rham cohomology identification is asserted here.  Those are represented by
explicit comparison packets.  The closed content is the algebraic even/odd
splitting under state swap.
-/

namespace InfoGeometry.Canonical.KLDivergenceDecomposition

open InfoGeometry.Topology.ThermodynamicGauge

universe u

variable {State : Type u}

/-- Symmetric/Jeffreys half of any asymmetric real divergence. -/
noncomputable def symmetricPart (D : State → State → ℝ) (p q : State) : ℝ :=
  (D p q + D q p) / 2

/-- Antisymmetric/current half of any asymmetric real divergence. -/
noncomputable def antisymmetricPart (D : State → State → ℝ) (p q : State) : ℝ :=
  (D p q - D q p) / 2

/-- The divergence is the sum of its symmetric and antisymmetric halves. -/
theorem divergence_eq_symmetric_add_antisymmetric
    (D : State → State → ℝ) (p q : State) :
    D p q = symmetricPart D p q + antisymmetricPart D p q := by
  unfold symmetricPart antisymmetricPart
  ring

/-- The symmetric half is invariant under swapping arguments. -/
theorem symmetricPart_swap (D : State → State → ℝ) (p q : State) :
    symmetricPart D q p = symmetricPart D p q := by
  unfold symmetricPart
  ring

/-- The antisymmetric half changes sign under swapping arguments. -/
theorem antisymmetricPart_swap (D : State → State → ℝ) (p q : State) :
    antisymmetricPart D q p = - antisymmetricPart D p q := by
  unfold antisymmetricPart
  ring

/-- The reverse divergence uses the same symmetric part and the opposite current. -/
theorem reverse_divergence_eq_symmetric_sub_antisymmetric
    (D : State → State → ℝ) (p q : State) :
    D q p = symmetricPart D p q - antisymmetricPart D p q := by
  unfold symmetricPart antisymmetricPart
  ring

/-- The antisymmetric half vanishes exactly when the divergence is swap-symmetric. -/
theorem antisymmetricPart_eq_zero_iff_symmetric
    (D : State → State → ℝ) (p q : State) :
    antisymmetricPart D p q = 0 ↔ D p q = D q p := by
  unfold antisymmetricPart
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h]
    ring

/-- Difference of forward and reverse divergence is twice the antisymmetric part. -/
theorem divergence_sub_reverse_eq_two_mul_antisymmetric
    (D : State → State → ℝ) (p q : State) :
    D p q - D q p = 2 * antisymmetricPart D p q := by
  unfold antisymmetricPart
  ring

/-- Sum of forward and reverse divergence is twice the symmetric part. -/
theorem divergence_add_reverse_eq_two_mul_symmetric
    (D : State → State → ℝ) (p q : State) :
    D p q + D q p = 2 * symmetricPart D p q := by
  unfold symmetricPart
  ring

/-- Nonnegativity of the symmetric half follows from nonnegativity of both directions. -/
theorem symmetricPart_nonneg_of_pair_nonneg
    (D : State → State → ℝ) (p q : State)
    (hpq : 0 ≤ D p q) (hqp : 0 ≤ D q p) :
    0 ≤ symmetricPart D p q := by
  unfold symmetricPart
  nlinarith

end InfoGeometry.Canonical.KLDivergenceDecomposition
