import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite causal matrix algebra

The former file carried an arbitrary integer under a `MonodromyWinding` class
and returned it by a tautological existential.  That was not a cohomology
theorem.  This owner retains the concrete matrix/Klein-quadric mathematics
without inventing a topological or physical interpretation.
-/

namespace InfoGeometry.Motives

variable {R : Type*} [CommRing R]

/-- The two-by-two causal matrix used by the finite projective carrier. -/
def CausalMatrix (t x y z : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![t + z, x - y],
    ![x + y, t - z]]

/-- The determinant readout of the causal matrix. -/
def CausalDeterminant (t x y z : R) : R :=
  (CausalMatrix t x y z).det

/-- The determinant-zero causal cone. -/
def KleinQuadric (t x y z : R) : Prop :=
  CausalDeterminant t x y z = 0

theorem causalDeterminant_eq_quadratic (t x y z : R) :
    CausalDeterminant t x y z = t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2 := by
  simp [CausalDeterminant, CausalMatrix, Matrix.det_fin_two]
  ring

theorem kleinQuadric_iff_quadratic (t x y z : R) :
    KleinQuadric t x y z ↔ t ^ 2 - x ^ 2 + y ^ 2 - z ^ 2 = 0 := by
  rw [KleinQuadric, causalDeterminant_eq_quadratic]

/-! ## A finite logarithmic barrier readout -/

/-- The log-determinant barrier on the positive determinant region. -/
noncomputable def LogBarrierPotential
    (X : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  -Real.log X.det

theorem exp_neg_logBarrierPotential
    (X : Matrix (Fin 2) (Fin 2) ℝ) (hdet : 0 < X.det) :
    Real.exp (LogBarrierPotential X) = (X.det)⁻¹ := by
  unfold LogBarrierPotential
  rw [Real.exp_neg, Real.exp_log hdet]

end InfoGeometry.Motives
