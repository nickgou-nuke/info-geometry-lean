import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge

Spinor carrier and creation / annihilation CAR operator algebra on `ExteriorAlgebra R (Dual R U)`.

This module formalizes the spinor carrier `Spinor R U := ExteriorAlgebra R (Module.Dual R U)`,
the creation operator `ε_α`, and its nilpotency and anticommutation laws in `Module.End R (Spinor R U)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge

open ExteriorAlgebra

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

/-- **Definition**: Spinor space `S = ⋀ U*`. -/
abbrev Spinor (R U : Type*) [CommRing R] [AddCommGroup U] [Module R U] :=
  ExteriorAlgebra R (Module.Dual R U)

/-- **Definition**: Creation operator `ε_α : S →ₗ[R] S` as left exterior multiplication by `ι(α)`. -/
def creation (alpha : Module.Dual R U) : Module.End R (Spinor R U) :=
  LinearMap.mulLeft R (ExteriorAlgebra.ι R alpha)

/-- **Theorem**: Creation operator nilpotency `ε_α² = 0`. -/
theorem creation_sq_zero (alpha : Module.Dual R U) :
    creation alpha * creation alpha = 0 := by
  ext ψ
  dsimp [creation]
  have h1 : ExteriorAlgebra.ι R alpha * (ExteriorAlgebra.ι R alpha * ψ) =
            (ExteriorAlgebra.ι R alpha * ExteriorAlgebra.ι R alpha) * ψ := by noncomm_ring
  rw [h1, ExteriorAlgebra.ι_sq_zero, zero_mul]

/-- **Theorem**: Creation operator anticommutation `ε_α ε_β + ε_β ε_α = 0`. -/
theorem creation_anticomm (alpha beta : Module.Dual R U) :
    creation alpha * creation beta + creation beta * creation alpha = 0 := by
  have h_sum : ExteriorAlgebra.ι R (alpha + beta) * ExteriorAlgebra.ι R (alpha + beta) = 0 :=
    ExteriorAlgebra.ι_sq_zero (alpha + beta)
  have h_a : ExteriorAlgebra.ι R alpha * ExteriorAlgebra.ι R alpha = 0 :=
    ExteriorAlgebra.ι_sq_zero alpha
  have h_b : ExteriorAlgebra.ι R beta * ExteriorAlgebra.ι R beta = 0 :=
    ExteriorAlgebra.ι_sq_zero beta
  have h_linear : ExteriorAlgebra.ι R (alpha + beta) = ExteriorAlgebra.ι R alpha + ExteriorAlgebra.ι R beta := by
    simp
  have h_anti : ExteriorAlgebra.ι R alpha * ExteriorAlgebra.ι R beta +
                ExteriorAlgebra.ι R beta * ExteriorAlgebra.ι R alpha = 0 := by
    calc ExteriorAlgebra.ι R alpha * ExteriorAlgebra.ι R beta + ExteriorAlgebra.ι R beta * ExteriorAlgebra.ι R alpha
        = (ExteriorAlgebra.ι R alpha + ExteriorAlgebra.ι R beta) * (ExteriorAlgebra.ι R alpha + ExteriorAlgebra.ι R beta)
          - ExteriorAlgebra.ι R alpha * ExteriorAlgebra.ι R alpha
          - ExteriorAlgebra.ι R beta * ExteriorAlgebra.ι R beta := by noncomm_ring
      _ = ExteriorAlgebra.ι R (alpha + beta) * ExteriorAlgebra.ι R (alpha + beta) - 0 - 0 := by rw [← h_linear, h_a, h_b]
      _ = 0 - 0 - 0 := by rw [h_sum]
      _ = 0 := by noncomm_ring
  ext ψ
  dsimp [creation]
  have h1 : ExteriorAlgebra.ι R alpha * (ExteriorAlgebra.ι R beta * ψ) +
            ExteriorAlgebra.ι R beta * (ExteriorAlgebra.ι R alpha * ψ) =
            (ExteriorAlgebra.ι R alpha * ExteriorAlgebra.ι R beta +
             ExteriorAlgebra.ι R beta * ExteriorAlgebra.ι R alpha) * ψ := by noncomm_ring
  rw [h1, h_anti, zero_mul]

/-- **Master Synthesis**: Spinor Creation Operator CAR Algebra. -/
theorem master_split_spinor_car_synthesis (alpha beta : Module.Dual R U) :
    (creation alpha * creation alpha = 0) ∧
    (creation alpha * creation beta + creation beta * creation alpha = 0) := ⟨
  creation_sq_zero alpha,
  creation_anticomm alpha beta
⟩

end InfoGeometry.Canonical.SplitSpinorCARAlgebraBridge
