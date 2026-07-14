import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.Cl11TensorTower
import Mathlib.Data.Matrix.Basic

noncomputable section

namespace Cl11TrifactorPropagation

open InfoGeometry.Clifford.Cl11TensorTower

/-!
# Cl(1,1) Matrix-Stage Trifactor Propagation

#### BUCKET 1: CLOSED FINITE THEOREMS
This file proves that the repo's finite matrix-stage embedding
`A ↦ A ⊗ I₂` preserves idempotence, cubic/tripotent identities, and
binary-volume normalized trace along every finite stage.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
The propagated identities are conditional on the corresponding base-stage
identity: `P * P = P` or `P * P * P = P`.

#### BUCKET 3: OPEN CLOSURE DEBT
This file does not prove a universal Clifford isomorphism
`Cl(p+1,q+1) ≃ Cl(1,1) ⊗ Cl(p,q)`, does not construct
`Cl(∞,∞)`, and does not prove octonionic, Cartan, KAN, or analytic limit
claims.  It is the finite matrix-stage propagation layer built on
`Cl11TensorTower.matStageEmbed`.
-/

/-- Define the propagation of a base Cl(1,1) operator up to stage n. -/
def propagateOperator : (n : ℕ) → MatStage 1 → MatStage (n + 1)
| 0, P => P
| (n + 1), P => matStageEmbed (n + 1) (propagateOperator n P)

/-- The fundamental projection symmetry P² = P is preserved under the Cl(1,1) embedding step. -/
theorem matStageEmbed_idempotent (n : ℕ) (P : MatStage n) (h : P * P = P) :
    matStageEmbed n P * matStageEmbed n P = matStageEmbed n P := by
  rw [← matStageEmbed_mul, h]

/-- The trifactor cubic symmetry OP³ = OP is preserved under the Cl(1,1) embedding step. -/
theorem matStageEmbed_cubic_idempotent (n : ℕ) (P : MatStage n) (h : P * P * P = P) :
    matStageEmbed n P * matStageEmbed n P * matStageEmbed n P = matStageEmbed n P := by
  rw [← matStageEmbed_mul, ← matStageEmbed_mul, h]

/-- The idempotent projector OP symmetry propagates to all CL(1,1) × CL(n,n) bounds.
    If OP is a projector in Cl(1,1), it remains a valid projector at stage n. -/
theorem propagation_preserves_idempotent (n : ℕ) (P : MatStage 1) (h : P * P = P) :
    propagateOperator n P * propagateOperator n P = propagateOperator n P := by
  induction n with
  | zero => exact h
  | succ n ih => 
      dsimp [propagateOperator]
      exact matStageEmbed_idempotent (n + 1) (propagateOperator n P) ih

/-- The cubic trifactor symmetry OP³ = OP propagates to all stages n. -/
theorem propagation_preserves_cubic (n : ℕ) (P : MatStage 1) (h : P * P * P = P) :
    propagateOperator n P * propagateOperator n P * propagateOperator n P = propagateOperator n P := by
  induction n with
  | zero => exact h
  | succ n ih => 
      dsimp [propagateOperator]
      exact matStageEmbed_cubic_idempotent (n + 1) (propagateOperator n P) ih

/--
The binary-volume normalized trace of a propagated finite matrix is stage
independent.  This is the finite trace readout of the tensor embedding
`A ↦ A ⊗ I₂`.
-/
theorem propagation_preserves_normalizedTrace (n : ℕ) (P : MatStage 1) :
    normalizedTrace (n + 1) (propagateOperator n P) = normalizedTrace 1 P := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      dsimp [propagateOperator]
      rw [normalizedTrace_matStageEmbed]
      exact ih

end Cl11TrifactorPropagation
