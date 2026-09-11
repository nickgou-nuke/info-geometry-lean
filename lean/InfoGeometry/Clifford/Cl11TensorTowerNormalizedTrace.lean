import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The normalized trace net on the real `Cl(1,1)` matrix tower

This owner records only the finite-stage algebraic facts.  It does not assert a
completion, a C*-algebra, a KMS state, or a `K₀` continuity theorem.
-/

namespace InfoGeometry.Clifford.Cl11TensorTower

theorem matStageEmbed_preserves_idempotent
    (n : ℕ) (p : MatStage n) (hp : p * p = p) :
    matStageEmbed n p * matStageEmbed n p = matStageEmbed n p := by
  rw [← matStageEmbed_mul, hp]

theorem matStageEmbed_preserves_real_projection
    (n : ℕ) (p : MatStage n)
    (hp : IsIdempotentElem p ∧ star p = p) :
    IsIdempotentElem (matStageEmbed n p) ∧
      star (matStageEmbed n p) = matStageEmbed n p := by
  refine ⟨matStageEmbed_preserves_idempotent n p hp.1, ?_⟩
  -- The matrix star is entrywise real conjugation, hence the real embedding
  -- preserves the self-adjointness statement already present at the stage.
  have hp' : p.conjTranspose = p := by
    simpa only [Matrix.star_eq_conjTranspose] using hp.2
  have hpT : p.transpose = p := by
    ext i j
    have h := congrArg (fun M : MatStage n => M i j) hp'
    simpa [Matrix.conjTranspose_apply] using h
  rw [matStageEmbed, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker]
  simpa [hpT]

theorem trace_matStageEmbed_readout (n : ℕ) (A : MatStage n) :
    Matrix.trace (matStageEmbed n A) = 2 * Matrix.trace A :=
  matStageEmbed_trace n A

theorem normalizedTrace_matStageEmbed_readout (n : ℕ) (A : MatStage n) :
    normalizedTrace (n + 1) (matStageEmbed n A) = normalizedTrace n A :=
  normalizedTrace_matStageEmbed n A

end InfoGeometry.Clifford.Cl11TensorTower
