import InfoGeometry.Physics.CuntzTransitionGramBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.HermitianDensityTangentSpace

/-!
# Normalized Cuntz Gram states

The normalized right Gramian is the finite density state associated with a
nonzero transition coefficient matrix.  This file only packages the
already-proved Hermitian, trace, and positivity laws; it does not introduce a
new density carrier or a logarithmic modular functional calculus.
-/

noncomputable section

namespace InfoGeometry.Physics.CuntzTransitionDensityBridge

open CuntzTransitionGramBridge
open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

def normalizedRightGramState [Nonempty n]
    (A : Mat n) (hT : gramTrace A ≠ 0) : HermitianDensityState n :=
  ⟨normalizedRightGram A,
    normalizedRightGram_isHermitian A,
    trace_normalizedRightGram A hT⟩

theorem normalizedRightGramState_apply [Nonempty n]
    (A : Mat n) (hT : gramTrace A ≠ 0) :
    (normalizedRightGramState A hT).1 = normalizedRightGram A := rfl

theorem normalizedRightGramState_posSemidef [Nonempty n]
    (A : Mat n) (hT : gramTrace A ≠ 0) :
    (normalizedRightGramState A hT).1.PosSemidef := by
  exact normalizedRightGram_posSemidef A

theorem traceFreePart_isHermitian [Nonempty n]
    {H : Mat n} (hH : H.IsHermitian) :
    (traceFreePart H).IsHermitian := by
  have htrace : star (Matrix.trace H) = Matrix.trace H := by
    rw [← Matrix.trace_conjTranspose, hH]
  unfold traceFreePart
  change (H - (((Fintype.card n : ℂ)⁻¹) * Matrix.trace H) •
      (1 : Mat n))ᴴ = H - (((Fintype.card n : ℂ)⁻¹) * Matrix.trace H) •
      (1 : Mat n)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hH]
  congr 1
  simp [htrace]

noncomputable def normalizedRightGramState_tangent [Nonempty n]
    (A : Mat n) (hT : gramTrace A ≠ 0) :
    HermitianDensityTangent (normalizedRightGramState A hT) := by
  refine ⟨traceFreePart (normalizedRightGram A), ?_, ?_⟩
  · exact traceFreePart_isHermitian (normalizedRightGram_isHermitian A)
  · exact trace_traceFreePart (normalizedRightGram A)

theorem normalizedRightGramState_traceFreePart [Nonempty n]
    (A : Mat n) (hT : gramTrace A ≠ 0) :
    (normalizedRightGramState A hT).1 =
      traceFreePart (normalizedRightGramState A hT).1 +
        ((Fintype.card n : ℂ)⁻¹) • (1 : Mat n) := by
  exact normalizedRightGram_eq_traceFreePart_add_uniform A hT

end InfoGeometry.Physics.CuntzTransitionDensityBridge
