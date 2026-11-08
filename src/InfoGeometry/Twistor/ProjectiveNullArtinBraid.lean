import InfoGeometry.Twistor.NullProjective
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Artin braid generators on a projective null boundary

This owner transports an explicit linear Artin braid relation through
Mathlib's projectivization and proves preservation of a quadratic null locus
from an explicit quadratic-form preservation theorem.  It does not construct
an anyon model, identify a Fibonacci category with a conformal boundary, or
claim a physical braid-group realization.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Twistor.ProjectiveNullArtinBraid

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def projectiveGenerator (ρ : ℕ → (V ≃ₗ[K] V)) (i : ℕ) : ℙ K V → ℙ K V :=
  Projectivization.map (ρ i).toLinearMap (ρ i).injective

theorem projectiveGenerator_preserves_null
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (i : ℕ) (hQ : ∀ v : V, Q (ρ i v) = Q v)
    (p : ℙ K V) :
    IsNull Q p → IsNull Q (projectiveGenerator ρ i p) := by
  refine Projectivization.ind (p := p) ?_
  intro v hv hp
  rw [projectiveGenerator, Projectivization.map_mk]
  rw [isNull_mk_iff]
  rw [show Q ((ρ i).toLinearMap v) = Q v by simpa using hQ v]
  exact (isNull_mk_iff Q v hv).mp hp

/-! ## The induced action on the null-boundary subtype -/

/-- The projectivized linear generator restricted to the quadratic null boundary.

This is a genuine subtype action: the proof component is supplied by the
quadratic-form preservation theorem, rather than postulated as structure data.
-/
def nullProjectiveGenerator
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v) (i : ℕ) :
    TwistorSpace Q → TwistorSpace Q := by
  intro p
  exact ⟨projectiveGenerator ρ i p.1,
    projectiveGenerator_preserves_null Q ρ i (hQ i) p.1 p.2⟩

theorem projectiveGenerator_artin_relation
    (ρ : ℕ → (V ≃ₗ[K] V))
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (i : ℕ) (p : ℙ K V) :
    projectiveGenerator ρ i
        (projectiveGenerator ρ (i + 1) (projectiveGenerator ρ i p)) =
      projectiveGenerator ρ (i + 1)
        (projectiveGenerator ρ i (projectiveGenerator ρ (i + 1) p)) := by
  refine Projectivization.ind (p := p) ?_
  intro v hv
  simp only [projectiveGenerator, Projectivization.map_mk]
  congr 1
  exact congrArg (fun f : V →ₗ[K] V => f v) (hArtin i)

theorem nullProjectiveGenerator_artin_relation
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (hArtin : ∀ i : ℕ,
      (ρ i).toLinearMap.comp
          ((ρ (i + 1)).toLinearMap.comp (ρ i).toLinearMap) =
        (ρ (i + 1)).toLinearMap.comp
          ((ρ i).toLinearMap.comp (ρ (i + 1)).toLinearMap))
    (i : ℕ) (p : TwistorSpace Q) :
    nullProjectiveGenerator Q ρ hQ i
        (nullProjectiveGenerator Q ρ hQ (i + 1)
          (nullProjectiveGenerator Q ρ hQ i p)) =
      nullProjectiveGenerator Q ρ hQ (i + 1)
        (nullProjectiveGenerator Q ρ hQ i
          (nullProjectiveGenerator Q ρ hQ (i + 1) p)) := by
  apply Subtype.ext
  exact projectiveGenerator_artin_relation ρ hArtin i p.1

theorem projectiveGenerator_commute_relation
    (ρ : ℕ → (V ≃ₗ[K] V))
    (i j : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (p : ℙ K V) :
    projectiveGenerator ρ i (projectiveGenerator ρ j p) =
      projectiveGenerator ρ j (projectiveGenerator ρ i p) := by
  refine Projectivization.ind (p := p) ?_
  intro v hv
  simp only [projectiveGenerator, Projectivization.map_mk]
  congr 1
  exact congrArg (fun f : V →ₗ[K] V => f v) hComm

theorem nullProjectiveGenerator_commute_relation
    (Q : QuadraticForm K V) (ρ : ℕ → (V ≃ₗ[K] V))
    (hQ : ∀ i v, Q (ρ i v) = Q v)
    (i j : ℕ)
    (hComm : (ρ i).toLinearMap.comp (ρ j).toLinearMap =
      (ρ j).toLinearMap.comp (ρ i).toLinearMap)
    (p : TwistorSpace Q) :
    nullProjectiveGenerator Q ρ hQ i
        (nullProjectiveGenerator Q ρ hQ j p) =
      nullProjectiveGenerator Q ρ hQ j
        (nullProjectiveGenerator Q ρ hQ i p) := by
  apply Subtype.ext
  exact projectiveGenerator_commute_relation ρ i j hComm p.1

end InfoGeometry.Twistor.ProjectiveNullArtinBraid
