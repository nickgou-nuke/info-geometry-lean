import InfoGeometry.Canonical.AlgebraicStarEnvelope
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzStarInductiveSystem

/-!
# Cuntz generators in the algebraic star envelope

This owner is the exact bridge from a coherent finite Cuntz star tower to its
filtered algebraic star envelope.  It uses no norm completion and makes no
claim about a C*-state; it only transports generators, adjoints, and range
projections through the universal star-algebra map.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzAlgebraicStarEnvelope

open InfoGeometry.Canonical.AlgebraicStarEnvelope
open InfoGeometry.Canonical.CuntzStarInductiveSystem

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

abbrev Envelope : Type :=
  AlgebraicStarEnvelope.Carrier Stage T.toContinuousStarInductiveSystem

def injection (n : ℕ) : Stage n →⋆ₐ[ℂ] Envelope Stage T :=
  AlgebraicStarEnvelope.stageInjection Stage T.toContinuousStarInductiveSystem n

def generator (n : ℕ) (i : Fin n) : Envelope Stage T :=
  injection Stage T n ((T.family n).S i)

omit [∀ n, PartialOrder (Stage n)] [∀ n, StarOrderedRing (Stage n)] in
@[simp] theorem generator_transition
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    generator Stage T n (Fin.castLE hmn i) =
      generator Stage T m i := by
  unfold generator injection
  rw [← T.map_generator hmn i]
  exact AlgebraicStarEnvelope.stageInjection_transition
    Stage T.toContinuousStarInductiveSystem hmn _

omit [∀ n, PartialOrder (Stage n)] [∀ n, StarOrderedRing (Stage n)] in
@[simp] theorem generator_star (n : ℕ) (i : Fin n) :
    star (generator Stage T n i) =
      injection Stage T n (star ((T.family n).S i)) := by
  change star ((injection Stage T n) ((T.family n).S i)) = _
  rw [map_star]

omit [∀ n, PartialOrder (Stage n)] [∀ n, StarOrderedRing (Stage n)] in
@[simp] theorem generator_projector (n : ℕ) (i : Fin n) :
    generator Stage T n i * star (generator Stage T n i) =
      injection Stage T n
        ((T.family n).S i * star ((T.family n).S i)) := by
  change (injection Stage T n) ((T.family n).S i) *
      star ((injection Stage T n) ((T.family n).S i)) = _
  have hstar := StarHomClass.map_star
    (injection Stage T n) ((T.family n).S i)
  rw [← hstar, ← map_mul]

theorem generator_transition_projector
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    injection Stage T n
        ((T.family n).S (Fin.castLE hmn i) *
          star ((T.family n).S (Fin.castLE hmn i))) =
      injection Stage T m
        ((T.family m).S i * star ((T.family m).S i)) := by
  rw [← CuntzStarTower.map_projector (Stage := Stage) T hmn i]
  exact AlgebraicStarEnvelope.stageInjection_transition
    Stage T.toContinuousStarInductiveSystem hmn _

end InfoGeometry.Canonical.CuntzAlgebraicStarEnvelope

end noncomputable section
