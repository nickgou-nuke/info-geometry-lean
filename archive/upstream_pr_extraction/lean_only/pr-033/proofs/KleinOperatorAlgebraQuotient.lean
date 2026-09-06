import proofs.KleinBrillouinBase
import proofs.KleinSixStateProjectiveMonodromy
import Mathlib.Topology.Constructions

/-!
# Honest operator-algebra quotient and deck-group lift

The concrete `ZMod 2` deck action has a genuine lift to `U6`, while the
full presented Klein holonomy is only projective.  This file packages the
honest conjugation action on `M₆(ℂ)` as an algebraic orbit quotient; it does
not claim local triviality of the quotient projection.
-/

noncomputable section
namespace KleinOperatorAlgebraQuotient

open KleinBrillouinBase
open KleinSixStateBundle
open KleinSixStateProjectiveMonodromy
open ProjectiveUnitary6
open TwoSheetThreeColorWeyl

abbrev Operator := Matrix (Fin 6) (Fin 6) ℂ
abbrev Deck2 := ZMod 2
abbrev OperatorTotal := BrillouinTorus × Operator

/-- Genuine explicit `ZMod 2` lift of the concrete sheet action. -/
def deckFibreAction (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) : Deck2 → U6 :=
  fun g => if g = 0 then 1 else thetaU6 ω hω

@[simp] theorem deckFibreAction_zero (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    deckFibreAction ω hω 0 = 1 := by simp [deckFibreAction]

@[simp] theorem deckFibreAction_one (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    deckFibreAction ω hω 1 = thetaU6 ω hω := by simp [deckFibreAction]

theorem deckFibreAction_theta_sq (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    (thetaU6 ω hω).1 * (thetaU6 ω hω).1 = 1 := by
  change reindexSix theta * reindexSix theta = 1
  rw [← map_mul, theta_sq ω hω]
  exact map_one reindexSix

/-- Conjugation action of the genuine deck lift on the operator fibre. -/
def operatorGlide (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    OperatorTotal → OperatorTotal := fun p =>
  (torusGlide p.1, reindexSix theta * p.2 * reindexSix theta)

theorem operatorGlide_involutive (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Involutive (operatorGlide ω hω) := by
  intro p
  rcases p with ⟨k, A⟩
  apply Prod.ext
  · exact torusGlide_involutive k
  · change (reindexSix theta * (reindexSix theta * A * reindexSix theta) *
      reindexSix theta) = A
    have hR : reindexSix theta * reindexSix theta = (1 : Operator) := by
      simpa using deckFibreAction_theta_sq ω hω
    calc
      reindexSix theta * (reindexSix theta * A * reindexSix theta) *
          reindexSix theta =
          (reindexSix theta * reindexSix theta) * A *
            (reindexSix theta * reindexSix theta) := by
              simp only [Matrix.mul_assoc]
    _ = A := by simpa [hR]

/-- The honest operator-algebra orbit relation. -/
def operatorSetoid (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    Setoid OperatorTotal where
  r x y := y = x ∨ y = operatorGlide ω hω x
  iseqv := by
    constructor
    · intro x; exact Or.inl rfl
    · intro x y h
      rcases h with rfl | h
      · exact Or.inl rfl
      · right
        rw [h, operatorGlide_involutive ω hω]
    · intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      · rcases hyz with rfl | hyz
        · exact Or.inr hxy
        · left
          rw [hyz, hxy, operatorGlide_involutive ω hω]

abbrev OperatorAssociatedQuotient (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) := Quotient (operatorSetoid ω hω)

def operatorQuotientMap (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) :
    OperatorTotal → OperatorAssociatedQuotient ω hω :=
  @Quotient.mk' _ (operatorSetoid ω hω)

theorem operatorQuotientMap_surjective (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Surjective (operatorQuotientMap ω hω) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  exact ⟨p, rfl⟩

/-- The central sign acts trivially on the operator fibre by conjugation. -/
theorem central_sign_conjugation (A : Operator) :
    (-(1 : Matrix (Fin 6) (Fin 6) ℂ)) * A * (-(1 : Matrix (Fin 6) (Fin 6) ℂ)) = A := by
  simp [Matrix.mul_assoc]

end KleinOperatorAlgebraQuotient
end noncomputable section
