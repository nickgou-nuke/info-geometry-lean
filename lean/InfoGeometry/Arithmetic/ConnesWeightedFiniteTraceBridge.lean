import InfoGeometry.Arithmetic.ConnesFiniteTraceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Weighted finite trace shadow

This owner combines two already-closed finite readouts: the logarithmic idele
character and the trace of a finite permutation action.  The two factors are
kept separate; no multiplicativity of fixed-point counts under composition is
asserted, and no adelic or distributional trace formula is claimed.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ConnesWeightedFiniteTraceBridge

open InfoGeometry.Arithmetic.ConnesFiniteTraceBridge
open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry

variable {X G : Type*} [Fintype X] [DecidableEq X]
variable [Group G]

/-- The finite weighted trace formed from an idele scale character and a
permutation trace. -/
def weightedPermutationTrace
    (A : IdeleClassLayer G) (σ : Equiv.Perm X) (s : ℂ) : ℂ :=
  ideleScaleCharacter A s * permutationTrace σ

theorem weightedPermutationTrace_eq_character_mul_fixedPointCount
    (A : IdeleClassLayer G) (σ : Equiv.Perm X) (s : ℂ) :
    weightedPermutationTrace A σ s =
      ideleScaleCharacter A s * (fixedPointCount σ : ℂ) := by
  unfold weightedPermutationTrace
  rw [permutationTrace_eq_fixedPointCount]

theorem weightedPermutationTrace_identity
    (σ : Equiv.Perm X) (s : ℂ) :
    weightedPermutationTrace
        (IdeleClassLayer.identity : IdeleClassLayer G) σ s =
      permutationTrace σ := by
  simp [weightedPermutationTrace, ideleScaleCharacter,
    IdeleClassLayer.identity]

/-- Weighted trace for a finite monoid action, with the scale datum kept
explicit because no identification of `A` with an acting element is assumed. -/
def weightedActionTrace
    {M : Type*} [Monoid M]
    (A : IdeleClassLayer G) (ρ : M →* Equiv.Perm X) (g : M) (s : ℂ) : ℂ :=
  ideleScaleCharacter A s * actionTrace ρ g

theorem weightedActionTrace_identity
    {M : Type*} [Monoid M]
    (A : IdeleClassLayer G) (ρ : M →* Equiv.Perm X) (s : ℂ) :
    weightedActionTrace A ρ 1 s =
      ideleScaleCharacter A s * (Fintype.card X : ℂ) := by
  unfold weightedActionTrace
  rw [actionTrace_one]

theorem weightedActionTrace_identity_layer
    {M : Type*} [Monoid M]
    (ρ : M →* Equiv.Perm X) (g : M) (s : ℂ) :
    weightedActionTrace
        (IdeleClassLayer.identity : IdeleClassLayer G) ρ g s =
      actionTrace ρ g := by
  simp [weightedActionTrace, ideleScaleCharacter,
    IdeleClassLayer.identity]

end InfoGeometry.Arithmetic.ConnesWeightedFiniteTraceBridge
