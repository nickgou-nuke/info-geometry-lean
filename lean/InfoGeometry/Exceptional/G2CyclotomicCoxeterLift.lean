import InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornG2CoxeterRelations
import Mathlib.GroupTheory.Coxeter.Matrix

/-!
# Coxeter lift for the cyclotomic root action

This owner lifts the two already-defined cyclotomic reflections to the
`I₂(6)` Coxeter group.  It is independent of the standard dihedral action;
the latter uses a different reflection convention on the two sectors.
-/

namespace InfoGeometry.Exceptional.G2CyclotomicCoxeterLift

open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl

abbrev Root := InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.Root

def g2CoxeterMatrix : CoxeterMatrix (Fin 2) := CoxeterMatrix.G₂

theorem cyclotomicCoxeter_normal_form (w : g2CoxeterMatrix.Group) :
    ∃ k : ZMod 6,
      w = (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val ∨
        w = g2CoxeterMatrix.simple 0 *
          (g2CoxeterMatrix.simple 0 * g2CoxeterMatrix.simple 1) ^ k.val := by
  rcases InfoGeometry.Lie.CanonicalZornG2CoxeterRelations.g2Coxeter_normal_form w with h | h
  · rcases h with ⟨k, hk⟩
    exact ⟨k, Or.inl (by simpa [g2CoxeterMatrix] using hk)⟩
  · rcases h with ⟨k, hk⟩
    exact ⟨k, Or.inr (by simpa [g2CoxeterMatrix] using hk)⟩

noncomputable def cyclotomicReflectionGenerators : Fin 2 → Equiv.Perm Root
  | 0 => cyclotomicS1Perm
  | 1 => cyclotomicS2Perm

theorem cyclotomicReflectionGenerators_isLiftable :
    g2CoxeterMatrix.IsLiftable cyclotomicReflectionGenerators := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [cyclotomicReflectionGenerators] using cyclotomicS1Perm_sq
  · simpa [cyclotomicReflectionGenerators, g2CoxeterMatrix] using
      cyclotomicS1Perm_mul_S2Perm_pow_six
  · simpa [cyclotomicReflectionGenerators, g2CoxeterMatrix] using
      cyclotomicS2Perm_mul_S1Perm_pow_six
  · simpa [cyclotomicReflectionGenerators] using cyclotomicS2Perm_sq

noncomputable def cyclotomicCoxeterLift :
    g2CoxeterMatrix.Group →* Equiv.Perm Root :=
  g2CoxeterMatrix.toCoxeterSystem.lift
    ⟨cyclotomicReflectionGenerators, cyclotomicReflectionGenerators_isLiftable⟩

@[simp] theorem cyclotomicCoxeterLift_apply_simple (i : Fin 2) :
    cyclotomicCoxeterLift (g2CoxeterMatrix.simple i) =
      cyclotomicReflectionGenerators i := by
  exact CoxeterSystem.lift_apply_simple
    g2CoxeterMatrix.toCoxeterSystem
    cyclotomicReflectionGenerators_isLiftable i

end InfoGeometry.Exceptional.G2CyclotomicCoxeterLift
