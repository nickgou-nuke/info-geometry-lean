import InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
import InfoGeometry.Algebra.InfiniteSuperClosureLemmas

/-!
# InfoGeometry.Canonical.CategoricalRecursiveClosureBridge

Category-theoretic language for inductive proof.

The theorem content here is the same recursive architecture already present in
the algebra layer:

* a bonding family of homomorphisms;
* a compatible cone to a target object;
* a universal direct-limit factorization;
* stagewise invariance read back at the limit.

This is the category-language version of "base case + successor step".
-/

namespace CategoricalRecursiveClosureBridge

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.InfiniteSuperClosureLemmas

universe u

section CompatibleCone

variable {Stage : Nat → Type u} [∀ n : Nat, Semiring (Stage n)]
variable {Limit : Type u} [Semiring Limit]

/-- Category-language alias for the cone compatibility predicate. -/
abbrev ConeCompatible
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit) : Prop :=
  InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.CompatibleCone bond toLimit

/-- A cone-compatible family has stage-independent limit images. -/
theorem cone_stageImage_constant
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : InfoGeometry.Algebra.InfiniteSuperClosureLemmas.CompatibleCone bond toLimit)
    (F : ∀ n : Nat, Stage n)
    (hF : ∀ n, bond n (F n) = F (n + 1)) :
    ∀ n : Nat, toLimit n (F n) = toLimit 0 (F 0) :=
  compatibleCone_image_eq_zero bond toLimit hcone F hF

/--
Universal factorization through the algebraic direct limit.

This is the categorical statement that the recursive system is determined by
its compatible cone into the target object.
-/
theorem directLimit_factorization_unique
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.CompatibleCone bond toLimit)
    (g : DirectLimitSuperClosure bond →+* Limit)
    (hg : ∀ n : Nat, g.comp (directLimitOf bond n) = toLimit n) :
    g = directLimitLift bond toLimit hcone :=
  directLimitLift_unique bond toLimit hcone g hg

/-- The canonical image of a finite stage in the direct limit is read back by the cone. -/
theorem directLimit_readback
    (bond : ∀ n : Nat, Stage n →+* Stage (n + 1))
    (toLimit : ∀ n : Nat, Stage n →+* Limit)
    (hcone : InfoGeometry.Algebra.DirectLimitSuperClosureLemmas.CompatibleCone bond toLimit)
    (n : Nat) (x : Stage n) :
    directLimitLift bond toLimit hcone (directLimitOf bond n x) = toLimit n x :=
  directLimitLift_of bond toLimit hcone n x

end CompatibleCone

end CategoricalRecursiveClosureBridge
