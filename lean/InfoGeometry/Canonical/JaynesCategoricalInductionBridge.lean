import InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
import InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge

/-!
# InfoGeometry.Canonical.JaynesCategoricalInductionBridge

Categorical induction bridge for finite Jaynes centered scores.

This file uses the existing category-language direct-limit lane:

* finite stages are profile rings `Atom n → ℝ`;
* one-step bonds are ring homomorphisms between profile rings;
* a compatible cone evaluates finite profiles in a target ring;
* reference and observation profiles are transported explicitly along the bonds;
* therefore the additive centered score `obs - reference` is transported along
  the same cone, and its compatible-cone image is stage-independent.

No entropy convergence theorem.
No probability-measure/LDDS limit.
No global-state uniqueness theorem.
No spectral, Tomita, or analytic-completion claim.
-/

namespace JaynesCategoricalInductionBridge

open InfoGeometry.Canonical.CategoricalRecursiveClosureBridge
open InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge
open InfoGeometry.Canonical.FiniteJaynesCenteredScoreBridge.FiniteReferenceStateOps
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

universe u

variable {Atom : Nat → Type u} [∀ n : Nat, Fintype (Atom n)]
variable {Limit : Type u} [Ring Limit]

/-- The profile ring at a finite Jaynes stage. -/
abbrev ProfileStage (Atom : Nat → Type u) (n : Nat) := Atom n → ℝ

/--
A categorical finite-Jaynes cone: profile-ring bonds, a compatible target cone,
and explicitly transported reference/observation profiles.
-/
structure JaynesCategoricalCone where
  /-- One-step profile-ring bonding maps. -/
  bond : ∀ n : Nat, ProfileStage Atom n →+* ProfileStage Atom (n + 1)
  /-- Compatible cone into a target ring. -/
  toLimit : ∀ n : Nat, ProfileStage Atom n →+* Limit
  /-- Cone compatibility. -/
  hcone : ConeCompatible bond toLimit
  /-- Stagewise reference profiles. -/
  reference : ∀ n : Nat, FiniteReferenceState (Atom n)
  /-- Stagewise observation profiles. -/
  observation : ∀ n : Nat, FiniteProfile (Atom n)
  /-- References are transported by the bonding maps. -/
  reference_compatible : ∀ n : Nat,
    bond n ((reference n).weight) = (reference (n + 1)).weight
  /-- Observations are transported by the bonding maps. -/
  observation_compatible : ∀ n : Nat,
    bond n (observation n) = observation (n + 1)

namespace JaynesCategoricalCone

variable (P : JaynesCategoricalCone (Atom := Atom) (Limit := Limit))

/-- The additive centered score at a finite stage. -/
def centered (n : Nat) : ProfileStage Atom n :=
  P.observation n - (P.reference n).weight

omit [∀ n : Nat, Fintype (Atom n)] in
/-- Centered scores are compatible with the finite profile-ring bonds. -/
theorem centered_compatible (n : Nat) :
    P.bond n (P.centered n) = P.centered (n + 1) := by
  unfold centered
  rw [map_sub, P.observation_compatible n, P.reference_compatible n]

omit [∀ n : Nat, Fintype (Atom n)] in
/--
Category-language stage-image constancy for finite Jaynes centered scores.
This is the precise cone/direct-limit form of the finite Jaynes induction law.
-/
theorem centered_stageImage_constant :
    ∀ n : Nat, P.toLimit n (P.centered n) = P.toLimit 0 (P.centered 0) :=
  cone_stageImage_constant (Stage := fun n => ProfileStage Atom n) (Limit := Limit)
    P.bond P.toLimit P.hcone P.centered P.centered_compatible

omit [∀ n : Nat, Fintype (Atom n)] in
/-- Direct-limit readback for a finite centered score through the compatible cone. -/
theorem centered_directLimit_readback (n : Nat) :
    directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n (P.centered n)) =
      P.toLimit n (P.centered n) :=
  directLimit_readback (Stage := fun n => ProfileStage Atom n) (Limit := Limit)
    P.bond P.toLimit P.hcone n (P.centered n)

omit [∀ n : Nat, Fintype (Atom n)] in
/-- Direct-limit readback of the stage `n` centered score equals the seed-stage cone image. -/
theorem centered_directLimit_eq_seed (n : Nat) :
    directLimitLift P.bond P.toLimit P.hcone (directLimitOf P.bond n (P.centered n)) =
      P.toLimit 0 (P.centered 0) := by
  rw [P.centered_directLimit_readback n, P.centered_stageImage_constant n]

omit [∀ n : Nat, Fintype (Atom n)] in
/-- Uniqueness of a cone evaluation on the direct limit, specialized to this Jaynes cone. -/
theorem factorization_unique
    (g : DirectLimitSuperClosure P.bond →+* Limit)
    (hg : ∀ n : Nat, g.comp (directLimitOf P.bond n) = P.toLimit n) :
    g = directLimitLift P.bond P.toLimit P.hcone :=
  directLimit_factorization_unique (Stage := fun n => ProfileStage Atom n) (Limit := Limit)
    P.bond P.toLimit P.hcone g hg

end JaynesCategoricalCone

end JaynesCategoricalInductionBridge
