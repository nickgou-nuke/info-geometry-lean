import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.RingTheory.Finiteness.Basic
import InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
import InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive

/-!
# Factor permutations on finite-projective module classes

This bridge starts from the actual finite-projective module carrier and the
coordinate ring equivalences on `A × A × A`. It makes no claim about
`Out(D₄)`: the symmetries considered here are factor permutations of this
explicit product ring.
-/

universe u

namespace InfoGeometry.SuperGrassmannian.TrialityProjectiveK0Action

open InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
open InfoGeometry.SuperGrassmannian.TrialityAutomorphismMotive

variable {R : Type u} [Ring R]

local instance ringHomInvPairEquiv (e : R ≃+* R) :
    RingHomInvPair (e : R →+* R) (e.symm : R →+* R) :=
  RingHomInvPair.of_ringEquiv e

local instance ringHomInvPairEquivSymm (e : R ≃+* R) :
    RingHomInvPair (e.symm : R →+* R) (e : R →+* R) :=
  RingHomInvPair.symm (e : R →+* R) (e.symm : R →+* R)

/-- A genuinely distinct carrier used for scalar-twisted module structures. -/
def TwistedCarrier (e : R ≃+* R) (M : ModuleCat.{u} R) : Type u := ULift.{0} M

/-- The lifted carrier inherits the additive group structure of the module object. -/
noncomputable instance twistedCarrierAddCommGroup (e : R ≃+* R) (M : ModuleCat.{u} R) :
    AddCommGroup (TwistedCarrier e M) := by
  letI : AddCommGroup M := M.isAddCommGroup
  change AddCommGroup (ULift.{0} M)
  infer_instance

/-- The action on the lifted carrier is reindexed by the inverse ring equivalence. -/
noncomputable instance twistedCarrierModule (e : R ≃+* R) (M : ModuleCat.{u} R) :
    Module R (TwistedCarrier e M) := by
  letI : AddCommGroup M := M.isAddCommGroup
  letI : Module R M := M.isModule
  change Module R (ULift.{0} M)
  letI : Module R (ULift.{0} M) := ULift.module' (R := R) (M := M)
  exact Module.compHom (M := ULift.{0} M) (e.symm : R →+* R)

/-- Pull a left module back along the inverse of a ring automorphism. -/
noncomputable def transportedModule (e : R ≃+* R) (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (TwistedCarrier e M)

/-- The carrier identity identifies the original module with its transported module
semilinearly, using the coefficient map `e`. -/
noncomputable def transportEquiv (e : R ≃+* R) (M : ModuleCat.{u} R) :
    (M : Type u) ≃ₛₗ[(e : R →+* R)] (transportedModule e M : Type u) := by
  letI : AddCommGroup M := M.isAddCommGroup
  letI : Module R M := M.isModule
  exact
    { toEquiv := ((AddEquiv.ulift : ULift.{0} M ≃+ M).symm).toEquiv
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro r x
        apply ULift.ext
        change r • x = e.symm (e r) • x
        simp }

/-- Ring-equivalence transport preserves finite generation. -/
theorem transportedModule_finite (e : R ≃+* R) (M : ModuleCat.{u} R)
    (hM : Module.Finite R M) : Module.Finite R (transportedModule e M) := by
  letI : Module.Finite R M := hM
  let f : M →ₛₗ[(e : R →+* R)] (transportedModule e M : Type u) := transportEquiv e M
  have hf : Function.Surjective f := by
    intro y
    exact ⟨(transportEquiv e M).symm y, rfl⟩
  exact Module.Finite.of_surjective (σ := (e : R →+* R)) f hf

/-- Ring-equivalence transport preserves projectivity. -/
theorem transportedModule_projective (e : R ≃+* R) (M : ModuleCat.{u} R)
    (hM : Module.Projective R M) :
    Module.Projective R (transportedModule e M) := by
  letI : Module.Projective R M := hM
  letI : RingHomInvPair (e : R →+* R) (e.symm : R →+* R) :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair (e.symm : R →+* R) (e : R →+* R) :=
    RingHomInvPair.symm (e : R →+* R) (e.symm : R →+* R)
  exact Module.Projective.of_equiv (transportEquiv e M)

/-- A finite projective module, transported along a ring automorphism. -/
noncomputable def transportFiniteProjective (e : R ≃+* R) (M : FiniteProjectiveModule R) :
    FiniteProjectiveModule R := by
  refine ⟨transportedModule e M.1, ?_, ?_⟩
  · exact transportedModule_finite e M.1 M.2.1
  · exact transportedModule_projective e M.1 M.2.2

end InfoGeometry.SuperGrassmannian.TrialityProjectiveK0Action
