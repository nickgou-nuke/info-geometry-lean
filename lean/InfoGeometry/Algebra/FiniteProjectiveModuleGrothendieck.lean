import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Finiteness.Prod
import InfoGeometry.Algebra.Grothendieck

/-!
# Grothendieck group of finitely generated projective modules

This file starts the algebraic `K₀` construction from actual finitely generated
projective modules.  The carrier is the commutative monoid of module
isomorphism classes under direct sum; its group completion is the `K₀` object
defined here.  No product-ring decomposition or triality action is asserted.
-/

universe u

namespace InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck

variable (R : Type u) [Ring R]

/-- A bundled left `R`-module which is finitely generated and projective. -/
def FiniteProjectiveModule :=
  { M : ModuleCat.{u} R // Module.Finite R M ∧ Module.Projective R M }

variable {R}

/-- A product of two projective modules is projective. -/
theorem projective_prod (M N : ModuleCat.{u} R)
    (hM : Module.Projective R M) (hN : Module.Projective R N) :
    Module.Projective R (M × N) := by
  obtain ⟨sM, hsM⟩ := Module.projective_def'.1 hM
  obtain ⟨sN, hsN⟩ := Module.projective_def'.1 hN
  let rM : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  let rN : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R id
  let i : M × N →ₗ[R] (M →₀ R) × (N →₀ R) := LinearMap.prodMap sM sN
  let r : (M →₀ R) × (N →₀ R) →ₗ[R] M × N := LinearMap.prodMap rM rN
  haveI : Module.Projective R ((M →₀ R) × (N →₀ R)) := Module.Projective.of_free
  apply Module.Projective.of_split i r
  change (rM.prodMap rN).comp (sM.prodMap sN) = LinearMap.id
  rw [LinearMap.prodMap_comp, hsM, hsN, LinearMap.prodMap_id]

/-- The direct sum of two finitely generated projective left modules. -/
def directSum (R : Type u) [Ring R] (M N : FiniteProjectiveModule R) :
    FiniteProjectiveModule R := by
  letI : Module.Finite R M.1 := M.2.1
  letI : Module.Finite R N.1 := N.2.1
  letI : Module.Projective R M.1 := M.2.2
  letI : Module.Projective R N.1 := N.2.2
  refine ⟨ModuleCat.of R (M.1 × N.1), ?_, ?_⟩
  · infer_instance
  · exact projective_prod M.1 N.1 M.2.2 N.2.2

/-- Isomorphism of bundled modules is the equivalence relation on representatives. -/
def moduleIsoSetoid (R : Type u) [Ring R] : Setoid (FiniteProjectiveModule R) where
  r M N := Nonempty (M.1 ≅ N.1)
  iseqv := {
    refl := fun M => ⟨CategoryTheory.Iso.refl M.1⟩
    symm := fun {M N} h => by
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    trans := fun {M N P} h₁ h₂ => by
      rcases h₁ with ⟨e₁⟩
      rcases h₂ with ⟨e₂⟩
      exact ⟨e₁ ≪≫ e₂⟩
  }

/-- Isomorphism classes of finitely generated projective left `R`-modules. -/
def ProjectiveModuleClass (R : Type u) [Ring R] := Quotient (moduleIsoSetoid R)

/-- Direct sum on isomorphism classes of finitely generated projective modules. -/
def classAdd (R : Type u) [Ring R] :
    ProjectiveModuleClass R → ProjectiveModuleClass R → ProjectiveModuleClass R :=
  Quotient.map₂ (fun M N => directSum R M N) (by
    intro M M' hM N N' hN
    rcases hM with ⟨eM⟩
    rcases hN with ⟨eN⟩
    exact ⟨(eM.toLinearEquiv.prodCongr eN.toLinearEquiv).toModuleIso⟩)

/-- The class of the zero module. -/
def zeroModuleClass (R : Type u) [Ring R] : ProjectiveModuleClass R := by
  letI : Module.Finite R (Fin 0 → R) := inferInstance
  letI : Module.Projective R (Fin 0 → R) := Module.Projective.of_free
  exact Quotient.mk (moduleIsoSetoid R)
    ⟨ModuleCat.of R (Fin 0 → R), inferInstance, inferInstance⟩

/-- The additive commutative monoid of isomorphism classes of finite projectives. -/
instance (R : Type u) [Ring R] : AddCommMonoid (ProjectiveModuleClass R) where
  zero := zeroModuleClass R
  add := classAdd R
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ (s₁ := moduleIsoSetoid R) (s₂ := moduleIsoSetoid R)
      (s₃ := moduleIsoSetoid R) x y z ?_
    intro M N P
    apply Quotient.sound
    exact ⟨(LinearEquiv.prodAssoc R M.1 N.1 P.1).toModuleIso⟩
  zero_add := by
    intro x
    refine Quotient.inductionOn (s := moduleIsoSetoid R) x ?_
    intro M
    apply Quotient.sound
    exact ⟨(LinearEquiv.uniqueProd (R := R) (M := M.1)
      (M₂ := Fin 0 → R)).toModuleIso⟩
  add_zero := by
    intro x
    refine Quotient.inductionOn (s := moduleIsoSetoid R) x ?_
    intro M
    apply Quotient.sound
    exact ⟨(LinearEquiv.prodUnique (R := R) (M := M.1)
      (M₂ := Fin 0 → R)).toModuleIso⟩
  nsmul := fun n x => Nat.rec (zeroModuleClass R) (fun _ y => classAdd R y x) n
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl
  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ (s₁ := moduleIsoSetoid R) (s₂ := moduleIsoSetoid R) x y ?_
    intro M N
    apply Quotient.sound
    exact ⟨(LinearEquiv.prodComm R M.1 N.1).toModuleIso⟩

/-- Algebraic `K₀(R)`: the group completion of finite projective module classes. -/
noncomputable def K0 (R : Type u) [Ring R] : Type (u + 1) :=
  Grothendieck (ProjectiveModuleClass R)

/-- The class map from finitely generated projective modules to algebraic `K₀(R)`. -/
noncomputable def k0Class (R : Type u) [Ring R] (M : FiniteProjectiveModule R) : K0 R :=
  grothendieckMap (ProjectiveModuleClass R) (Quotient.mk _ M)

end InfoGeometry.Algebra.FiniteProjectiveModuleGrothendieck
