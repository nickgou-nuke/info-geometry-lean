import InfoGeometry.Canonical.CausalFunctor
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Subring.Basic

open CategoryTheory Limits

variable {α : Type*} [PartialOrder α]

/--
  The Modular Automorphism Group generates the intrinsic flow of time
  for a quantum geometry. For a given Universal Causal Future, it is a
  one-parameter group of automorphisms parameterized by the real numbers ℝ.
-/
abbrev ModularAutomorphismGroup (F : CausalFunctor α) [HasColimit F] :=
  Multiplicative ℝ →* Aut (UniversalCausalFuture F)

/--
  A state on the algebra is invariant under the modular time-evolution if 
  evaluating the state on an observable before and after the modular flow 
  yields the same result.
  (In Tomita-Takesaki theory, the KMS state is invariant under its own modular group).
-/
def IsModularInvariantState (F : CausalFunctor α) [HasColimit F] 
    (σ : ModularAutomorphismGroup F) 
    (ω : UniversalCausalFuture F → ℝ) : Prop :=
  ∀ (t : Multiplicative ℝ) (x : UniversalCausalFuture F),
    ω (((σ t).hom : UniversalCausalFuture F → UniversalCausalFuture F) x) = ω x

/--
  The Tomita-Takesaki Time-Evolution Generator.
  If the Causal Functor satisfies Einstein Causality, its global modular flow 
  must preserve the spacelike commutativity of the localized observables.
-/
theorem modular_evolution_preserves_commutativity 
    (F : CausalFunctor α) [HasColimit F] (hca : EinsteinCausality F)
    (σ : ModularAutomorphismGroup F)
    {A B : CausalSpacetime α} (h : A ≁ B) (x : F.obj A) (y : F.obj B) (t : Multiplicative ℝ) :
    Commute 
      (((σ t).hom : UniversalCausalFuture F → UniversalCausalFuture F) ((colimit.ι F A) x)) 
      (((σ t).hom : UniversalCausalFuture F → UniversalCausalFuture F) ((colimit.ι F B) y)) := by
  have h_comm := EinsteinCausality.commute_of_spacelike (F := F) hca h x y
  -- Since σ(t) is an algebra automorphism, it preserves algebraic commutativity.
  dsimp [Commute, SemiconjBy] at h_comm ⊢
  -- applying the ring homomorphism
  have H := congr_arg (σ t).hom h_comm
  simp only [map_mul] at H
  exact H

/--
  The Modular Fixed Point Space (KMS States):
  The set of elements inside the Universal Causal Future that are completely 
  invariant under the modular time-evolution flow σ_t.
-/
def KMSFixedPoints (F : CausalFunctor α) [HasColimit F]
    (σ : ModularAutomorphismGroup F) : Set (UniversalCausalFuture F) :=
  { x | ∀ t : Multiplicative ℝ, (σ t).hom x = x }
