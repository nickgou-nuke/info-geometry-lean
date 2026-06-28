import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.Ring.Basic

open CategoryTheory Limits

/-- 
  Spacetime events ordered by causality.
  An arrow `A ⟶ B` exists if and only if `A ≤ B` causally. 
-/
def CausalSpacetime (α : Type*) := α

instance {α : Type*} [PartialOrder α] : PartialOrder (CausalSpacetime α) :=
  inferInstanceAs (PartialOrder α)

-- Mathlib automatically derives the Category instance for any Preorder!

variable {α : Type*} [PartialOrder α]

/-- 
  A Causal Functor maps the causal spacetime poset into the category of Algebras/Rings.
  The "bonding maps" are causal propagators of the physical system.
-/
abbrev CausalFunctor (α : Type*) [PartialOrder α] :=
  CausalSpacetime α ⥤ RingCat

/--
  The Universal Causal Future (The Future Light Cone) is exactly the Colimit
  of the Causal Functor. It binds the entire spreading history into a unified
  infinite-dimensional algebra.
-/
noncomputable abbrev UniversalCausalFuture
    (F : CausalFunctor α) [HasColimit F] : RingCat :=
  colimit F

/--
  The Causal Propagation Theorem:
  Information generated at a localized event `x` at time `A` propagates causally 
  into the Universal Causal Future. The identity of this information is conserved
  regardless of whether we view it directly from `A` or through a future intermediate event `B`.
-/
theorem causal_information_conservation
    (F : CausalFunctor α) [HasColimit F] 
    {A B : CausalSpacetime α} (causal_link : A ≤ B) 
    (x : F.obj A) :
    (colimit.ι F A) x = (colimit.ι F B) ((F.map (homOfLE causal_link)) x) := by
  have h := colimit.w F (homOfLE causal_link)
  exact congr_arg (fun (f : F.obj A ⟶ colimit F) => f x) h.symm

/--
  Two events are spacelike separated if they have no causal relationship.
  Neither can influence the other.
-/
def SpacelikeSeparated (A B : CausalSpacetime α) : Prop :=
  ¬(A ≤ B) ∧ ¬(B ≤ A)

notation A " ≁ " B => SpacelikeSeparated A B

/--
  Einstein Causality (The Haag-Kastler Locality Axiom).
  Observables at spacelike separated events must commute when pushed forward
  into the Universal Causal Future.
-/
class EinsteinCausality (F : CausalFunctor α) [HasColimit F] : Prop where
  commute_of_spacelike : ∀ {A B : CausalSpacetime α} (_h : A ≁ B) (x : F.obj A) (y : F.obj B),
    Commute ((colimit.ι F A) x) ((colimit.ι F B) y)
