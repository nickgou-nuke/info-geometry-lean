import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Algebra.Monoid

/-!
# Continuous left actions in `TopCat`

This owner packages the topological part of a left monoid action without
introducing coordinates or a completion.  Composition in `TopCat` acts on the
right, so the resulting map is contravariant in the acting element; the
composition theorem records that order explicitly.
-/

noncomputable section

namespace InfoGeometry.Canonical.ContinuousLeftActionTopCat

open CategoryTheory

universe u v

variable {M : Type u} {X : Type v} [Monoid M] [TopologicalSpace X]

/-- A left monoid action whose individual translations are continuous. -/
structure ContinuousLeftAction (M : Type u) (X : Type v)
    [Monoid M] [TopologicalSpace X] where
  smul : M → X → X
  one_smul : ∀ x, smul 1 x = x
  mul_smul : ∀ (a b : M) (x : X), smul (a * b) x = smul a (smul b x)
  continuous_smul : ∀ a, Continuous (smul a)

/-- The regular left action of a topological monoid on itself. -/
def regularLeftAction {M : Type u} [Monoid M] [TopologicalSpace M]
    [ContinuousMul M] : ContinuousLeftAction M M where
  smul a x := a * x
  one_smul x := one_mul x
  mul_smul a b x := mul_assoc a b x
  continuous_smul a :=
    (continuous_const : Continuous (fun _ : M => a)).mul continuous_id

variable (A : ContinuousLeftAction M X)

/-- The continuous translation associated with one acting element. -/
def translation (a : M) : TopCat.of X ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := A.smul a
      continuous_toFun := A.continuous_smul a }

@[simp] theorem translation_apply (a : M) (x : X) :
    translation A a x = A.smul a x :=
  rfl

theorem translation_one :
    translation A 1 = 𝟙 (TopCat.of X) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact A.one_smul x

theorem translation_comp (a b : M) :
    translation A a ≫ translation A b =
      translation A (b * a) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change A.smul b (A.smul a x) = A.smul (b * a) x
  exact (A.mul_smul b a x).symm

theorem translation_word (a b c : M) :
    translation A a ≫ translation A b ≫ translation A c =
      translation A (c * b * a) := by
  rw [translation_comp, translation_comp]

end InfoGeometry.Canonical.ContinuousLeftActionTopCat
