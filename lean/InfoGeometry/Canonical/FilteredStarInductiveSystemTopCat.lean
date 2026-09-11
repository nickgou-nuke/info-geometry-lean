import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological arrows for filtered star-inductive systems

The algebraic filtered system already carries a continuous linear map for each
transition.  This owner exposes the same transition as a native `TopCat`
morphism, preserving the noncommutative star-algebra source rather than
introducing a scalar or diagonal surrogate.
-/

noncomputable section

namespace CStarStateColimit.Native.ContinuousStarInductiveSystem

open CategoryTheory

universe u

variable {I : Type u} [Preorder I]
variable {Stage : I → Type u}
variable [∀ i, CStarAlgebra (Stage i)]
variable {Ainf : Type u} [CStarAlgebra Ainf]

def transitionTopCatHom
    (sys : ContinuousStarInductiveSystem Stage)
    {i j : I} (hij : i ≤ j) :
    TopCat.of (Stage i) ⟶ TopCat.of (Stage j) :=
  TopCat.ofHom
    { toFun := fun a => sys.map hij a
      continuous_toFun :=
        (ContinuousStarInductiveSystem.transitionCLM Stage sys hij).continuous }

@[simp] theorem transitionTopCatHom_apply
    (sys : ContinuousStarInductiveSystem Stage)
    {i j : I} (hij : i ≤ j) (a : Stage i) :
    sys.transitionTopCatHom hij a = sys.map hij a :=
  by
    change (sys.map hij) a = (sys.map hij) a
    rfl

theorem transitionTopCatHom_continuous
    (sys : ContinuousStarInductiveSystem Stage)
    {i j : I} (hij : i ≤ j) :
    Continuous (sys.map hij) :=
  (ContinuousStarInductiveSystem.transitionCLM Stage sys hij).continuous

theorem transitionTopCatHom_id
    (sys : ContinuousStarInductiveSystem Stage) (i : I) :
    sys.transitionTopCatHom (le_refl i) = 𝟙 (TopCat.of (Stage i)) := by
  apply TopCat.hom_ext
  ext a
  rw [TopCat.id_app]
  change (sys.map (le_refl i)) a = a
  rw [sys.map_id]
  rfl

theorem transitionTopCatHom_comp
    (sys : ContinuousStarInductiveSystem Stage)
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    sys.transitionTopCatHom hij ≫ sys.transitionTopCatHom hjk =
      sys.transitionTopCatHom (le_trans hij hjk) := by
  apply TopCat.hom_ext
  ext a
  rw [TopCat.comp_app]
  change (sys.map hjk) ((sys.map hij) a) = (sys.map (le_trans hij hjk)) a
  exact congrArg (fun f : Stage i →⋆ₐ[ℂ] Stage k => f a)
    (sys.map_comp hij hjk)

theorem transitionTopCatHom_comp_cocone_ιTopCatHom
    (sys : ContinuousStarInductiveSystem Stage)
    (cocone :
      CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone
        (Ainf := Ainf) Stage sys)
    {i j : I} (hij : i ≤ j) :
    sys.transitionTopCatHom hij ≫
        CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone.ιTopCatHom
          (Stage := Stage) (sys := sys) cocone j =
      CStarStateColimit.Native.ContinuousStarInductiveSystem.StarInductiveCocone.ιTopCatHom
        (Stage := Stage) (sys := sys) cocone i := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  rw [TopCat.comp_app]
  exact congrArg (fun f : Stage i →⋆ₐ[ℂ] Ainf => f a)
    (cocone.ι_comm hij)

end CStarStateColimit.Native.ContinuousStarInductiveSystem
