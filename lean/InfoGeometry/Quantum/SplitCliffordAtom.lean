import Mathlib.CategoryTheory.ConcreteCategory.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.RealKCategory
import InfoGeometry.Quantum.RealMajoranaCategory
set_option linter.unusedVariables false

open CategoryTheory

universe u

namespace InfoGeometry.Quantum.SplitCliffordAtom

abbrev RealMajoranaCore := RealMajoranaCategory.RealMajoranaCore
abbrev RealMajoranaCore.Hom := RealMajoranaCategory.RealMajoranaCore.Hom
abbrev RealKCategory := RealKCategory.RealKVect

/--
Equivariant split-Clifford atom: a real carrier with the primitive Majorana core
action. The distinguished four generators are derived as
`{Id, ε, J, J∘ε}`.
-/
structure Atom where
  core : RealMajoranaCore

instance : CoeSort Atom (Type u) := ⟨fun X => X.core⟩

namespace Atom

/-- The four distinguished generators of the split-Clifford atom. -/
def oneOp (X : Atom) : X →ₗ[ℝ] X := LinearMap.id

def epsOp (X : Atom) : X →ₗ[ℝ] X := X.core.eps

def jOp (X : Atom) : X →ₗ[ℝ] X := X.core.J

noncomputable def kOp (X : Atom) : X →ₗ[ℝ] X :=
  X.core.K

@[simp] lemma j_sq (X : Atom) :
    (jOp X).comp (jOp X) = (oneOp X) := by
  simpa [jOp, oneOp] using X.core.J_sq

@[simp] lemma eps_sq (X : Atom) :
    (epsOp X).comp (epsOp X) = (oneOp X) := by
  simpa [epsOp, oneOp] using X.core.eps_sq

@[simp] lemma j_eps_anticomm (X : Atom) :
    (jOp X).comp (epsOp X) = -((epsOp X).comp (jOp X)) := by
  simpa [jOp, epsOp] using X.core.J_eps_anticomm

@[simp] lemma k_eq_j_comp_eps (X : Atom) :
    kOp X = (jOp X).comp (epsOp X) := by
  rfl

@[simp] lemma k_sq (X : Atom) :
    (kOp X).comp (kOp X) = -(oneOp X) := by
  simpa [kOp, oneOp] using X.core.K_sq

/-- Equivariant atom morphisms are core-equivariant maps. -/
@[ext] structure Hom (X Y : Atom) where
  homCore : X.core ⟶ Y.core

instance (X Y : Atom) : CoeFun (Hom X Y) (fun _ => X → Y) := ⟨fun f => f.homCore.hom⟩

lemma Hom.comm_j {X Y : Atom} (f : Hom X Y) :
    f.homCore.hom.comp (jOp X) = (jOp Y).comp f.homCore.hom := by
  simpa [jOp] using f.homCore.comm_J

lemma Hom.comm_eps {X Y : Atom} (f : Hom X Y) :
    f.homCore.hom.comp (epsOp X) = (epsOp Y).comp f.homCore.hom := by
  simpa [epsOp] using f.homCore.comm_eps

lemma Hom.comm_k {X Y : Atom} (f : Hom X Y) :
    f.homCore.hom.comp (kOp X) = (kOp Y).comp f.homCore.hom := by
  simpa [kOp] using f.homCore.comm_K

noncomputable instance : Category Atom where
  Hom X Y := Hom X Y
  id X := { homCore := 𝟙 X.core }
  comp {X Y Z} f g := { homCore := f.homCore ≫ g.homCore }

@[simp] lemma hom_id (X : Atom) : ((𝟙 X : X ⟶ X).homCore.hom) = LinearMap.id := rfl

@[simp] lemma hom_comp {X Y Z : Atom} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).homCore.hom) = g.homCore.hom.comp f.homCore.hom := rfl

/-- Forget the atom wrapper and keep the primitive Majorana core. -/
noncomputable def forgetToCore : Atom ⥤ RealMajoranaCore where
  obj X := X.core
  map {X Y} f := f.homCore
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Wrap every Majorana core as an atom. -/
noncomputable def fromCore : RealMajoranaCore ⥤ Atom where
  obj X := ⟨X⟩
  map {X Y} f := ⟨f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Atom/core equivalence: same data, explicit atomic packaging. -/
noncomputable def atomEquivCore : Atom ≌ RealMajoranaCore where
  functor := forgetToCore
  inverse := fromCore
  unitIso := NatIso.ofComponents
    (fun X =>
      { hom := ⟨𝟙 X.core⟩
        inv := ⟨𝟙 X.core⟩
        hom_inv_id := by
          apply Hom.ext
          rfl
        inv_hom_id := by
          apply Hom.ext
          rfl })
    (by
      intro X Y f
      apply Hom.ext
      rfl)
  counitIso := NatIso.ofComponents
    (fun X =>
      { hom := 𝟙 X
        inv := 𝟙 X })
    (by
      intro X Y f
      rfl)
  functor_unitIso_comp := by
    intro X
    rfl

/-- Forget atom structure down to the real `K`-vector layer. -/
noncomputable def toRealKVect : Atom ⥤ RealKCategory :=
  forgetToCore ⋙ RealMajoranaCategory.RealMajoranaCore.toRealKVect

end Atom

end InfoGeometry.Quantum.SplitCliffordAtom
