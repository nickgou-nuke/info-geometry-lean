import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularFlowTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Homeomorphic and categorical time slices of a symbolic-latent flow

The native zero and additive laws imply that the time-`t` action has inverse
the time-`(-t)` action.  This owner records that elementary consequence and
exposes it as a `TopCat` isomorphism.
-/

def SymbolicLatentModularFlow.actHomeomorph
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) : X ≃ₜ X where
  toFun := Φ.act t
  invFun := Φ.act (-t)
  left_inv := by
    intro x
    simpa [Φ.zero_apply] using (Φ.add_apply (-t) t x).symm
  right_inv := by
    intro x
    simpa [Φ.zero_apply] using (Φ.add_apply t (-t) x).symm
  continuous_toFun := Φ.continuous_act.comp
    (continuous_const.prodMk continuous_id)
  continuous_invFun := Φ.continuous_act.comp
    (continuous_const.prodMk continuous_id)

@[simp] theorem SymbolicLatentModularFlow.actHomeomorph_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    Φ.actHomeomorph t x = Φ.act t x :=
  rfl

theorem SymbolicLatentModularFlow.actHomeomorph_zero_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    Φ.actHomeomorph 0 x = x :=
  Φ.zero_apply x

theorem SymbolicLatentModularFlow.actHomeomorph_add_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) (x : X) :
    Φ.actHomeomorph (s + t) x =
      Φ.actHomeomorph s (Φ.actHomeomorph t x) :=
  Φ.add_apply s t x

theorem SymbolicLatentModularFlow.actHomeomorph_trans
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) :
    (Φ.actHomeomorph s).trans (Φ.actHomeomorph t) =
      Φ.actHomeomorph (t + s) := by
  ext x
  change Φ.act t (Φ.act s x) = Φ.act (t + s) x
  simpa using (Φ.add_apply t s x).symm

def SymbolicLatentModularFlow.actHomeomorphTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    TopCat.of X ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Φ.actHomeomorph t
      continuous_toFun := (Φ.actHomeomorph t).continuous_toFun }

def SymbolicLatentModularFlow.actHomeomorphInverseTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    TopCat.of X ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := (Φ.actHomeomorph t).symm
      continuous_toFun := (Φ.actHomeomorph t).symm.continuous_toFun }

@[simp] theorem SymbolicLatentModularFlow.actHomeomorphInverseTopCatHom_eq
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    Φ.actHomeomorphInverseTopCatHom t = Φ.actHomeomorphTopCatHom (-t) := by
  ext x
  rfl

@[simp] theorem SymbolicLatentModularFlow.actHomeomorphInverseTopCatHom_zero
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) :
    Φ.actHomeomorphInverseTopCatHom 0 = 𝟙 _ := by
  have h0 : Φ.actHomeomorph 0 = Homeomorph.refl X := by
    ext x
    simpa using Φ.actHomeomorph_zero_apply x
  ext x
  simp [SymbolicLatentModularFlow.actHomeomorphInverseTopCatHom, h0]

theorem SymbolicLatentModularFlow.actHomeomorphTopCatHom_isIso
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    IsIso (Φ.actHomeomorphTopCatHom t) := by
  refine IsIso.mk ⟨Φ.actHomeomorphInverseTopCatHom t, ?_, ?_⟩
  · apply TopCat.hom_ext
    ext x
    change (Φ.actHomeomorph t).symm (Φ.actHomeomorph t x) = x
    exact (Φ.actHomeomorph t).symm_apply_apply x
  · apply TopCat.hom_ext
    ext x
    change (Φ.actHomeomorph t) ((Φ.actHomeomorph t).symm x) = x
    exact (Φ.actHomeomorph t).apply_symm_apply x

theorem SymbolicLatentModularFlow.actHomeomorphTopCatHom_comp_inv
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    Φ.actHomeomorphTopCatHom t ≫ Φ.actHomeomorphInverseTopCatHom t =
      𝟙 (TopCat.of X) := by
  ext x
  change Φ.act (-t) (Φ.act t x) = x
  simpa [Φ.zero_apply] using (Φ.add_apply (-t) t x).symm

theorem SymbolicLatentModularFlow.actHomeomorphInverseTopCatHom_comp
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    Φ.actHomeomorphInverseTopCatHom t ≫ Φ.actHomeomorphTopCatHom t =
      𝟙 (TopCat.of X) := by
  ext x
  change Φ.act t (Φ.act (-t) x) = x
  simpa [Φ.zero_apply] using (Φ.add_apply t (-t) x).symm

theorem SymbolicLatentModularFlow.actHomeomorphTopCatHom_comp
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) :
    Φ.actHomeomorphTopCatHom t ≫ Φ.actHomeomorphTopCatHom s =
      Φ.actHomeomorphTopCatHom (t + s) := by
  ext x
  change Φ.actHomeomorph s (Φ.actHomeomorph t x) = Φ.actHomeomorph (t + s) x
  simpa [SymbolicLatentModularFlow.actHomeomorph_apply, add_comm] using
    (Φ.add_apply s t x).symm

@[simp] theorem SymbolicLatentModularFlow.actHomeomorphTopCatHom_comp_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) (x : X) :
    (Φ.actHomeomorphTopCatHom t ≫ Φ.actHomeomorphTopCatHom s) x =
      Φ.actHomeomorphTopCatHom (t + s) x := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun f => f x) (Φ.actHomeomorphTopCatHom_comp s t)

theorem SymbolicLatentModularFlow.actHomeomorphTopCatHom_zero
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) :
    Φ.actHomeomorphTopCatHom 0 = 𝟙 _ := by
  ext x
  change Φ.actHomeomorph 0 x = x
  simpa using Φ.zero_apply x

theorem SymbolicLatentModularFlow.actTopCatHom_isIso
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    IsIso (Φ.actTopCatHom t) := by
  refine (TopCat.isIso_iff_isHomeomorph (Φ.actTopCatHom t)).2 ?_
  change IsHomeomorph (Φ.act t)
  exact (Φ.actHomeomorph t).isHomeomorph

theorem SymbolicLatentModularFlow.actTopCatHom_comp
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) :
    Φ.actTopCatHom t ≫ Φ.actTopCatHom s =
      Φ.actTopCatHom (t + s) := by
  ext x
  change Φ.act s (Φ.act t x) = Φ.act (t + s) x
  simpa [SymbolicLatentModularFlow.actHomeomorph_apply, add_comm] using
    (Φ.add_apply s t x).symm

end InfoGeometry.Topology
