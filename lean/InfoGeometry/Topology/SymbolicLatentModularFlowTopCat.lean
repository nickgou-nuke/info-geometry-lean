import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularFlow
import InfoGeometry.Topology.SymbolicLatentInvolutionTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` readout of the native symbolic-latent flow

This is only the continuous action already present in the flow structure.  It
does not add a KMS state, a generator, or an operator-algebraic claim.
-/

def SymbolicLatentModularFlow.actTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    TopCat.of X ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := Φ.act t
      continuous_toFun := Φ.continuous_act.comp
        (continuous_const.prodMk continuous_id) }

def SymbolicLatentModularFlow.jointActTopCatHom
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) :
    TopCat.of (ℝ × X) ⟶ TopCat.of X :=
  TopCat.ofHom
    { toFun := fun p => Φ.act p.1 p.2
      continuous_toFun := Φ.continuous_act }

def SymbolicLatentModularFlow.timeSliceTopCatHom
    {X : Type} [TopologicalSpace X]
    (t : ℝ) :
    TopCat.of X ⟶ TopCat.of (ℝ × X) :=
  TopCat.ofHom
    { toFun := fun x => (t, x)
      continuous_toFun := continuous_const.prodMk continuous_id }

@[simp] theorem SymbolicLatentModularFlow.jointActTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (p : ℝ × X) :
    Φ.jointActTopCatHom p = Φ.act p.1 p.2 :=
  rfl

@[simp] theorem SymbolicLatentModularFlow.actTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    Φ.actTopCatHom t x = Φ.act t x :=
  rfl

theorem SymbolicLatentModularFlow.actTopCatHom_zero
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) :
    Φ.actTopCatHom 0 = 𝟙 (TopCat.of X) := by
  ext x
  exact Φ.zero_apply x

theorem SymbolicLatentModularFlow.timeSlice_jointAct_factorization
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    timeSliceTopCatHom t ≫ Φ.jointActTopCatHom =
      Φ.actTopCatHom t := by
  ext x
  rfl

theorem SymbolicLatentModularFlow.actTopCatHom_add
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) :
    Φ.actTopCatHom (s + t) =
      Φ.actTopCatHom s ≫ Φ.actTopCatHom t := by
  ext x
  have hst : s + t = t + s := add_comm s t
  rw [hst]
  simpa [SymbolicLatentModularFlow.actTopCatHom,
    CategoryTheory.comp_apply] using Φ.add_apply t s x

@[simp] theorem SymbolicLatentModularFlow.actTopCatHom_add_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (s t : ℝ) (x : X) :
    Φ.actTopCatHom (s + t) x =
      Φ.actTopCatHom t (Φ.actTopCatHom s x) := by
  simpa [SymbolicLatentModularFlow.actTopCatHom, CategoryTheory.comp_apply] using
    congrArg (fun f => f x) (Φ.actTopCatHom_add s t)

theorem SymbolicLatentModularFlow.actTopCatHom_neg_left
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    Φ.actTopCatHom (-t) ≫ Φ.actTopCatHom t = 𝟙 (TopCat.of X) := by
  ext x
  simpa [SymbolicLatentModularFlow.actTopCatHom,
    CategoryTheory.comp_apply, Φ.zero_apply] using
      (Φ.add_apply t (-t) x).symm

@[simp] theorem SymbolicLatentModularFlow.actTopCatHom_neg_left_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    Φ.actTopCatHom t (Φ.actTopCatHom (-t) x) = x := by
  simpa [SymbolicLatentModularFlow.actTopCatHom, CategoryTheory.comp_apply]
    using congrArg (fun f => f x) (Φ.actTopCatHom_neg_left t)

theorem SymbolicLatentModularFlow.actTopCatHom_neg_right
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) :
    Φ.actTopCatHom t ≫ Φ.actTopCatHom (-t) = 𝟙 (TopCat.of X) := by
  ext x
  simpa [SymbolicLatentModularFlow.actTopCatHom,
    CategoryTheory.comp_apply, Φ.zero_apply] using
      (Φ.add_apply (-t) t x).symm

@[simp] theorem SymbolicLatentModularFlow.actTopCatHom_neg_right_apply
    {X : Type} [TopologicalSpace X]
    (Φ : SymbolicLatentModularFlow X) (t : ℝ) (x : X) :
    Φ.actTopCatHom (-t) (Φ.actTopCatHom t x) = x := by
  simpa [SymbolicLatentModularFlow.actTopCatHom, CategoryTheory.comp_apply]
    using congrArg (fun f => f x) (Φ.actTopCatHom_neg_right t)

theorem SymbolicLatentModularReversal.actTopCatHom_natural
    {X : Type} [TopologicalSpace X]
    {Φ : SymbolicLatentModularFlow X}
    (R : SymbolicLatentModularReversal Φ) (t : ℝ) :
    R.involution.toTopCatHom ≫ Φ.actTopCatHom t =
      Φ.actTopCatHom (-t) ≫ R.involution.toTopCatHom := by
  ext x
  simpa [SymbolicLatentModularFlow.actTopCatHom,
    SymbolicLatentInvolution.toTopCatHom,
    CategoryTheory.comp_apply, neg_neg] using
    (R.reverses_flow (-t) x).symm

end InfoGeometry.Topology
