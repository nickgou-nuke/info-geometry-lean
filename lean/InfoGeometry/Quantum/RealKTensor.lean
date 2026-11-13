/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RealKCategory
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor products balanced by an internal complex structure

The existing `RealKVect` owner derives complex scalar multiplication from a
real-linear operator `K` with `K² = -id`. This file transports Mathlib's module
tensor product through that existing construction. Its carrier is again a real
space with an internal complex structure. The pure tensor is real bilinear and
obeys the additional relation `(K x) ⊗ y = x ⊗ (K y)`.

The construction applies to arbitrary `RealKVect` objects, without finite
dimension assumptions. Tensoring intertwining maps preserves identities and
composition. No monoidal-category instance or Hilbert-space completion is
claimed here.

This is the balanced composition needed by the realification construction in
Hoffreumon--Woods, arXiv:2504.02808v2, Section III and Supplementary B. It is not
the ordinary real tensor product of the two underlying real vector spaces.
-/

open CategoryTheory
open scoped TensorProduct

universe u

namespace InfoGeometry.Quantum.RealKCategory.RealKVect

namespace RealKTensor

attribute [local instance] complexModule

/-- Native tensor product of the complex actions already derived from `K`. -/
noncomputable def complexTensor (X Y : RealKVect.{u}) : ModuleCat ℂ :=
  ModuleCat.of ℂ (asComplexModule X ⊗[ℂ] asComplexModule Y)

/-- The balanced tensor object, returned to real spaces with internal `K`. -/
noncomputable def obj (X Y : RealKVect.{u}) : RealKVect.{u} :=
  complexToRealK.obj (complexTensor X Y)

/-- Pure tensor in the balanced tensor object. -/
noncomputable def tmul (X Y : RealKVect.{u}) (x : X) (y : Y) : obj X Y :=
  (x : asComplexModule X) ⊗ₜ[ℂ] (y : asComplexModule Y)

/-- The derived complex action restricts to the original real action. -/
theorem ofReal_smul (X : RealKVect.{u}) (r : ℝ) (x : X) :
    ((r : ℂ) • (x : asComplexModule X) : asComplexModule X) = r • x := by
  change complexSMul X (r : ℂ) x = r • x
  simp [complexSMul]

/-- The derived imaginary action is the existing internal operator. -/
theorem I_smul (X : RealKVect.{u}) (x : X) :
    ((Complex.I : ℂ) • (x : asComplexModule X) : asComplexModule X) = X.K x :=
  complexI_smul_eq_K X x

theorem tmul_add_left (X Y : RealKVect.{u}) (x x' : X) (y : Y) :
    tmul X Y (x + x') y = tmul X Y x y + tmul X Y x' y :=
  TensorProduct.add_tmul (x : asComplexModule X) (x' : asComplexModule X)
    (y : asComplexModule Y)

theorem tmul_add_right (X Y : RealKVect.{u}) (x : X) (y y' : Y) :
    tmul X Y x (y + y') = tmul X Y x y + tmul X Y x y' :=
  TensorProduct.tmul_add (x : asComplexModule X) (y : asComplexModule Y)
    (y' : asComplexModule Y)

theorem tmul_smul_left (X Y : RealKVect.{u}) (r : ℝ) (x : X) (y : Y) :
    tmul X Y (r • x) y = r • tmul X Y x y := by
  change (r • x : asComplexModule X) ⊗ₜ[ℂ] (y : asComplexModule Y) =
    (r : ℂ) • ((x : asComplexModule X) ⊗ₜ[ℂ] (y : asComplexModule Y))
  rw [← ofReal_smul X r x]
  exact (TensorProduct.smul_tmul' (r : ℂ) (x : asComplexModule X)
    (y : asComplexModule Y)).symm

theorem tmul_smul_right (X Y : RealKVect.{u}) (r : ℝ) (x : X) (y : Y) :
    tmul X Y x (r • y) = r • tmul X Y x y := by
  change (x : asComplexModule X) ⊗ₜ[ℂ] (r • y : asComplexModule Y) =
    (r : ℂ) • ((x : asComplexModule X) ⊗ₜ[ℂ] (y : asComplexModule Y))
  rw [← ofReal_smul Y r y]
  exact TensorProduct.tmul_smul (r : ℂ) (x : asComplexModule X)
    (y : asComplexModule Y)

/-- The pure tensor packaged as a real bilinear map on the original carriers. -/
noncomputable def bilinear (X Y : RealKVect.{u}) : X →ₗ[ℝ] Y →ₗ[ℝ] obj X Y :=
  LinearMap.mk₂ ℝ (tmul X Y)
    (tmul_add_left X Y) (tmul_smul_left X Y)
    (tmul_add_right X Y) (tmul_smul_right X Y)

@[simp] theorem bilinear_apply (X Y : RealKVect.{u}) (x : X) (y : Y) :
    bilinear X Y x y = tmul X Y x y := rfl

/-- The composite internal complex structure can act in the first factor. -/
theorem K_tmul_left (X Y : RealKVect.{u}) (x : X) (y : Y) :
    (obj X Y).K (tmul X Y x y) = tmul X Y (X.K x) y := by
  change (Complex.I : ℂ) •
      ((x : asComplexModule X) ⊗ₜ[ℂ] (y : asComplexModule Y)) =
    (X.K x : asComplexModule X) ⊗ₜ[ℂ] (y : asComplexModule Y)
  rw [TensorProduct.smul_tmul', I_smul]

/-- The same internal complex structure can act in the second factor. -/
theorem K_tmul_right (X Y : RealKVect.{u}) (x : X) (y : Y) :
    (obj X Y).K (tmul X Y x y) = tmul X Y x (Y.K y) := by
  change (Complex.I : ℂ) •
      ((x : asComplexModule X) ⊗ₜ[ℂ] (y : asComplexModule Y)) =
    (x : asComplexModule X) ⊗ₜ[ℂ] (Y.K y : asComplexModule Y)
  rw [← TensorProduct.tmul_smul, I_smul]

/-- The extra balance relation identifying the two local internal phases. -/
theorem K_balance (X Y : RealKVect.{u}) (x : X) (y : Y) :
    tmul X Y (X.K x) y = tmul X Y x (Y.K y) :=
  (K_tmul_left X Y x y).symm.trans (K_tmul_right X Y x y)

/-- Morphisms from the tensor object are determined by pure tensors. -/
theorem hom_ext {X Y Z : RealKVect.{u}} {f g : obj X Y ⟶ Z}
    (h : ∀ (x : X) (y : Y), f.hom (tmul X Y x y) = g.hom (tmul X Y x y)) :
    f = g := by
  apply RealKVect.Hom.ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add t s ht hs =>
    exact (f.hom.map_add t s).trans
      ((congrArg₂ (· + ·) ht hs).trans (g.hom.map_add t s).symm)

/-- Tensor intertwining maps using Mathlib's tensor map construction. -/
noncomputable def map {X X' Y Y' : RealKVect.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    obj X Y ⟶ obj X' Y' :=
  complexToRealK.map (ModuleCat.ofHom
    (TensorProduct.map f.toComplexLinear.hom g.toComplexLinear.hom))

/-- Naturality on pure tensors is inherited from the native tensor map. -/
@[simp] theorem map_tmul {X X' Y Y' : RealKVect.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (x : X) (y : Y) :
    (map f g).hom (tmul X Y x y) = tmul X' Y' (f.hom x) (g.hom y) := rfl

@[simp] theorem map_id (X Y : RealKVect.{u}) :
    map (𝟙 X) (𝟙 Y) = 𝟙 (obj X Y) := by
  apply hom_ext
  intro x y
  rfl

/-- Tensor maps preserve the noncommutative order of composition in each factor. -/
theorem map_comp {X X' X'' Y Y' Y'' : RealKVect.{u}}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    map (f ≫ f') (g ≫ g') = map f g ≫ map f' g' := by
  apply hom_ext
  intro x y
  rfl

end RealKTensor

end InfoGeometry.Quantum.RealKCategory.RealKVect
