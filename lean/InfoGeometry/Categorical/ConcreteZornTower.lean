/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import InfoGeometry.Categorical.ZornBraidColimit
import InfoGeometry.Canonical.ZornSpinor

/-!
# Concrete Zorn Tower and Multiplication Witness

This file instantiates the categorical `CompatibleBilinearMultiplication` witness
for the concrete sequence of `ZornMatrix ℚ` spaces.
-/

namespace InfoGeometry.Categorical.ConcreteZornTower

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Categorical.ZornBraidColimit
open InfoGeometry.Canonical

/--
The concrete filtered diagram of finite Zorn states.
Since all states are copies of `ZornMatrix ℚ` and inclusions are trivial,
we define it as a constant functor over `ℕ`.
-/
noncomputable def concreteZornSequence : ℕ ⥤ ModuleCat.{0} ℚ where
  obj _ := ModuleCat.of ℚ (ZornMatrix ℚ)
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := (Category.id_comp _).symm

/--
The canonical trivial cocone for the constant Zorn sequence.
-/
noncomputable def zornCocone : Cocone concreteZornSequence where
  pt := ModuleCat.of ℚ (ZornMatrix ℚ)
  ι := {
    app := fun _ => 𝟙 _
    naturality := fun _ _ _ => rfl
  }

/--
The colimit of `concreteZornSequence` is isomorphic to `ZornMatrix ℚ`.
-/
noncomputable def colimitIsoZorn : colimit concreteZornSequence ≅ ModuleCat.of ℚ (ZornMatrix ℚ) :=
  colimit.isoColimitCocone {
    cocone := zornCocone
    isColimit := {
      desc := fun s => s.ι.app 0
      fac := fun s j => by
        have h := s.ι.naturality (homOfLE (Nat.zero_le j))
        dsimp [concreteZornSequence] at h
        rw [Category.id_comp] at h
        exact h.symm
      uniq := fun s m hm => by
        have h0 := hm 0
        exact h0
    }
  }

@[simp] theorem smul_a (r : ℚ) (z : ZornMatrix ℚ) : (r • z).a = r * z.a := rfl
@[simp] theorem smul_b (r : ℚ) (z : ZornMatrix ℚ) : (r • z).b = r * z.b := rfl
@[simp] theorem smul_x (r : ℚ) (z : ZornMatrix ℚ) : (r • z).x = r • z.x := rfl
@[simp] theorem smul_y (r : ℚ) (z : ZornMatrix ℚ) : (r • z).y = r • z.y := rfl

/--
The concrete bilinear multiplication on the finite stage `ZornMatrix ℚ`.
-/
noncomputable def concreteStageMul : 
    ZornMatrix ℚ →ₗ[ℚ] ZornMatrix ℚ →ₗ[ℚ] ZornMatrix ℚ :=
  LinearMap.mk₂ ℚ ZornMatrix.mul 
    (fun x y z => by
      rcases x with ⟨xa, xb, xx, xy⟩
      rcases y with ⟨ya, yb, yx, yy⟩
      rcases z with ⟨za, zb, zx, zy⟩
      ext1
      · dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.add_def]; ring
      · dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.add_def]; ring
      · ext1 i; fin_cases i <;> dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.add_def, ZornMatrix.cross, Pi.add_apply] <;> ring
      · ext1 i; fin_cases i <;> dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.add_def, ZornMatrix.cross, Pi.add_apply] <;> ring)
    (fun r x y => by
      rcases x with ⟨xa, xb, xx, xy⟩
      rcases y with ⟨ya, yb, yx, yy⟩
      ext1
      · dsimp [ZornMatrix.mul, ZornMatrix.dot]; ring
      · dsimp [ZornMatrix.mul, ZornMatrix.dot]; ring
      · ext1 i; fin_cases i <;> dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.smul_apply] <;> ring
      · ext1 i; fin_cases i <;> dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.smul_apply] <;> ring)
    (fun x y z => by
      rcases x with ⟨xa, xb, xx, xy⟩
      rcases y with ⟨ya, yb, yx, yy⟩
      rcases z with ⟨za, zb, zx, zy⟩
      ext1
      · dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.add_def]; ring
      · dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.add_def]; ring
      · ext1 i; fin_cases i <;> dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.add_def, ZornMatrix.cross, Pi.add_apply] <;> ring
      · ext1 i; fin_cases i <;> dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.add_def, ZornMatrix.cross, Pi.add_apply] <;> ring)
    (fun r x y => by
      rcases x with ⟨xa, xb, xx, xy⟩
      rcases y with ⟨ya, yb, yx, yy⟩
      ext1
      · dsimp [ZornMatrix.mul, ZornMatrix.dot]; ring
      · dsimp [ZornMatrix.mul, ZornMatrix.dot]; ring
      · ext1 i; fin_cases i <;> dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.smul_apply] <;> ring
      · ext1 i; fin_cases i <;> dsimp [ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.smul_apply] <;> ring)

noncomputable def homToZorn : ↑(colimit concreteZornSequence) →ₗ[ℚ] ZornMatrix ℚ :=
  ModuleCat.Hom.hom colimitIsoZorn.hom

noncomputable def invToColimit : ZornMatrix ℚ →ₗ[ℚ] ↑(colimit concreteZornSequence) :=
  ModuleCat.Hom.hom colimitIsoZorn.inv

/--
The descended bilinear multiplication on the continuum limit.
-/
noncomputable def concreteColimitMul : 
    ↑(colimit concreteZornSequence) →ₗ[ℚ] ↑(colimit concreteZornSequence) →ₗ[ℚ] ↑(colimit concreteZornSequence) :=
  LinearMap.mk₂ ℚ 
    (fun x y => invToColimit (concreteStageMul (homToZorn x) (homToZorn y)))
    (fun _ _ _ => by simp only [map_add, LinearMap.add_apply])
    (fun _ _ _ => by simp only [map_smul, LinearMap.smul_apply])
    (fun _ _ _ => by simp only [map_add])
    (fun _ _ _ => by simp only [map_smul])

theorem colimitIsoZorn_inv_eq_ι (j : ℕ) :
    colimitIsoZorn.inv = colimit.ι concreteZornSequence j := by
  have h := (colimit.cocone concreteZornSequence).ι.naturality (homOfLE (Nat.zero_le j))
  dsimp [concreteZornSequence] at h
  rw [Category.comp_id] at h
  exact h.symm

/--
The `CompatibleBilinearMultiplication` witness for the concrete Zorn tower,
fulfilling the categorical consistency constraint for multiplication descent.
-/
noncomputable def concreteZornBilinearMultiplication : 
    CompatibleBilinearMultiplication ℚ concreteZornSequence where
  stageMul _ := concreteStageMul
  colimitMul := concreteColimitMul
  colimitMul_ι_ι j x y := by
    dsimp [concreteColimitMul]
    have h1 : homToZorn (invToColimit x) = x := by
      have hc : homToZorn (invToColimit x) = (ModuleCat.Hom.hom (colimitIsoZorn.inv ≫ colimitIsoZorn.hom)) x := rfl
      rw [hc, colimitIsoZorn.inv_hom_id]
      rfl
    have h2 : homToZorn (invToColimit y) = y := by
      have hc : homToZorn (invToColimit y) = (ModuleCat.Hom.hom (colimitIsoZorn.inv ≫ colimitIsoZorn.hom)) y := rfl
      rw [hc, colimitIsoZorn.inv_hom_id]
      rfl
    rw [← colimitIsoZorn_inv_eq_ι j]
    change invToColimit (concreteStageMul (homToZorn (invToColimit x)) (homToZorn (invToColimit y))) = invToColimit (concreteStageMul x y)
    rw [h1, h2]

end InfoGeometry.Categorical.ConcreteZornTower
