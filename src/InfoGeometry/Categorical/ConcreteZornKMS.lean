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
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import Mathlib.CategoryTheory.Limits.HasLimits
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Algebra.Category.ModuleCat.Basic
import InfoGeometry.Categorical.ConcreteZornTower
import InfoGeometry.Categorical.ZornBraidColimitKMS
import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Canonical.ZornSpinor

/-!
# Concrete Zorn KMS State

This file instantiates `ZornBraidKMSState` over the `concreteZornSequence`.
-/

namespace InfoGeometry.Categorical.ConcreteZornKMS

open CategoryTheory
open CategoryTheory.Limits
open ZornBraidColimit
open ConcreteZornTower
open ZornBraidColimitKMS
open InfoGeometry.Canonical
open BostConnesKMS

/--
A linear map swapping `a` and `b`, and negating `x` and `y`.
-/
noncomputable def zornConjugateLinear : ZornMatrix ℚ →ₗ[ℚ] ZornMatrix ℚ where
  toFun z := { a := z.b, b := z.a, x := -z.x, y := -z.y }
  map_add' x y := by
    ext <;> simp [ZornMatrix.add_def] <;> ring
  map_smul' m x := by
    ext <;> simp

/--
The lifting of this conjugation to the colimit.
-/
noncomputable def continuumStar : 
    ↑(zornContinuumModule ℚ concreteZornSequence) → ↑(zornContinuumModule ℚ concreteZornSequence) :=
  fun c => invToColimit (zornConjugateLinear (homToZorn c))

/--
A mapping from `ℕ` to `ℕ+`.
-/
def stageIndex : ℕ → ℕ+ :=
  fun n => ⟨n + 1, Nat.succ_pos n⟩

/--
A macroscopic state functional.
-/
noncomputable def zornState : ↑(zornContinuumModule ℚ concreteZornSequence) → ℝ :=
  fun c => ((homToZorn c).a : ℝ)

/--
The instance of `ZornBraidKMSState` over `concreteZornSequence`.
-/
noncomputable def concreteZornBraidKMSState {Op : Type*} [Ring Op] [StarRing Op]
    (C : BostConnesCuntzSystem Op)
    (bcKMS : KMSProjectionState C) :
    ZornBraidKMSState C concreteZornSequence :=
  let result := Prod.mk bcKMS (Prod.mk zornState (Prod.mk stageIndex continuumStar))
  show KMSProjectionState C ×
      ((↑(zornContinuumModule ℚ concreteZornSequence) → ℝ) ×
        ((ℕ → ℕ+) ×
          (↑(zornContinuumModule ℚ concreteZornSequence) →
            ↑(zornContinuumModule ℚ concreteZornSequence))))
    from result

end InfoGeometry.Categorical.ConcreteZornKMS
