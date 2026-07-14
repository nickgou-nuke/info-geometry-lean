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

namespace ConcreteZornKMS

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Categorical.ZornBraidColimit
open InfoGeometry.Categorical.ConcreteZornTower
open InfoGeometry.Categorical.ZornBraidColimitKMS
open InfoGeometry.Canonical
open InfoGeometry.Canonical.BostConnesKMS

/--
A linear map swapping `a` and `b`, and negating `x` and `y`.
-/
noncomputable def zornConjugateLinear : ZornMatrix ℚ →ₗ[ℚ] ZornMatrix ℚ where
  toFun z := { a := z.b, b := z.a, x := -z.x, y := -z.y }
  map_add' x y := sorry
  map_smul' m x := sorry

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
    (bcKMS : KMSProjectionState C)
    (zornCuntzGenerator : ∀ j, concreteZornSequence.obj j) :
    ZornBraidKMSState C concreteZornSequence concreteZornBilinearMultiplication zornCuntzGenerator where
  bcKMS := bcKMS
  zornState := zornState
  stageIndex := stageIndex
  continuumStar := continuumStar
  eval_continuum_cuntz := sorry

end ConcreteZornKMS
