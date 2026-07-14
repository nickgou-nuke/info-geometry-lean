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
import InfoGeometry.Categorical.ZornBraidColimit
import InfoGeometry.Canonical.BostConnesKMS

/-!
# Zorn Braid Colimit KMS State

This module constructs the formal mathematical structures that connect the
`continuumCuntzGenerator` from the Zorn limit boundary directly to the
`KMSProjectionState` defined in `InfoGeometry.Canonical.BostConnesKMS`.

## BUCKET 1: CLOSED FINITE THEOREMS
* `evaluate_continuum_boltzmann_weight`: Shows how the Boltzmann weights
  evaluate on the macroscopic continuum generators.
* `evaluate_continuum_boltzmann_weight_off_diag`: Off-diagonal elements
  vanish.

## BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
* `ZornBraidKMSState`: The core structural bridge connecting the
  infinite-dimensional categorical colimit of the Zorn braid sequence
  to the Bost--Connes KMS readout.

## BUCKET 3: OPEN CLOSURE DEBT
* Construct a strict non-associative C*-algebra structure on the colimit.
* Formally connect the indexing mapping `stageIndex` to the physical degrees
  of freedom of the finite Zorn representations.
-/

namespace InfoGeometry.Categorical.ZornBraidColimitKMS

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Categorical.ZornBraidColimit
open InfoGeometry.Canonical.BostConnesKMS

universe u

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : BostConnesCuntzSystem Op)
variable {R : Type u} [CommRing R] {J : Type u} [Category.{u} J]
variable (ZornSequence : J ⥤ ModuleCat.{u} R)
variable [HasColimit ZornSequence]
variable (M : CompatibleBilinearMultiplication R ZornSequence)
variable (zornCuntzGenerator : ∀ j, ZornSequence.obj j)

/--
The bridge state connecting the Zorn braid colimit continuum to the 
Bost--Connes KMS thermodynamic state.

This structure assumes an assignment of positive integers to the categorical 
stages and an involution operation on the continuum. It mandates that the 
macroscopic Zorn state evaluates inner products of the continuum Cuntz 
generators identically to the Bost--Connes KMS projection weights.
-/
structure ZornBraidKMSState where
  /-- The Bost--Connes KMS state providing the thermodynamic parameters. -/
  bcKMS : KMSProjectionState C
  
  /-- A macro-state functional on the Zorn continuum. -/
  zornState : ↑(zornContinuumModule R ZornSequence) → ℝ
  
  /-- The index mapping from the Zorn braid stages to the Bost--Connes natural numbers. -/
  stageIndex : J → ℕ+
  
  /-- An involution operation on the macroscopic continuum. -/
  continuumStar : ↑(zornContinuumModule R ZornSequence) → ↑(zornContinuumModule R ZornSequence)
  
  /-- 
  The fundamental bridge: the Zorn macroscopic continuum generators, when projected,
  evaluate exactly to the Bost-Connes KMS Boltzmann weights.
  -/
  eval_continuum_cuntz : ∀ (j k : J),
    zornState (M.colimitMul
      (continuumCuntzGenerator R ZornSequence zornCuntzGenerator j)
      (continuumStar (continuumCuntzGenerator R ZornSequence zornCuntzGenerator k))) =
    kmsProjectionReadout bcKMS.β bcKMS.ζβ (stageIndex j) (stageIndex k)

namespace ZornBraidKMSState

variable {C} {ZornSequence} {M} {zornCuntzGenerator}
variable (state : ZornBraidKMSState C ZornSequence M zornCuntzGenerator)

/--
The Boltzmann weights evaluate on the diagonal macroscopic continuum generators
as $n^{-β} / ζβ$, where $n$ is the positive integer mapped from the stage $j$.
-/
theorem evaluate_continuum_boltzmann_weight (j : J) :
    state.zornState (M.colimitMul
      (continuumCuntzGenerator R ZornSequence zornCuntzGenerator j)
      (state.continuumStar (continuumCuntzGenerator R ZornSequence zornCuntzGenerator j))) =
    ((state.stageIndex j : ℕ) : ℝ) ^ (-state.bcKMS.β) / state.bcKMS.ζβ := by
  rw [state.eval_continuum_cuntz j j]
  exact kmsProjectionReadout_self state.bcKMS.β state.bcKMS.ζβ (state.stageIndex j)

/--
Off-diagonal macroscopic continuum generators evaluate to zero under the state,
reflecting the orthogonality of the Bost--Connes Cuntz generators.
-/
theorem evaluate_continuum_boltzmann_weight_off_diag {j k : J} (h : state.stageIndex j ≠ state.stageIndex k) :
    state.zornState (M.colimitMul
      (continuumCuntzGenerator R ZornSequence zornCuntzGenerator j)
      (state.continuumStar (continuumCuntzGenerator R ZornSequence zornCuntzGenerator k))) = 0 := by
  rw [state.eval_continuum_cuntz j k]
  exact kmsProjectionReadout_ne h

end ZornBraidKMSState

end InfoGeometry.Categorical.ZornBraidColimitKMS
