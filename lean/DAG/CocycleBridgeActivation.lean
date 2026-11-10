/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import DAG.CocycleBridge
import DAG.ChiralDiracAnticommutation
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Fibonacci.HexagonCocycle

/-!
# Cocycle Bridge Activation — Typed DAG and Operator-Cocycle Components

Exposes three independently owned layers:

```
Layer 1 (discrete)    Layer 2 (algebraic limit)    Layer 3 (Hilbert flow)
DAG.TwoComplex    |   SplitCliffordDirectLimit   |   AdditiveModularFlow
  Hodge data          Cl(n,n) → DirectLimit         exp(tK)
```

This module exposes independently typed DAG, algebraic direct-limit,
Hilbert-space modular-flow, and braided-category components.  It does not
construct maps connecting those components, nor an analytic completion or a
Connes cocycle on the split-Clifford direct limit.
-/

namespace DAG.CocycleBridgeActivation

universe v u

open DAG
open DAG.CocycleBridge
open CategoryTheory
open CategoryTheory.MonoidalCategory
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge
open InfoGeometry.CliffordTower
open InfoGeometry.Volume.ConnesCocycle

/--
The currently implemented data record for this bridge stores only the DAG
Hodge readout.  The split-Clifford direct limit and the generic Hilbert-space
modular flow are exposed separately below; no lift of the DAG incidence maps,
boundary states, or Connes cocycle to that direct limit is defined here.
-/
structure CocycleBridge (α : Type) [BEq α] [Hashable α] where
  /-- Layer 1: discrete Hodge data from the DAG TwoComplex -/
  hodge : HodgeCocycleData α

/-! The remaining layers are direct owner definitions rather than textual
metadata fields. -/

noncomputable def analyticBridge (n : ℕ) :
    SplitClNNAlg n →ₐ[ℝ] SplitClNNAlg (n + 1) :=
  splitCliffordStep n

theorem analyticBridge_injective (n : ℕ) :
    Function.Injective (analyticBridge n) :=
  splitCliffordStep_injective n

noncomputable def connesCocycle {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : AlgebraEnd H) : AdditiveModularFlow (H := H) :=
  additiveModularFlowOfGenerator K

theorem connesCocycle_map_add {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : AlgebraEnd H) (s t : ℝ) :
    connesCocycle K (s + t) = connesCocycle K s * connesCocycle K t :=
  AdditiveModularFlow.map_add (connesCocycle K) s t

theorem hexagonCocycle {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.MonoidalCategory C] [CategoryTheory.BraidedCategory C]
    (X Y Z : C) :
    α_ X Y Z ≪≫ β_ X (Y ⊗ Z) ≪≫ α_ Y Z X =
      whiskerRightIso (β_ X Y) Z ≪≫ α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z) := by
  exact InfoGeometry.Fibonacci.HexagonCocycle.hexagon_as_cocycle X Y Z

theorem hexagonCocycle_yangBaxter {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.MonoidalCategory C] [CategoryTheory.BraidedCategory C]
    (X Y Z : C) :
    (α_ X Y Z).symm ≪≫
        whiskerRightIso (β_ X Y) Z ≪≫
          α_ Y X Z ≪≫ whiskerLeftIso Y (β_ X Z) ≪≫
            (α_ Y Z X).symm ≪≫ whiskerRightIso (β_ Y Z) X ≪≫ α_ Z Y X =
      whiskerLeftIso X (β_ Y Z) ≪≫
        (α_ X Z Y).symm ≪≫ whiskerRightIso (β_ X Z) Y ≪≫
          α_ Z X Y ≪≫ whiskerLeftIso Z (β_ X Y) := by
  exact InfoGeometry.Fibonacci.HexagonCocycle.braid_relation_from_hexagon X Y Z

/--
Construct the implemented Hodge-data record from a TwoComplex.  This does not
construct a functor to the split-Clifford direct limit or to a Kasparov cycle.
-/
def fromTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) : CocycleBridge α :=
  { hodge := CocycleBridge.fromTwoComplex tc}

end DAG.CocycleBridgeActivation
