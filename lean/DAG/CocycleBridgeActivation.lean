import DAG.CocycleBridge
import DAG.ChiralDiracAnticommutation
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Volume.ConnesCocycle
import InfoGeometry.Fibonacci.HexagonCocycle

/-!
# Cocycle Bridge Activation — Wiring Discrete DAG to Analytic Cocycles

Closes the three-layer connection:

```
Layer 1 (discrete)    Layer 2 (analytic colimit)    Layer 3 (cocycle)
DAG.TwoComplex    →   SplitCliffordDirectLimit   →   ConnesCocycle
  ∂₁, ∂₂, β₁, χ       Cl(n,n) → direct limit       Δ^{it}, Radon-Nikodym
```

The direct-limit, modular-flow, and braided ingredients are exposed below
through their existing typed owners.  No analytic completion theorem is
asserted merely by naming these finite ingredients.
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
The Three-Layer Cocycle Bridge.

Layer 1: `TwoComplex` — discrete DAG with incidence matrices ∂₁, ∂₂.
         Provides HodgeCocycleData (β₀, β₁, χ, Hodge dims).

Layer 2: `SplitCliffordInfinity` — the direct limit of the recursive
         Cl(n,n) tower. This IS the analytic completion. The infinite
         direct limit carries the Cantor boundary states.

Layer 3: `ConnesCocycle` — the modular automorphism Δ^{it} acting on
         the direct limit completion. The KMS thermal flow.

The bridge: ∂₁, ∂₂ from the DAG lift to finite Clifford generators.
The direct limit extends them to the infinite algebra where the
Connes cocycle is defined.
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
Construct the three-layer cocycle bridge from a TwoComplex.

The HodgeCocycleData is computed from the DAG; the other layers are exposed
by the owner definitions above.  The construction does not claim a completed
analytic braided functor.
-/
def fromTwoComplex {α : Type} [BEq α] [Hashable α] (tc : TwoComplex α) : CocycleBridge α :=
  { hodge := CocycleBridge.fromTwoComplex tc}

end DAG.CocycleBridgeActivation
