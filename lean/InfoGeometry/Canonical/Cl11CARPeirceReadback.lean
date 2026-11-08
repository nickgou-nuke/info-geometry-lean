/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealCARPeirceBridge
import InfoGeometry.Canonical.Cl11CARFockColimitBridge
import InfoGeometry.Canonical.Cl11PeirceWeightTrace

/-! Native Jordan--Wigner and algebraic-colimit CAR pairs discharge the
Peirce hypotheses. No analytic KMS or completion claim is made. -/
noncomputable section
namespace InfoGeometry.Canonical.Cl11CARPeirceReadback
open InfoGeometry.Clifford.Cl11TensorTower InfoGeometry.Clifford.Cl11TensorTowerLimit
open Cl11CARFockColimitBridge Cl11PeirceWeightTrace
open Cl11TensorInductiveLimitTopologicalTrace CliffordCARAlgebraicTopologicalComparison
open PeirceWeightedTrace PeirceHyperbolicOrbit

theorem last_site_weighted_boundary (k : ℕ) (a b : ℝ) (X : MatStage (k+1)) :
    let C := finiteLastCARPair k
    a * normalizedTraceTopologicalColimitMap (algebraicToTopological
      (supportWeight a b (ofStage (k+1) C.annihilation) (ofStage (k+1) C.creation) *
        ofStage (k+1) (C.annihilation*X))) =
    b * normalizedTraceTopologicalColimitMap (algebraicToTopological
      (supportWeight a b (ofStage (k+1) C.annihilation) (ofStage (k+1) C.creation) *
        ofStage (k+1) (X*C.annihilation))) := by
  dsimp only
  exact weighted_boundary_readback (k+1) a b _ _ X
    (finiteLastCARPair k).nilpotent_annihilation (finiteLastCARPair k).nilpotent_creation
    (finiteLastCARPair k).annihilation_reflexive (finiteLastCARPair k).creation_reflexive

theorem algebraic_hyperbolic_idempotent (k : ℕ) (u v : ℝ) (h : u*u-v*v=1) :
    IsIdempotentElem (hyperbolicPlus u v (algebraicCARPair k).annihilation
      (algebraicCARPair k).creation) := by
  exact hyperbolicPlus_idempotent
    (algebraicCARPair k).nilpotent_annihilation (algebraicCARPair k).nilpotent_creation
    (algebraicCARPair k).annihilation_reflexive (algebraicCARPair k).creation_reflexive u v h

end InfoGeometry.Canonical.Cl11CARPeirceReadback
