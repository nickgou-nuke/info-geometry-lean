/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.KreinPeirceTowerIntertwine
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity

/-!
# Peirce Tetraktys Colimit & StarOrderedRing Krein Positivity Bridge

Intertwines `InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity` (the
`Cl(1,1)^{\otimes n}` inductive colimit `Limit` and `genV_eq_conePlus_hodge_coefficient`)
with `InfoGeometry.Algebra.KreinPeirceTowerIntertwine` and
`InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge`:
1. `towerTrace_mul_star_self_nonneg` & `towerTrace_genV_nonneg`: in any
   `StarOrderedRing`, `0 ≤ towerTrace (genV P A (star A))` for any self-adjoint `P`
   in `ClTower B n`.
2. `ofStage_preserves_peirce_yang_mills`: `ofStage n : Stage n →+* Limit`
   preserves `peirce11`, `idempotencyDefect`, `peirceMaurerCartanCurvature`, and
   `peirceCovariantDeriv`.
-/

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.Algebra.NoncommutativeCliffordPrimitives
open InfoGeometry.Algebra.TwoSheetDiracMassEntropy
open InfoGeometry.Algebra.NoncommutativeKreinMathlibBridge
open InfoGeometry.Algebra.KreinPeirceTowerIntertwine
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Clifford.Cl11TensorTowerLimit

namespace InfoGeometry.Algebra.PeirceTetraktysKreinBridge

universe u

/-- In any `StarOrderedRing`, `0 ≤ towerTrace (A * star A)` at every depth `n : ℕ`. -/
theorem towerTrace_mul_star_self_nonneg
    {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
    [StarRing B] [StarOrderedRing B]
    {n : ℕ} (A : ClTower B n) :
    (0 : B) ≤ towerTrace (A * star A) := by
  have h : A * star A = star (star A) * star A := by rw [star_star]
  rw [h]
  exact towerTrace_star_mul_self_nonneg (star A)

/-- Combining `genV_eq_conePlus_hodge_coefficient` (`PeirceTetraktysColimitCoercivity`)
with `towerTrace_star_mul_self_nonneg` (`NoncommutativeKreinMathlibBridge`), the
Peirce Tetraktys quadratic coupling `genV P A (star A)` has non-negative `towerTrace`
for any self-adjoint `P` in `ClTower B n` over a `StarOrderedRing`. -/
theorem towerTrace_genV_nonneg
    {B : Type u} [Ring B] [PartialOrder B] [IsOrderedAddMonoid B]
    [StarRing B] [StarOrderedRing B]
    {n : ℕ} {P : ClTower B n} (hPs : star P = P) (A : ClTower B n) :
    (0 : B) ≤ towerTrace (n := n) (PeirceSpine.genV P A (star A)) := by
  rw [genV_eq_conePlus_hodge_coefficient hPs A, towerTrace_add]
  exact add_nonneg
    (towerTrace_mul_star_self_nonneg (PeirceSpine.conePlus P A))
    (towerTrace_star_mul_self_nonneg (PeirceSpine.conePlus P A))

/-- The canonical colimit inclusion `ofStage n : Stage n →+* Limit` from
`PeirceTetraktysColimitCoercivity` preserves `PeirceSpine.peirce11`,
`idempotencyDefect`, `peirceMaurerCartanCurvature`, and `peirceCovariantDeriv`. -/
theorem ofStage_preserves_peirce_yang_mills
    (n : ℕ) (P A C X : Stage n) :
    ofStage n (PeirceSpine.peirce11 P X) =
        PeirceSpine.peirce11 (ofStage n P) (ofStage n X) ∧
      ofStage n (idempotencyDefect X) = idempotencyDefect (ofStage n X) ∧
      ofStage n (peirceMaurerCartanCurvature P A C) =
        peirceMaurerCartanCurvature (ofStage n P) (ofStage n A) (ofStage n C) ∧
      ofStage n (peirceCovariantDeriv P A C X) =
        peirceCovariantDeriv (ofStage n P) (ofStage n A) (ofStage n C) (ofStage n X) :=
  ringHom_preserves_peirce_yang_mills (ofStage n) P A C X

end InfoGeometry.Algebra.PeirceTetraktysKreinBridge
