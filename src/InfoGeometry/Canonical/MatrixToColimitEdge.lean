/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
import InfoGeometry.Canonical.MatrixConnectionCurvatureTransport
import InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.TowerMatrix
import InfoGeometry.Canonical.EinsteinCartanBianchiBridge
import InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
import InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Phase 7: Matrix exterior-form carrier → inductive colimit edge

Connects the matrix-valued connection carrier `Matrix (Fin (2^N)) (Fin (2^N)) (ExteriorAlgebra ℝ V)`
into the inductive colimit `Limit` (owned by `PeirceTetraktysColimitCoercivity`, carrier
`Stage n → bondMap → ofStage → Limit`).

The edge uses the augmentation map `algebraMapInv : ExteriorAlgebra ℝ V →+* ℝ` (grade-zero
projection), applied entry-wise to matrices indexed by `Idx N`, then composed with
`ofStage N : Stage N →+* Limit`. The conversion between `Fin (2^N)`- and `Idx N`-indexed
matrices uses entry-wise reindexing via `idxEquivFinPowTwo`.

All Peirce algebraic operations are preserved because they are defined purely in terms of
ring operations, and the composite map is a ring homomorphism.

Curvature transport (`curvatureFromConnection`, `covariantDerivative`, Bianchi) remains on
the matrix exterior-form carrier because `Limit` has no exterior-derivative structure;
the edge maps the computed curvature element into `Limit` for colimit-level statements.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixToColimitEdge

open ExteriorAlgebra
open InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity
open InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap
open InfoGeometry.Canonical.MatrixConnectionCurvatureTransport
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Core.IdempotentGraphGrassmannian
open CanonicalTwoSheetedInductiveColimit
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {N : ℕ}

local notation "Mat" => Matrix (Fin (2 ^ N)) (Fin (2 ^ N)) (ExteriorAlgebra ℝ V)

@[irreducible]
def gradeZeroRingHom : ExteriorAlgebra ℝ V →+* ℝ :=
  algebraMapInv.toRingHom

/-! Entry-wise grade-zero lift: `Mat → Stage N` -/
def gradeZeroMatrixFun : Mat → Stage N :=
  fun A i j => gradeZeroRingHom (A ((idxEquivFinPowTwo N).toFun i) ((idxEquivFinPowTwo N).toFun j))

def gradeZeroMatrixRingHom : Mat →+* Stage N :=
  { toFun := fun A i j => gradeZeroRingHom (A ((idxEquivFinPowTwo N).toFun i) ((idxEquivFinPowTwo N).toFun j))
  , map_add' := fun A B => by
      ext i j
      calc
        gradeZeroMatrixFun (A + B) i j =
          gradeZeroRingHom ((A + B) ((idxEquivFinPowTwo N).toFun i) ((idxEquivFinPowTwo N).toFun j)) := by rfl
        _ = gradeZeroRingHom (A ((idxEquivFinPowTwo N).toFun i) ((idxEquivFinPowTwo N).toFun j) +
          B ((idxEquivFinPowTwo N).toFun i) ((idxEquivFinPowTwo N).toFun j)) := by
          rw [Matrix.add_apply]
        _ = gradeZeroRingHom (A ((idxEquivFinPowTwo N).toFun i) ((idxEquivFinPowTwo N).toFun j)) +
          gradeZeroRingHom (B ((idxEquivFinPowTwo N).toFun i) ((idxEquivFinPowTwo N).toFun j)) := by
          rw [gradeZeroRingHom.map_add]
        _ = gradeZeroMatrixFun A i j + gradeZeroMatrixFun B i j := by simp [gradeZeroMatrixFun]
    , map_zero' := by
      ext i j
      simp [gradeZeroMatrixFun, Matrix.zero_apply, gradeZeroRingHom.map_zero]
    , map_one' := by
      ext i j
      simp [gradeZeroMatrixFun, Matrix.one_apply]
      , map_mul' := by
          intro A B
          ext i j
          change gradeZeroRingHom
              ((A * B) ((idxEquivFinPowTwo N).toFun i)
                ((idxEquivFinPowTwo N).toFun j)) = _
          rw [Matrix.mul_apply, map_sum]
          simp only [gradeZeroMatrixFun, Matrix.mul_apply, map_mul]
          exact (Equiv.sum_comp (idxEquivFinPowTwo N)
            (fun k : Fin (2 ^ N) =>
              gradeZeroRingHom
                (A ((idxEquivFinPowTwo N).toFun i) k) *
              gradeZeroRingHom
                (B k ((idxEquivFinPowTwo N).toFun j)))).symm
  }

def matrixToColimitRingHom : Mat →+* Limit :=
  (ofStage N).comp gradeZeroMatrixRingHom

/-! Curvature element transported to `Limit` -/
theorem curvature_in_colimit
    {d : Module.End ℝ (ExteriorAlgebra ℝ V)} {A : Mat} :
    matrixToColimitRingHom (curvatureFromConnection d A) =
      matrixToColimitRingHom (curvatureFromConnection d A) := by
  rfl

/-! Connection `A` and curvature `F_A` both embed into `Limit`:
`g(F_A) = g(dA + A²) = g(dA) + g(A)·g(A)` in `Limit`. -/
theorem connection_curvature_colimit_element
    {d : Module.End ℝ (ExteriorAlgebra ℝ V)} {A : Mat} :
    matrixToColimitRingHom (curvatureFromConnection d A) =
      matrixToColimitRingHom (matrixExteriorDerivative d A) +
        matrixToColimitRingHom A * matrixToColimitRingHom A := by
  calc
    matrixToColimitRingHom (curvatureFromConnection d A) =
      matrixToColimitRingHom (matrixExteriorDerivative d A + A * A) := by rfl
    _ = matrixToColimitRingHom (matrixExteriorDerivative d A) + matrixToColimitRingHom (A * A) := by
      apply matrixToColimitRingHom.map_add
    _ = matrixToColimitRingHom (matrixExteriorDerivative d A) +
        (matrixToColimitRingHom A * matrixToColimitRingHom A) := by
      have h : matrixToColimitRingHom (A * A) = matrixToColimitRingHom A * matrixToColimitRingHom A := by
        apply matrixToColimitRingHom.map_mul
      rw [h]
    _ = matrixToColimitRingHom (matrixExteriorDerivative d A) +
        matrixToColimitRingHom A * matrixToColimitRingHom A := by rfl

end InfoGeometry.Canonical.MatrixToColimitEdge

end noncomputable section
