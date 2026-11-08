/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixStageInductiveLimit
import InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
import InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet

/-!
# Compatible weighted matrix functionals on the canonical matrix-stage colimit

The repository has two presentations of the same full matrix stages: matrices
indexed by bit words and matrices indexed by `Fin (2^n)`. A compatible
noncommutative weighted functional on the latter tower transports through the
proved stage equivalence and descends to the canonical quotient colimit of the
former tower. This is the generic transport layer for consumers such as the
finite Markov Green pairing; it does not construct a Markov stationary weight
net. It keeps weighted readouts distinct from the canonical tracial
`limitInner`; no nonuniform state is identified with that trace.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit

open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation

/-- The `Fin (2^n)` stage functional pulled back to the repository's canonical
full matrix carrier indexed by `BitWord n`. -/
def pulledWeightedStageFunctional
    (D : ∀ n : ℕ, MatrixStage n) (n : ℕ) : Stage n →ₗ[ℂ] ℂ :=
  (weightedStageFunctional D n).comp
    (stageStarAlgEquiv n).toAlgEquiv.toLinearMap

/-- Naturality of the explicit BitWord/`Fin (2^n)` stage equivalence for every
transition map, not only for one successor step. -/
theorem stageStarAlgEquiv_stageMorphism {m n : ℕ} (h : m ≤ n)
    (A : Stage m) :
    stageStarAlgEquiv n (stageMorphism m n h A) =
      rawMap h (stageStarAlgEquiv m A) := by
  induction h with
  | refl =>
      rw [stageMorphism_id]
      simp [rawMap, concreteMap_id]
  | @step n h ih =>
      rw [stageMorphism_step]
      change stageStarAlgEquiv (n + 1)
        (bondFun n (stageMorphism m n h A)) =
        rawMap (Nat.le.step h) (stageStarAlgEquiv m A)
      rw [stageStarAlgEquiv_bond, ih]
      have hmap : rawMap (Nat.le.step h) (stageStarAlgEquiv m A) =
          concreteStep n (rawMap h (stageStarAlgEquiv m A)) := by
        change map concreteData (Nat.le.step h) (stageStarAlgEquiv m A) =
          concreteData.step n (map concreteData h (stageStarAlgEquiv m A))
        rw [map_succ]
        rfl
      rw [hmap]

/-- Compatibility of the pulled-back full-matrix functional along all
canonical BitWord stage transitions. -/
theorem pulledWeightedStageFunctional_compatible
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : WeightedCompatible D) :
    ∀ {m n : ℕ} (h : m ≤ n) (A : Stage m),
      pulledWeightedStageFunctional D n (stageMorphism m n h A) =
        pulledWeightedStageFunctional D m A := by
  intro m n h A
  change weightedStageFunctional D n
      (stageStarAlgEquiv n (stageMorphism m n h A)) =
        weightedStageFunctional D m (stageStarAlgEquiv m A)
  rw [stageStarAlgEquiv_stageMorphism]
  exact hD h (stageStarAlgEquiv m A)

/-- A compatible weighted full-matrix functional, transported to and
descended through the canonical quotient matrix-stage colimit. -/
def weightedMatrixStageColimitFunctional
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : WeightedCompatible D) : MatrixStageLimit → ℂ :=
  Quotient.lift
    (fun x : Element => pulledWeightedStageFunctional D x.1 x.2)
    (by
      intro x y hxy
      rcases hxy with ⟨k, hx, hy, heq⟩
      rw [← pulledWeightedStageFunctional_compatible D hD hx x.2,
        ← pulledWeightedStageFunctional_compatible D hD hy y.2]
      rw [heq])

/-- Exact finite-stage readout of the descended functional. -/
@[simp]
theorem weightedMatrixStageColimitFunctional_toLimit
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : WeightedCompatible D) (n : ℕ) (A : Stage n) :
    weightedMatrixStageColimitFunctional D hD (toLimit n A) =
      weightedStageFunctional D n (stageStarAlgEquiv n A) := by
  calc
    weightedMatrixStageColimitFunctional D hD (toLimit n A) =
        pulledWeightedStageFunctional D n A := by
          simpa only [weightedMatrixStageColimitFunctional, toLimit] using
            (Quotient.lift_mk (s := matrixStageSetoid)
              (fun x : Element => pulledWeightedStageFunctional D x.1 x.2)
              (by
                intro x y hxy
                rcases hxy with ⟨k, hx, hy, heq⟩
                rw [← pulledWeightedStageFunctional_compatible D hD hx x.2,
                  ← pulledWeightedStageFunctional_compatible D hD hy y.2]
                rw [heq])
              (⟨n, A⟩ : Element))
    _ = weightedStageFunctional D n (stageStarAlgEquiv n A) := rfl

/-- The same readout expressed in the standard `Fin (2^n)` presentation.
It is the precise bridge to the existing weighted functional on its native
matrix tower. -/
@[simp]
theorem weightedMatrixStageColimitFunctional_stageEquiv
    (D : ∀ n : ℕ, MatrixStage n)
    (hD : WeightedCompatible D) (n : ℕ) (A : Stage n) :
    weightedMatrixStageColimitFunctional D hD
        (canonicalStageHom n A) =
      matrixTraceFunctional n (stageStarAlgEquiv n A * D n) := by
  rw [canonicalStageHom_apply,
    weightedMatrixStageColimitFunctional_toLimit,
    weightedStageFunctional_apply]

end InfoGeometry.QuantumContext.MatrixStageWeightedFunctionalColimit

end
