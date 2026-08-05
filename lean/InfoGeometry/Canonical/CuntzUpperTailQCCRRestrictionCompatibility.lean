import InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCoherence

/-!
# Fiber/ambient naturality for upper-tail restriction

The closed q-CCR zero-fibre inclusion is compatible with restriction from the
full inverse limit to an upper tail.  This is the canonical square connecting
the relation-locus diagram to its ambient parameter diagram.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCompatibility

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
open InfoGeometry.Canonical.CuntzUpperTailQCCRInverseRestriction
open InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCoherence
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

theorem upperTailQCCRRestriction_fiber_ambient_natural
    (m : ℕ) :
    upperTailQCCRZeroFiberRestrictionMap Stage T m ≫
        qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) =
      qCcrParameterZeroFiberToParameterLimit Stage
        T.toContinuousStarInductiveSystem ≫
        upperTailQCCRParameterRestrictionMap Stage T m := by
  apply limit.hom_ext
  intro j
  let jfull : ℕ := j.1
  let jtail : UpperNatIndex m := j
  let jzero : UpperNatIndex m := j
  calc
    (upperTailQCCRZeroFiberRestrictionMap Stage T m ≫
        qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) ≫
        limit.π
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j =
      upperTailQCCRZeroFiberRestrictionMap Stage T m ≫
        (qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ≫
          limit.π
            (qCcrParameterTopologicalDiagram
              (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j) := by
        rw [Category.assoc]
    _ = upperTailQCCRZeroFiberRestrictionMap Stage T m ≫
        (qCcrParameterZeroFiberToParameterLimitCone
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).π.app j := by
        rw [qCcrParameterZeroFiberToParameterLimit_projection]
    _ = upperTailQCCRZeroFiberRestrictionMap Stage T m ≫
        (limit.π
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j ≫
          (qCcrParameterZeroFiberToParameterNatTrans
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app j) := by
        rfl
    _ = (upperTailQCCRZeroFiberRestrictionMap Stage T m ≫
        limit.π
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j) ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app j := by
        rw [Category.assoc]
    _ = limit.π
          (qCcrParameterZeroFiberTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem) jfull ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app j := by
        rw [upperTailQCCRZeroFiberRestrictionMap_projection]
    _ = (qCcrParameterZeroFiberToParameterLimit Stage
          T.toContinuousStarInductiveSystem ≫
        upperTailQCCRParameterRestrictionMap Stage T m) ≫
        limit.π
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j := by
        rw [Category.assoc,
          upperTailQCCRParameterRestrictionMap_projection,
          qCcrParameterZeroFiberToParameterLimit_projection]
        rfl

theorem upperTailQCCRRestriction_between_fiber_ambient_natural
    (m n : ℕ) (hmn : m ≤ n) :
    upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
        qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n) =
      qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ≫
        upperTailQCCRParameterRestrictionMap_between Stage T m n hmn := by
  apply limit.hom_ext
  intro j
  let jm : UpperNatIndex m := ⟨j.1, le_trans hmn j.2⟩
  calc
    (upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
        qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) ≫
        limit.π
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j =
      upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
        (qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n) ≫
          limit.π
            (qCcrParameterTopologicalDiagram
              (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j) := by
        rw [Category.assoc]
    _ = upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
        (limit.π
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j ≫
          (qCcrParameterZeroFiberToParameterNatTrans
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)).app j) := by
        rw [qCcrParameterZeroFiberToParameterLimit_projection]
        rfl
    _ = (upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
        limit.π
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j) ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)).app j := by
        rw [Category.assoc]
    _ = limit.π
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) jm ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)).app j := by
        rw [upperTailQCCRZeroFiberRestrictionMap_between_projection]
    _ = (qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ≫
        upperTailQCCRParameterRestrictionMap_between Stage T m n hmn) ≫
        limit.π
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j := by
        rw [Category.assoc,
          upperTailQCCRParameterRestrictionMap_between_projection,
          qCcrParameterZeroFiberToParameterLimit_projection]
        rfl

end InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCompatibility
