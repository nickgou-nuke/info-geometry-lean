import InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCoherence
import InfoGeometry.Algebra.FiniteSpinAlgebra

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
  have h_mid :
      topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem) j.1 ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app j =
      topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem) j.1 ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          Stage T.toContinuousStarInductiveSystem).app j.1 := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  have h_lhs :
      (upperTailQCCRZeroFiberRestrictionMap Stage T m ≫
          qCcrParameterZeroFiberToParameterLimit
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) ≫
          topologicalInverseProjection
            (qCcrParameterTopologicalDiagram
              (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j =
        topologicalInverseProjection
            (qCcrParameterZeroFiberTopologicalDiagram Stage
              T.toContinuousStarInductiveSystem) j.1 ≫
          (qCcrParameterZeroFiberToParameterNatTrans
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app j := by
    rw [Category.assoc]
    rw [qCcrParameterZeroFiberToParameterLimit_projection]
    dsimp [qCcrParameterZeroFiberToParameterLimitCone]
    rw [← Category.assoc]
    rw [upperTailQCCRZeroFiberRestrictionMap_projection]
    rfl
  have h1 : upperTailQCCRParameterRestrictionMap Stage T m ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j =
      topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage
          T.toContinuousStarInductiveSystem) j.1 :=
    upperTailQCCRParameterRestrictionMap_projection Stage T m j
  have h_rhs :
      (qCcrParameterZeroFiberToParameterLimit Stage
          T.toContinuousStarInductiveSystem ≫
        upperTailQCCRParameterRestrictionMap Stage T m) ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j =
      topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem) j.1 ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          Stage T.toContinuousStarInductiveSystem).app j.1 := by
    have hstep : (qCcrParameterZeroFiberToParameterLimit Stage
          T.toContinuousStarInductiveSystem ≫
        upperTailQCCRParameterRestrictionMap Stage T m) ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j =
        qCcrParameterZeroFiberToParameterLimit Stage
          T.toContinuousStarInductiveSystem ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem) j.1 := by
      rw [Category.assoc]
      exact congrArg (qCcrParameterZeroFiberToParameterLimit Stage T.toContinuousStarInductiveSystem ≫ ·) h1
    have h2 := qCcrParameterZeroFiberToParameterLimit_projection Stage T.toContinuousStarInductiveSystem j.1
    dsimp [qCcrParameterZeroFiberToParameterLimitCone] at h2
    exact hstep.trans h2
  exact (h_lhs.trans h_mid).trans h_rhs.symm

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
  have h_mid :
      topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) jm ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)).app j =
      topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) jm ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app jm := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  have h_lhs :
      (upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
          qCcrParameterZeroFiberToParameterLimit
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) ≫
          topologicalInverseProjection
            (qCcrParameterTopologicalDiagram
              (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j =
        topologicalInverseProjection
            (qCcrParameterZeroFiberTopologicalDiagram
              (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) jm ≫
          (qCcrParameterZeroFiberToParameterNatTrans
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)).app j := by
    rw [Category.assoc]
    rw [qCcrParameterZeroFiberToParameterLimit_projection]
    dsimp [qCcrParameterZeroFiberToParameterLimitCone]
    rw [← Category.assoc]
    rw [upperTailQCCRZeroFiberRestrictionMap_between_projection]
    rfl
  have h1 : upperTailQCCRParameterRestrictionMap_between Stage T m n hmn ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j =
      topologicalInverseProjection
        (qCcrParameterTopologicalDiagram
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) jm :=
    upperTailQCCRParameterRestrictionMap_between_projection Stage T m n hmn j
  have h_rhs :
      (qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ≫
        upperTailQCCRParameterRestrictionMap_between Stage T m n hmn) ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j =
      topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) jm ≫
        (qCcrParameterZeroFiberToParameterNatTrans
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app jm := by
    have hstep : (qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ≫
        upperTailQCCRParameterRestrictionMap_between Stage T m n hmn) ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j =
        qCcrParameterZeroFiberToParameterLimit
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) jm := by
      rw [Category.assoc]
      exact congrArg (qCcrParameterZeroFiberToParameterLimit (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ≫ ·) h1
    have h2 := qCcrParameterZeroFiberToParameterLimit_projection
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) jm
    dsimp [qCcrParameterZeroFiberToParameterLimitCone] at h2
    exact hstep.trans h2
  exact (h_lhs.trans h_mid).trans h_rhs.symm

end InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCompatibility
