import InfoGeometry.Canonical.CuntzUpperTailQCCRInverseRestriction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Nested upper-tail restriction and coherence

Restriction of a compatible family from a smaller upper tail to a larger one
is functorial.  This owner provides the between-tail maps and proves that
their composites agree with the direct restriction map, separately for the
ambient and zero-fibre q-CCR diagrams.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCoherence

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
open InfoGeometry.Canonical.CuntzUpperTailQCCRInverseRestriction
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

def upperTailQCCRParameterRestrictionCone_between
    (m n : ℕ) (hmn : m ≤ n) :
    Cone (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) where
  pt := qCcrParameterTopologicalLimit
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)
  π :=
    { app := fun j =>
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
          ⟨j.1, le_trans hmn j.2⟩
      naturality := by
        intro j k f
        have h := topologicalInverseProjection_naturality
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
          (CategoryTheory.homOfLE
            (show (⟨j.1, le_trans hmn j.2⟩ : UpperNatIndex m) ≤
              ⟨k.1, le_trans hmn k.2⟩ from leOfHom f))
        simpa [qCcrParameterTopologicalDiagram,
          qCcrParameterTransitionMap, upperTailContinuousStarSystem] using h.symm }

noncomputable def upperTailQCCRParameterRestrictionMap_between
    (m n : ℕ) (hmn : m ≤ n) :
    qCcrParameterTopologicalLimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ⟶
      qCcrParameterTopologicalLimit
        (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n) :=
  topologicalInverseLift
    (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n))
    (upperTailQCCRParameterRestrictionCone_between Stage T m n hmn)

@[reassoc]
theorem upperTailQCCRParameterRestrictionMap_between_projection
    (m n : ℕ) (hmn : m ≤ n) (j : UpperNatIndex n) :
    upperTailQCCRParameterRestrictionMap_between Stage T m n hmn ≫
        topologicalInverseProjection
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j =
      topologicalInverseProjection
        (qCcrParameterTopologicalDiagram
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
        ⟨j.1, le_trans hmn j.2⟩ := by
  exact topologicalInverseLift_projection
    (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n))
    (upperTailQCCRParameterRestrictionCone_between Stage T m n hmn) j

theorem upperTailQCCRParameterRestrictionMap_between_comp
    (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k) :
    upperTailQCCRParameterRestrictionMap_between Stage T m n hmn ≫
        upperTailQCCRParameterRestrictionMap_between Stage T n k hnk =
      upperTailQCCRParameterRestrictionMap_between Stage T m k (le_trans hmn hnk) := by
  apply topologicalInverseLift_unique
    (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage k) (upperTailContinuousStarSystem Stage T k))
    (upperTailQCCRParameterRestrictionCone_between Stage T m k (le_trans hmn hnk))
    (upperTailQCCRParameterRestrictionMap_between Stage T m n hmn ≫
      upperTailQCCRParameterRestrictionMap_between Stage T n k hnk)
  intro j
  rw [Category.assoc,
    upperTailQCCRParameterRestrictionMap_between_projection,
    upperTailQCCRParameterRestrictionMap_between_projection]
  rfl

def upperTailQCCRZeroFiberRestrictionCone_between
    (m n : ℕ) (hmn : m ≤ n) :
    Cone (qCcrParameterZeroFiberTopologicalDiagram
      (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) where
  pt := qCcrParameterZeroFiberTopologicalLimit
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)
  π :=
    { app := fun j =>
        topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
          ⟨j.1, le_trans hmn j.2⟩
      naturality := by
        intro j k f
        have h := topologicalInverseProjection_naturality
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
          (CategoryTheory.homOfLE
            (show (⟨j.1, le_trans hmn j.2⟩ : UpperNatIndex m) ≤
              ⟨k.1, le_trans hmn k.2⟩ from leOfHom f))
        simpa [qCcrParameterZeroFiberTopologicalDiagram,
          qCcrParameterZeroFiberTransitionTopCatHom,
          qCcrParameterZeroFiberTransitionMap,
          qCcrParameterTransitionMap, upperTailContinuousStarSystem] using h.symm }

noncomputable def upperTailQCCRZeroFiberRestrictionMap_between
    (m n : ℕ) (hmn : m ≤ n) :
    qCcrParameterZeroFiberTopologicalLimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ⟶
      qCcrParameterZeroFiberTopologicalLimit
        (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n) :=
  topologicalInverseLift
    (qCcrParameterZeroFiberTopologicalDiagram
      (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n))
    (upperTailQCCRZeroFiberRestrictionCone_between Stage T m n hmn)

@[reassoc]
theorem upperTailQCCRZeroFiberRestrictionMap_between_projection
    (m n : ℕ) (hmn : m ≤ n) (j : UpperNatIndex n) :
    upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
        topologicalInverseProjection
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j =
      topologicalInverseProjection
        (qCcrParameterZeroFiberTopologicalDiagram
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
        ⟨j.1, le_trans hmn j.2⟩ := by
  exact topologicalInverseLift_projection
    (qCcrParameterZeroFiberTopologicalDiagram
      (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n))
    (upperTailQCCRZeroFiberRestrictionCone_between Stage T m n hmn) j

theorem upperTailQCCRZeroFiberRestrictionMap_between_comp
    (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k) :
    upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
        upperTailQCCRZeroFiberRestrictionMap_between Stage T n k hnk =
      upperTailQCCRZeroFiberRestrictionMap_between Stage T m k (le_trans hmn hnk) := by
  apply topologicalInverseLift_unique
    (qCcrParameterZeroFiberTopologicalDiagram
      (UpperTailStage Stage k) (upperTailContinuousStarSystem Stage T k))
    (upperTailQCCRZeroFiberRestrictionCone_between Stage T m k (le_trans hmn hnk))
    (upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn ≫
      upperTailQCCRZeroFiberRestrictionMap_between Stage T n k hnk)
  intro j
  rw [Category.assoc,
    upperTailQCCRZeroFiberRestrictionMap_between_projection,
    upperTailQCCRZeroFiberRestrictionMap_between_projection]
  rfl

end InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCoherence
