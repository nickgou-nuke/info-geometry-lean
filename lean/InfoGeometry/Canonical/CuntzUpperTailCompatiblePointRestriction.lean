import InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCompatibility
import InfoGeometry.Canonical.CuntzCompatiblePointLimit

/-!
# Restriction of compatible Cuntz inverse-limit points to upper tails

This owner connects the generic compatible Cuntz property family on the full
inductive system to the corresponding family on an upper tail.  The result is
an equality of actual `TopCat` inverse-limit readouts, obtained by the limit
universal property.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzUpperTailCompatiblePointRestriction

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
open InfoGeometry.Canonical.CuntzUpperTailQCCRLimitReadout
open InfoGeometry.Canonical.CuntzUpperTailQCCRInverseRestriction
open InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCompatibility
open InfoGeometry.Canonical.CuntzUpperTailQCCRRestrictionCoherence
open InfoGeometry.Canonical.CuntzCompatiblePointColimit
open InfoGeometry.Canonical.CuntzCompatiblePointLimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

/-- Restrict a compatible Cuntz property family to the stages at or above `m`. -/
def upperTailCompatibleCuntzPointFamily
    (family : CompatibleCuntzPointFamily T.toContinuousStarInductiveSystem)
    (m : ℕ) :
    CompatibleCuntzPointFamily
      (upperTailContinuousStarSystem Stage T m) where
  c := fun j => family.c j.1
  cstar := fun j => family.cstar j.1
  relation := fun j => family.relation j.1
  compatible_c := by
    intro j k hjk
    simpa [upperTailContinuousStarSystem] using
      family.map_c (show j.1 ≤ k.1 from hjk)
  compatible_cstar := by
    intro j k hjk
    simpa [upperTailContinuousStarSystem] using
      family.map_cstar (show j.1 ≤ k.1 from hjk)

theorem upperTailCompatibleCuntzPointFamily_point
    (family : CompatibleCuntzPointFamily T.toContinuousStarInductiveSystem)
    (m : ℕ) (j : UpperNatIndex m) :
    (upperTailCompatibleCuntzPointFamily Stage T family m).toQCCR.point j =
      family.toQCCR.point j.1 := by
  rfl

theorem compatibleCuntzPointLimitMap_restrict
    (family : CompatibleCuntzPointFamily T.toContinuousStarInductiveSystem)
    (m : ℕ) :
    cuntzCompatiblePointLimitMap
        T.toContinuousStarInductiveSystem family ≫
        upperTailQCCRZeroFiberRestrictionMap Stage T m =
      cuntzCompatiblePointLimitMap
        (upperTailContinuousStarSystem Stage T m)
        (upperTailCompatibleCuntzPointFamily Stage T family m) := by
  apply limit.hom_ext
  intro j
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  have hfull := cuntzCompatiblePointLimitMap_projection
    T.toContinuousStarInductiveSystem family j.1 u
  have htail := cuntzCompatiblePointLimitMap_projection
    (upperTailContinuousStarSystem Stage T m)
    (upperTailCompatibleCuntzPointFamily Stage T family m) j u
  change
    ((cuntzCompatiblePointLimitMap
        T.toContinuousStarInductiveSystem family ≫
      upperTailQCCRZeroFiberRestrictionMap Stage T m) ≫
      limit.π
        (qCcrParameterZeroFiberTopologicalDiagram
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j) u =
      ((cuntzCompatiblePointLimitMap
          (upperTailContinuousStarSystem Stage T m)
          (upperTailCompatibleCuntzPointFamily Stage T family m) ≫
        limit.π
        (qCcrParameterZeroFiberTopologicalDiagram
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j) u)
  rw [Category.assoc, upperTailQCCRZeroFiberRestrictionMap_projection]
  change
    limit.π
        (qCcrParameterZeroFiberTopologicalDiagram Stage
          T.toContinuousStarInductiveSystem) j.1
        (cuntzCompatiblePointLimitMap
          T.toContinuousStarInductiveSystem family u) =
      limit.π
        (qCcrParameterZeroFiberTopologicalDiagram
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j
        (cuntzCompatiblePointLimitMap
          (upperTailContinuousStarSystem Stage T m)
          (upperTailCompatibleCuntzPointFamily Stage T family m) u)
  rw [hfull, htail]
  rfl

theorem compatibleCuntzPointAmbientLimitMap_restrict
    (family : CompatibleCuntzPointFamily T.toContinuousStarInductiveSystem)
    (m : ℕ) :
    cuntzCompatiblePointAmbientLimitMap
        T.toContinuousStarInductiveSystem family ≫
        upperTailQCCRParameterRestrictionMap Stage T m =
      cuntzCompatiblePointAmbientLimitMap
        (upperTailContinuousStarSystem Stage T m)
        (upperTailCompatibleCuntzPointFamily Stage T family m) := by
  rw [cuntzCompatiblePointAmbientLimitMap,
    cuntzCompatiblePointAmbientLimitMap]
  rw [Category.assoc,
    ← upperTailQCCRRestriction_fiber_ambient_natural]
  rw [← Category.assoc, compatibleCuntzPointLimitMap_restrict]

theorem compatibleCuntzPointLimitMap_between
    (family : CompatibleCuntzPointFamily T.toContinuousStarInductiveSystem)
    (m n : ℕ) (hmn : m ≤ n) :
    cuntzCompatiblePointLimitMap
        (upperTailContinuousStarSystem Stage T m)
        (upperTailCompatibleCuntzPointFamily Stage T family m) ≫
        upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn =
      cuntzCompatiblePointLimitMap
        (upperTailContinuousStarSystem Stage T n)
        (upperTailCompatibleCuntzPointFamily Stage T family n) := by
  apply limit.hom_ext
  intro j
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  have hm := cuntzCompatiblePointLimitMap_projection
    (upperTailContinuousStarSystem Stage T m)
    (upperTailCompatibleCuntzPointFamily Stage T family m)
    ⟨j.1, le_trans hmn j.2⟩ u
  have hn := cuntzCompatiblePointLimitMap_projection
    (upperTailContinuousStarSystem Stage T n)
    (upperTailCompatibleCuntzPointFamily Stage T family n) j u
  change
    ((cuntzCompatiblePointLimitMap
        (upperTailContinuousStarSystem Stage T m)
        (upperTailCompatibleCuntzPointFamily Stage T family m) ≫
      upperTailQCCRZeroFiberRestrictionMap_between Stage T m n hmn) ≫
      limit.π
        (qCcrParameterZeroFiberTopologicalDiagram
          (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j) u =
      ((cuntzCompatiblePointLimitMap
          (upperTailContinuousStarSystem Stage T n)
          (upperTailCompatibleCuntzPointFamily Stage T family n) ≫
        limit.π
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j)) u
  rw [Category.assoc,
    upperTailQCCRZeroFiberRestrictionMap_between_projection]
  change
    limit.π
        (qCcrParameterZeroFiberTopologicalDiagram
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
        ⟨j.1, le_trans hmn j.2⟩
        (cuntzCompatiblePointLimitMap
          (upperTailContinuousStarSystem Stage T m)
          (upperTailCompatibleCuntzPointFamily Stage T family m) u) =
      limit.π
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage n) (upperTailContinuousStarSystem Stage T n)) j
          (cuntzCompatiblePointLimitMap
            (upperTailContinuousStarSystem Stage T n)
          (upperTailCompatibleCuntzPointFamily Stage T family n) u)
  rw [hm, hn]
  rfl

end InfoGeometry.Canonical.CuntzUpperTailCompatiblePointRestriction
