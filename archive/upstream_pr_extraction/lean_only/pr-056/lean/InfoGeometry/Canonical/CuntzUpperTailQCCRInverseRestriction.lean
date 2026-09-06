import InfoGeometry.Canonical.CuntzUpperTailQCCRLimitReadout
import InfoGeometry.Canonical.FilteredTopologicalDirectInverseColimit

/-!
# Restriction from the full q-CCR inverse limit to an upper tail

There is a canonical map in the restriction direction: a compatible family
on all stages restricts to the stages `j ≥ m`.  This owner builds that map by
the `TopCat` inverse-limit universal property.  It deliberately does not
include a reverse map, since the inductive system supplies forward maps but
not inverses.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzUpperTailQCCRInverseRestriction

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

def upperTailQCCRParameterRestrictionCone (m : ℕ) :
    Cone (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) where
  pt := qCcrParameterTopologicalLimit Stage T.toContinuousStarInductiveSystem
  π :=
    { app := fun j =>
        limit.π
          (qCcrParameterTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem) j.1
      naturality := by
        intro j k f
        have hfull := topologicalInverseProjection_naturality
          (qCcrParameterTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem)
          (CategoryTheory.homOfLE (show j.1 ≤ k.1 from leOfHom f))
        simpa [qCcrParameterTopologicalDiagram,
          qCcrParameterTransitionMap, upperTailContinuousStarSystem] using hfull.symm }

noncomputable def upperTailQCCRParameterRestrictionMap (m : ℕ) :
    qCcrParameterTopologicalLimit Stage T.toContinuousStarInductiveSystem ⟶
      qCcrParameterTopologicalLimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) :=
  limit.lift
    (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
    (upperTailQCCRParameterRestrictionCone Stage T m)

@[reassoc]
theorem upperTailQCCRParameterRestrictionMap_projection
    (m : ℕ) (j : UpperNatIndex m) :
    upperTailQCCRParameterRestrictionMap Stage T m ≫
        limit.π
          (qCcrParameterTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j =
      limit.π
        (qCcrParameterTopologicalDiagram Stage
          T.toContinuousStarInductiveSystem) j.1 := by
  exact topologicalInverseLift_projection
    (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
    (upperTailQCCRParameterRestrictionCone Stage T m) j

def upperTailQCCRZeroFiberRestrictionCone (m : ℕ) :
    Cone (qCcrParameterZeroFiberTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) where
  pt := qCcrParameterZeroFiberTopologicalLimit Stage T.toContinuousStarInductiveSystem
  π :=
    { app := fun j =>
        limit.π
          (qCcrParameterZeroFiberTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem) j.1
      naturality := by
        intro j k f
        have hfull := topologicalInverseProjection_naturality
          (qCcrParameterZeroFiberTopologicalDiagram Stage
            T.toContinuousStarInductiveSystem)
          (CategoryTheory.homOfLE (show j.1 ≤ k.1 from leOfHom f))
        simpa [qCcrParameterZeroFiberTopologicalDiagram,
          qCcrParameterZeroFiberTransitionTopCatHom,
          qCcrParameterZeroFiberTransitionMap,
          qCcrParameterTransitionMap, upperTailContinuousStarSystem] using hfull.symm }

noncomputable def upperTailQCCRZeroFiberRestrictionMap (m : ℕ) :
    qCcrParameterZeroFiberTopologicalLimit Stage T.toContinuousStarInductiveSystem ⟶
      qCcrParameterZeroFiberTopologicalLimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) :=
  limit.lift
    (qCcrParameterZeroFiberTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
    (upperTailQCCRZeroFiberRestrictionCone Stage T m)

@[reassoc]
theorem upperTailQCCRZeroFiberRestrictionMap_projection
    (m : ℕ) (j : UpperNatIndex m) :
    upperTailQCCRZeroFiberRestrictionMap Stage T m ≫
        limit.π
          (qCcrParameterZeroFiberTopologicalDiagram
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j =
      limit.π
        (qCcrParameterZeroFiberTopologicalDiagram Stage
          T.toContinuousStarInductiveSystem) j.1 := by
  exact topologicalInverseLift_projection
    (qCcrParameterZeroFiberTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
    (upperTailQCCRZeroFiberRestrictionCone Stage T m) j

end InfoGeometry.Canonical.CuntzUpperTailQCCRInverseRestriction
