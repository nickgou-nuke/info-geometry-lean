import InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
import InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit

/-!
# Inverse-limit readouts for upper-tail Cuntz q-CCR points

The upper-tail Cuntz construction already has a direct-colimit readout.  This
owner supplies the compatible inverse-limit point and its ambient parameter
map, preserving the same finite-stage property at every tail index.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzUpperTailQCCRLimitReadout

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

def upperTailCuntzQCCRPointTopCatFamily
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) :
    TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage j.1) //
        p ∈ qCcrParameterZeroLocus (A := Stage j.1)} :=
  TopCat.ofHom
    { toFun := fun _ => upperTailCuntzQCCRPoint Stage T m i j
      continuous_toFun := continuous_const }

theorem upperTailCuntzQCCRPointTopCatFamily_natural
    (m : ℕ) (i : Fin m) {j k : UpperNatIndex m} (hjk : j ≤ k) :
    upperTailCuntzQCCRPointTopCatFamily Stage T m i j ≫
        qCcrParameterZeroFiberTransitionTopCatHom
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)
          hjk =
      upperTailCuntzQCCRPointTopCatFamily Stage T m i k := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  exact congrArg Subtype.val
    (upperTailCuntzPointFamily_compatible Stage T m i hjk)

noncomputable def upperTailCuntzQCCRLimitMap
    (m : ℕ) (i : Fin m) :
    TopCat.of PUnit ⟶
      qCcrParameterZeroFiberTopologicalLimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) :=
  qCcrParameterZeroFiberPointLimitMap
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)
    (upperTailCuntzQCCRPointTopCatFamily Stage T m i)
    (by
      intro j k f
      exact upperTailCuntzQCCRPointTopCatFamily_natural Stage T m i
        (leOfHom f))

@[simp]
theorem upperTailCuntzQCCRLimitMap_projection
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (u : PUnit) :
    limit.π
        (qCcrParameterZeroFiberTopologicalDiagram
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j
        (upperTailCuntzQCCRLimitMap Stage T m i u) =
      upperTailCuntzQCCRPointTopCatFamily Stage T m i j u := by
  exact qCcrParameterZeroFiberPointLimitMap_projection
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)
    (upperTailCuntzQCCRPointTopCatFamily Stage T m i)
    (by
      intro j k f
      exact upperTailCuntzQCCRPointTopCatFamily_natural Stage T m i
        (leOfHom f)) j u

noncomputable def upperTailCuntzQCCRAmbientLimitMap
    (m : ℕ) (i : Fin m) :
    TopCat.of PUnit ⟶
      qCcrParameterTopologicalLimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) :=
  upperTailCuntzQCCRLimitMap Stage T m i ≫
    qCcrParameterZeroFiberToParameterLimit
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)

@[simp]
theorem upperTailCuntzQCCRAmbientLimitMap_projection
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (u : PUnit) :
    limit.π
        (qCcrParameterTopologicalDiagram
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) j
        (upperTailCuntzQCCRAmbientLimitMap Stage T m i u) =
      (qCcrParameterZeroFiberToParameterNatTrans
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app j
        (upperTailCuntzQCCRPointTopCatFamily Stage T m i j u) := by
  have h := qCcrParameterZeroFiberPointAmbientLimitMap_projection
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)
    (upperTailCuntzQCCRPointTopCatFamily Stage T m i)
    (by
      intro j k f
      exact upperTailCuntzQCCRPointTopCatFamily_natural Stage T m i
        (leOfHom f)) j u
  simpa [upperTailCuntzQCCRAmbientLimitMap,
    upperTailCuntzQCCRLimitMap] using h

end InfoGeometry.Canonical.CuntzUpperTailQCCRLimitReadout
