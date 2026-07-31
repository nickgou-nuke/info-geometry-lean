import InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit
import InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit

/-!
# Cuntz-generator points on an upper-tail q-CCR colimit

The finite Cuntz generator witness is now instantiated as a compatible point
family on the upper-tail index category.  The resulting map is obtained by
the generic filtered `TopCat` colimit construction, so the endpoint witness
is connected to the same noncommutative colimit as the transition maps.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.CuntzStarInductiveSystem
open InfoGeometry.Canonical.CuntzTowerUpperTailActionColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRCompatiblePointColimit
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.CStarCuntzCARCCRTopologicalBridge
open InfoGeometry.Physics.CStarCuntzTensorQuotient
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : CuntzStarTower Stage)

abbrev UpperTailStage (m : ℕ) : UpperNatIndex m → Type :=
  fun j => Stage j.1

include T

def upperTailContinuousStarSystem (m : ℕ) :
    ContinuousStarInductiveSystem (UpperTailStage Stage m) where
  map := fun {j k} hj =>
    T.map (show j.1 ≤ k.1 from hj)
  map_id := by
    intro j
    simpa using T.map_id j.1
  map_comp := by
    intro j k l hjk hkl
    simpa using T.map_comp
      (show j.1 ≤ k.1 from hjk)
      (show k.1 ≤ l.1 from hkl)

def upperTailCuntzQCCRPoint
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) :
    {p : QCCRParameterSpace (Stage j.1) //
      p ∈ qCcrParameterZeroLocus (A := Stage j.1)} :=
  ⟨(star ((T.family j.1).S (Fin.castLE j.2 i)),
      ((T.family j.1).S (Fin.castLE j.2 i), (0 : Stage j.1))), by
    change qCcrParameterResidualContinuousMap (A := Stage j.1)
        (star ((T.family j.1).S (Fin.castLE j.2 i)),
          ((T.family j.1).S (Fin.castLE j.2 i), (0 : Stage j.1))) = 0
    simpa [qCcrParameterResidualContinuousMap] using
      cstar_cuntz_generator_qccr_zero (T.family j.1) (Fin.castLE j.2 i)⟩

def upperTailCuntzPointFamily
    (m : ℕ) (i : Fin m) :
    CompatibleQCCRPointFamily
      (sys := upperTailContinuousStarSystem Stage T m) where
  point := upperTailCuntzQCCRPoint Stage T m i

theorem upperTailCuntzPointFamily_compatible
    (m : ℕ) (i : Fin m) :
    ∀ {j k : UpperNatIndex m} (hjk : j ≤ k),
      qCcrParameterZeroFiberTransitionMap
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) hjk
          ((upperTailCuntzPointFamily Stage T m i).point j) =
        (upperTailCuntzPointFamily Stage T m i).point k := by
    intro j k hjk
    apply Subtype.ext
    apply Prod.ext
    · simp [upperTailCuntzPointFamily,
        qCcrParameterZeroFiberTransitionMap,
        qCcrParameterTransitionMap, upperTailCuntzQCCRPoint,
        upperTailContinuousStarSystem, T.map_generator, map_star]
    · apply Prod.ext
      · simp [upperTailCuntzPointFamily,
          qCcrParameterZeroFiberTransitionMap,
          qCcrParameterTransitionMap, upperTailCuntzQCCRPoint,
          upperTailContinuousStarSystem, T.map_generator]
      · simp [upperTailCuntzPointFamily,
          qCcrParameterZeroFiberTransitionMap,
          qCcrParameterTransitionMap, upperTailCuntzQCCRPoint,
          upperTailContinuousStarSystem]

noncomputable def upperTailCuntzQCCRColimitMap
    (m : ℕ) (i : Fin m) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) :=
  compatiblePointColimitMap
    (upperTailContinuousStarSystem Stage T m)
    (upperTailCuntzPointFamily Stage T m i)
    (upperTailCuntzPointFamily_compatible Stage T m i)

theorem upperTailCuntzQCCRColimitMap_stage
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) :
    topologicalDirectInjection
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j ≫
        upperTailCuntzQCCRColimitMap Stage T m i =
      (compatiblePointNatTrans
        (upperTailContinuousStarSystem Stage T m)
        (upperTailCuntzPointFamily Stage T m i)
        (upperTailCuntzPointFamily_compatible Stage T m i)).app j ≫
        qCcrParameterZeroFiberTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j := by
  exact compatiblePointColimitMap_stage
    (upperTailContinuousStarSystem Stage T m)
    (upperTailCuntzPointFamily Stage T m i)
    (upperTailCuntzPointFamily_compatible Stage T m i) j

noncomputable def upperTailCuntzQCCRZeroFiberToParameterColimit
    (m : ℕ) :
    qCcrParameterZeroFiberTopologicalColimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ⟶
      qCcrParameterTopologicalColimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) :=
  qCcrParameterZeroFiberToParameterColimit
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)

theorem upperTailCuntzQCCRZeroFiberToParameterColimit_stage
    (m : ℕ) (j : UpperNatIndex m) :
    qCcrParameterZeroFiberTopologicalInjection
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j ≫
        upperTailCuntzQCCRZeroFiberToParameterColimit Stage T m =
      (qCcrParameterZeroFiberToParameterNatTrans
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)).app j ≫
        qCcrParameterTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j := by
  exact qCcrParameterZeroFiberToParameterColimit_stage
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j

noncomputable def upperTailCuntzQCCRParameterColimitMap
    (m : ℕ) (i : Fin m) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) :=
  upperTailCuntzQCCRColimitMap Stage T m i ≫
    upperTailCuntzQCCRZeroFiberToParameterColimit Stage T m

theorem upperTailCuntzQCCRParameterColimitMap_stage_apply
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (u : PUnit) :
    upperTailCuntzQCCRParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      qCcrParameterTopologicalInjection
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
        (upperTailCuntzQCCRPoint Stage T m i j).1 := by
  have hpoint := compatiblePointColimitMap_stage_apply
    (upperTailContinuousStarSystem Stage T m)
    (upperTailCuntzPointFamily Stage T m i)
    (upperTailCuntzPointFamily_compatible Stage T m i) j u
  have hincl := qCcrParameterZeroFiberToParameterColimit_stage
    (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
  have hincl' := congrArg
    (fun f => f (upperTailCuntzQCCRPoint Stage T m i j)) hincl
  have hincl'' :
      upperTailCuntzQCCRZeroFiberToParameterColimit Stage T m
          (qCcrParameterZeroFiberTopologicalInjection
            (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
            (upperTailCuntzQCCRPoint Stage T m i j)) =
        qCcrParameterTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
          (upperTailCuntzQCCRPoint Stage T m i j).1 := by
    simpa [qCcrParameterZeroFiberToParameterNatTrans] using hincl'
  calc
    upperTailCuntzQCCRParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      upperTailCuntzQCCRZeroFiberToParameterColimit Stage T m
        (qCcrParameterZeroFiberTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
          (upperTailCuntzQCCRPoint Stage T m i j)) := by
        have hpoint' := congrArg
          (fun z => upperTailCuntzQCCRZeroFiberToParameterColimit Stage T m z)
          hpoint
        simpa [upperTailCuntzQCCRParameterColimitMap] using hpoint'
    _ = qCcrParameterTopologicalInjection
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
        (upperTailCuntzQCCRPoint Stage T m i j).1 := by
        exact hincl''

def upperTailQCCRParameterToFullCocone
    (m : ℕ) :
    Cocone
      (qCcrParameterTopologicalDiagram
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m)) where
  pt := qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem
  ι :=
    { app := fun j =>
        qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
      naturality := by
        intro j k f
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro p
        change qCcrParameterTopologicalInjection Stage
            T.toContinuousStarInductiveSystem k.1
            (qCcrParameterTransitionMap (UpperTailStage Stage m)
              (upperTailContinuousStarSystem Stage T m)
              (show j.1 ≤ k.1 from leOfHom f) p) =
          qCcrParameterTopologicalInjection Stage
            T.toContinuousStarInductiveSystem j.1 p
        simpa [qCcrParameterTransitionMap, upperTailContinuousStarSystem] using
          qCcrParameterTopologicalInjection_transition Stage
            T.toContinuousStarInductiveSystem (show j.1 ≤ k.1 from leOfHom f) p }

noncomputable def upperTailQCCRParameterToFullColimitMap
    (m : ℕ) :
    qCcrParameterTopologicalColimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ⟶
      qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem :=
  topologicalDirectDescend
    (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
    (upperTailQCCRParameterToFullCocone Stage T m)

theorem upperTailQCCRParameterToFullColimitMap_stage
    (m : ℕ) (j : UpperNatIndex m) (p : QCCRParameterSpace (Stage j.1)) :
    upperTailQCCRParameterToFullColimitMap Stage T m
        (qCcrParameterTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j p) =
      qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1 p := by
  have h := topologicalDirectDescend_stage
    (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
    (upperTailQCCRParameterToFullCocone Stage T m) j
  exact congrArg (fun f => f p) h

noncomputable def upperTailCuntzQCCRFullParameterColimitMap
    (m : ℕ) (i : Fin m) :
    topologicalDirectColimit
        ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem :=
  upperTailCuntzQCCRParameterColimitMap Stage T m i ≫
    upperTailQCCRParameterToFullColimitMap Stage T m

theorem upperTailCuntzQCCRFullParameterColimitMap_stage_apply
    (m : ℕ) (i : Fin m) (j : UpperNatIndex m) (u : PUnit) :
    upperTailCuntzQCCRFullParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (upperTailCuntzQCCRPoint Stage T m i j).1 := by
  have hupper := upperTailCuntzQCCRParameterColimitMap_stage_apply
    Stage T m i j u
  have hfull := upperTailQCCRParameterToFullColimitMap_stage
    Stage T m j (upperTailCuntzQCCRPoint Stage T m i j).1
  calc
    upperTailCuntzQCCRFullParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit)) j u) =
      upperTailQCCRParameterToFullColimitMap Stage T m
        (qCcrParameterTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j
          (upperTailCuntzQCCRPoint Stage T m i j).1) := by
        have h := congrArg
          (fun z => upperTailQCCRParameterToFullColimitMap Stage T m z) hupper
        simpa [upperTailCuntzQCCRFullParameterColimitMap] using h
    _ = qCcrParameterTopologicalInjection Stage T.toContinuousStarInductiveSystem j.1
        (upperTailCuntzQCCRPoint Stage T m i j).1 := by
        exact hfull

theorem upperTailCuntzQCCRFullParameterColimitMap_cutoff_compat
    (m n : ℕ) (hmn : m ≤ n) (i : Fin m)
    (j : UpperNatIndex n) (u : PUnit) :
    upperTailCuntzQCCRFullParameterColimitMap Stage T m i
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex m)).obj (TopCat.of PUnit))
          ⟨j.1, le_trans hmn j.2⟩ u) =
      upperTailCuntzQCCRFullParameterColimitMap Stage T n (Fin.castLE hmn i)
        (topologicalDirectInjection
          ((Functor.const (UpperNatIndex n)).obj (TopCat.of PUnit)) j u) := by
  have hm := upperTailCuntzQCCRFullParameterColimitMap_stage_apply
    Stage T m i ⟨j.1, le_trans hmn j.2⟩ u
  have hn := upperTailCuntzQCCRFullParameterColimitMap_stage_apply
    Stage T n (Fin.castLE hmn i) j u
  have hpoint :
      (upperTailCuntzQCCRPoint Stage T m i
        ⟨j.1, le_trans hmn j.2⟩).1 =
      (upperTailCuntzQCCRPoint Stage T n (Fin.castLE hmn i) j).1 := by
    apply Prod.ext
    · congr 1
    · apply Prod.ext
      · congr 1
      · rfl
  rw [hm, hn, hpoint]

theorem upperTailQCCRParameterToFullColimitMap_unique
    (m : ℕ)
    (f : qCcrParameterTopologicalColimit
        (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) ⟶
      qCcrParameterTopologicalColimit Stage T.toContinuousStarInductiveSystem)
    (hstage : ∀ j : UpperNatIndex m,
      qCcrParameterTopologicalInjection
          (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m) j ≫ f =
        (upperTailQCCRParameterToFullCocone Stage T m).ι.app j) :
    f = upperTailQCCRParameterToFullColimitMap Stage T m := by
  apply topologicalDirectDescend_unique
    (qCcrParameterTopologicalDiagram
      (UpperTailStage Stage m) (upperTailContinuousStarSystem Stage T m))
    (upperTailQCCRParameterToFullCocone Stage T m) f
  intro j
  exact hstage j

end InfoGeometry.Canonical.CuntzUpperTailQCCRColimitReadout
