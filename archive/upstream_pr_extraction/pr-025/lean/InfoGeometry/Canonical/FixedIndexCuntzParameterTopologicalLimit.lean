import InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
import InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
import InfoGeometry.Canonical.FixedIndexCuntzStarTower

/-!
# Fixed-index Cuntz generator readouts in q-CCR TopCat limits

The fixed-index tower supplies the actual finite-stage generator compatibility
law.  This owner transports each generator label through the generic direct and
inverse q-CCR limit interfaces; it does not assert a concrete varying-cutoff
representation.
-/

noncomputable section

namespace InfoGeometry.Canonical.FixedIndexCuntzParameterTopologicalLimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.OperatorAlgebra.QCCRResidual
open InfoGeometry.Canonical.CARCCRFockCuntzParameterTopologicalReadout
open InfoGeometry.Canonical.CStarCuntzCARCCRParameterTopCat
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalColimit
open InfoGeometry.Canonical.FilteredQCCRParameterTopologicalLimit
open InfoGeometry.Canonical.FixedIndexCuntzStarTower
open CStarStateColimit.Native
open FilteredColimit.Native.Topological

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Stage : ℕ → Type}
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]
variable (T : FixedIndexCuntzStarTower.Data (ι := ι) Stage)

/-- The q-CCR zero-fibre point carried by a fixed generator label at stage n. -/
def fixedIndexCuntzParameterPoint (i : ι) (n : ℕ) :
    TopCat.of PUnit ⟶
      TopCat.of {p : QCCRParameterSpace (Stage n) //
        p ∈ qCcrParameterZeroLocus (A := Stage n)} :=
  cstarCuntzParameterPointTopCatHom (T.family n) i

theorem fixedIndexCuntzParameterPoint_natural
    {m n : ℕ} (hmn : m ≤ n) (i : ι) :
    fixedIndexCuntzParameterPoint T i m ≫
        qCcrParameterZeroFiberTransitionTopCatHom Stage
          T.toContinuousStarInductiveSystem hmn =
      fixedIndexCuntzParameterPoint T i n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change qCcrParameterTransitionMap Stage
      T.toContinuousStarInductiveSystem hmn
      (cstarCuntzParameterPoint (T.family m) i) =
    cstarCuntzParameterPoint (T.family n) i
  simp [qCcrParameterTransitionMap, cstarCuntzParameterPoint,
    T.map_generator, map_star]

noncomputable def fixedIndexCuntzParameterPointLimitMap (i : ι) :
    TopCat.of PUnit ⟶
      qCcrParameterZeroFiberTopologicalLimit Stage
        T.toContinuousStarInductiveSystem :=
  qCcrParameterZeroFiberPointLimitMap Stage
    T.toContinuousStarInductiveSystem
    (fixedIndexCuntzParameterPoint T i)
    (by
      intro m n f
      exact fixedIndexCuntzParameterPoint_natural T (leOfHom f) i)

@[simp]
theorem fixedIndexCuntzParameterPointLimitMap_projection
    (i : ι) (n : ℕ) (u : PUnit) :
    topologicalInverseProjection
        (qCcrParameterZeroFiberTopologicalDiagram Stage
          T.toContinuousStarInductiveSystem) n
        (fixedIndexCuntzParameterPointLimitMap T i u) =
      fixedIndexCuntzParameterPoint T i n u := by
  exact qCcrParameterZeroFiberPointLimitMap_projection Stage
    T.toContinuousStarInductiveSystem (fixedIndexCuntzParameterPoint T i)
    (by
      intro m n f
      exact fixedIndexCuntzParameterPoint_natural T (leOfHom f) i) n u

noncomputable def fixedIndexCuntzParameterPointColimitMap (i : ι) :
    topologicalDirectColimit
        ((Functor.const ℕ).obj (TopCat.of PUnit)) ⟶
      qCcrParameterZeroFiberTopologicalColimit Stage
        T.toContinuousStarInductiveSystem :=
  qCcrParameterZeroFiberPointColimitMap Stage
    T.toContinuousStarInductiveSystem
    (fixedIndexCuntzParameterPoint T i)
    (by
      intro m n f
      exact fixedIndexCuntzParameterPoint_natural T (leOfHom f) i)

@[reassoc]
theorem fixedIndexCuntzParameterPointColimitMap_stage
    (i : ι) (n : ℕ) :
    topologicalDirectInjection ((Functor.const ℕ).obj (TopCat.of PUnit)) n ≫
        fixedIndexCuntzParameterPointColimitMap T i =
      (fixedIndexCuntzParameterPoint T i n) ≫
        qCcrParameterZeroFiberTopologicalInjection Stage
          T.toContinuousStarInductiveSystem n := by
  exact qCcrParameterZeroFiberPointColimitMap_stage Stage
    T.toContinuousStarInductiveSystem (fixedIndexCuntzParameterPoint T i)
    (by
      intro m n f
      exact fixedIndexCuntzParameterPoint_natural T (leOfHom f) i) n

noncomputable def fixedIndexCuntzParameterPointAmbientLimitMap (i : ι) :
    TopCat.of PUnit ⟶
      qCcrParameterTopologicalLimit Stage
        T.toContinuousStarInductiveSystem :=
  qCcrParameterZeroFiberPointAmbientLimitMap Stage
    T.toContinuousStarInductiveSystem
    (fixedIndexCuntzParameterPoint T i)
    (by
      intro m n f
      exact fixedIndexCuntzParameterPoint_natural T (leOfHom f) i)

@[simp]
theorem fixedIndexCuntzParameterPointAmbientLimitMap_projection
    (i : ι) (n : ℕ) (u : PUnit) :
    topologicalInverseProjection
        (qCcrParameterTopologicalDiagram Stage
          T.toContinuousStarInductiveSystem) n
        (fixedIndexCuntzParameterPointAmbientLimitMap T i u) =
      (qCcrParameterZeroFiberToParameterNatTrans Stage
        T.toContinuousStarInductiveSystem).app n
        (fixedIndexCuntzParameterPoint T i n u) := by
  exact qCcrParameterZeroFiberPointAmbientLimitMap_projection Stage
    T.toContinuousStarInductiveSystem (fixedIndexCuntzParameterPoint T i)
    (by
      intro m n f
      exact fixedIndexCuntzParameterPoint_natural T (leOfHom f) i) n u

noncomputable def fixedIndexCuntzParameterPointAmbientColimitMap (i : ι) :
    topologicalDirectColimit
        ((Functor.const ℕ).obj (TopCat.of PUnit)) ⟶
      qCcrParameterTopologicalColimit Stage
        T.toContinuousStarInductiveSystem :=
  qCcrParameterZeroFiberPointAmbientColimitMap Stage
    T.toContinuousStarInductiveSystem
    (fixedIndexCuntzParameterPoint T i)
    (by
      intro m n f
      exact fixedIndexCuntzParameterPoint_natural T (leOfHom f) i)

@[reassoc]
theorem fixedIndexCuntzParameterPointAmbientColimitMap_stage
    (i : ι) (n : ℕ) :
    topologicalDirectInjection ((Functor.const ℕ).obj (TopCat.of PUnit)) n ≫
        fixedIndexCuntzParameterPointAmbientColimitMap T i =
      (fixedIndexCuntzParameterPoint T i n) ≫
        (qCcrParameterZeroFiberToParameterNatTrans Stage
          T.toContinuousStarInductiveSystem).app n ≫
        qCcrParameterTopologicalInjection Stage
          T.toContinuousStarInductiveSystem n := by
  exact qCcrParameterZeroFiberPointAmbientColimitMap_stage Stage
    T.toContinuousStarInductiveSystem (fixedIndexCuntzParameterPoint T i)
    (by
      intro m n f
      exact fixedIndexCuntzParameterPoint_natural T (leOfHom f) i) n

end InfoGeometry.Canonical.FixedIndexCuntzParameterTopologicalLimit
