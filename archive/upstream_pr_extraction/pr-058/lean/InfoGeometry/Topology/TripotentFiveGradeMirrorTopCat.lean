import InfoGeometry.Topology.SymbolicLatentIndexedObservationFunctor

/-!
# `TopCat` mirror for the finite five-grade observation range

This owner specializes the generic indexed observation functor to the
five-grade mirror.  It records only the finite topological involution and
does not identify it with an operator-level or Clifford symmetry.
-/

namespace InfoGeometry.Topology.TripotentFiveGradeMirrorTopCat

open CategoryTheory
open InfoGeometry.Physics.Algebra
open InfoGeometry.Topology
open InfoGeometry.Topology.TripotentFiveGradeSymbolicLatent
open InfoGeometry.Topology.TripotentFiveGradeMirrorTopological

noncomputable section

local instance : TopologicalSpace FiveGrade := ⊥
local instance : DiscreteTopology FiveGrade := discreteTopology_bot FiveGrade

abbrev fiveGradeObservationQuotientRangeTopCat : TopCat :=
  TopCat.of (Set.range
    (symbolicObservationQuotientMap (X := FiveGrade) (ι := FiveGrade)
      fiveGradeSystem))

def fiveGradeIndexedMirrorTopCatIso :
    fiveGradeObservationQuotientRangeTopCat ≅
      fiveGradeObservationQuotientRangeTopCat :=
  indexedObservationQuotientRangeTopCatIso (ι := FiveGrade)
    fiveGradeIndexedMirror

theorem fiveGradeIndexedMirrorTopCatIso_apply
    (y : Set.range
      (symbolicObservationQuotientMap (X := FiveGrade) (ι := FiveGrade)
        fiveGradeSystem)) :
    (fiveGradeIndexedMirrorTopCatIso.hom y).1 =
      indexedCoordinateAction fiveGradeIndexedMirror y.1 := rfl

theorem fiveGradeIndexedMirrorTopCatIso_involutive :
    (fiveGradeIndexedMirrorTopCatIso :
      fiveGradeObservationQuotientRangeTopCat ≅
        fiveGradeObservationQuotientRangeTopCat).hom ≫
        (fiveGradeIndexedMirrorTopCatIso :
          fiveGradeObservationQuotientRangeTopCat ≅
            fiveGradeObservationQuotientRangeTopCat).hom =
      𝟙 fiveGradeObservationQuotientRangeTopCat := by
  apply TopCat.hom_ext
  ext y k
  cases k <;> rfl

theorem fiveGradeIndexedMirrorTopCatIso_inv_eq_hom :
    (fiveGradeIndexedMirrorTopCatIso :
      fiveGradeObservationQuotientRangeTopCat ≅
        fiveGradeObservationQuotientRangeTopCat).inv =
      (fiveGradeIndexedMirrorTopCatIso :
        fiveGradeObservationQuotientRangeTopCat ≅
          fiveGradeObservationQuotientRangeTopCat).hom := by
  apply TopCat.hom_ext
  ext y k
  cases k <;> rfl

end

end InfoGeometry.Topology.TripotentFiveGradeMirrorTopCat
