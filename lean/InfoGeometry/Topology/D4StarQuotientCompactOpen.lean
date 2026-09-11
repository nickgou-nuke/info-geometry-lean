import InfoGeometry.Topology.D4StarQuotientSeparation
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-! Finite and compact consequences of the two-class quotient. -/

instance d4StarQuotientFinite : Finite D4StarQuotient := by
  apply Finite.of_injective quotientToBool
  intro q r h
  exact d4StarQuotientEquivBool.injective h

instance d4StarQuotientCompactSpace : CompactSpace D4StarQuotient :=
  ⟨Set.finite_univ.isCompact⟩

theorem d4StarQuotient_isCompact_univ :
    IsCompact (Set.univ : Set D4StarQuotient) :=
  Set.finite_univ.isCompact

def centreClass : Set D4StarQuotient :=
  {q | q = starQuotientMap centralVertex}

def outerClass : Set D4StarQuotient :=
  {q | q = starQuotientMap (outerVertex ColorChannel.red)}

theorem centreClass_nonempty : (centreClass : Set D4StarQuotient).Nonempty :=
  ⟨starQuotientMap centralVertex, rfl⟩

theorem outerClass_nonempty : (outerClass : Set D4StarQuotient).Nonempty :=
  ⟨starQuotientMap (outerVertex ColorChannel.red), rfl⟩

theorem centreClass_disjoint_outerClass :
    Disjoint centreClass outerClass := by
  rw [Set.disjoint_left]
  intro q hcentre houter
  have h : starQuotientMap centralVertex =
      starQuotientMap (outerVertex ColorChannel.red) :=
    hcentre.symm.trans houter
  exact centre_not_outer_class ColorChannel.red h

theorem centreClass_compact : IsCompact centreClass := by
  exact (Set.toFinite {starQuotientMap centralVertex}).isCompact

theorem outerClass_compact : IsCompact outerClass := by
  exact (Set.toFinite {starQuotientMap (outerVertex ColorChannel.red)}).isCompact

end InfoGeometry.Topology.PauliJungD4Star
