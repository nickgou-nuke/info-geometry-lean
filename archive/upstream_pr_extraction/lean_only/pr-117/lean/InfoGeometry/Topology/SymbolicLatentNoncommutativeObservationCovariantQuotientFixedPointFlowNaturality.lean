import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantQuotientFixedPointFlowCompHaus

/-!
# Naturality of fixed-point inclusions

The fixed-point restriction is the ambient quotient flow viewed through its
closed invariant subtype.  This owner records the resulting naturality
square in `CompHaus`.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

theorem operatorObservationQuotientCovariantFixedPointFlow_naturality
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S)
    (fixedTime s : ℝ) :
    operatorObservationQuotientCovariantFixedPointInclusion Φ fixedTime ≫
        operatorObservationQuotientCompHausCovariantFlowHom Φ s =
      operatorObservationQuotientCovariantFixedPointFlowHom Φ fixedTime s ≫
        operatorObservationQuotientCovariantFixedPointInclusion Φ fixedTime := by
  apply ConcreteCategory.hom_ext
  intro q
  change descendedCovariantOperatorObservationFlow Φ s q.1 =
    descendedCovariantOperatorObservationFlow Φ s q.1
  rfl

end InfoGeometry.Topology
