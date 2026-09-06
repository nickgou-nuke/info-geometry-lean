import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact commuting loci for operator-valued observations

For a compact latent carrier, the closed locus on which all retained operator
observables commute is itself a compact Hausdorff carrier.  This is a
topological packaging of the existing noncommutative observation theorem; it
does not collapse operator values to scalar features.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [Fintype ι]

theorem isCompact_operatorCommutingLocus
    (S : NoncommutativeObservableSystem X A ι) :
    IsCompact (operatorCommutingLocus S) := by
  exact (isClosed_operatorCommutingLocus S).isCompact

noncomputable def operatorCommutingLocusCompHaus
    (S : NoncommutativeObservableSystem X A ι) : CompHaus := by
  letI : CompactSpace {x : X // x ∈ operatorCommutingLocus S} :=
    isCompact_iff_compactSpace.mp (isCompact_operatorCommutingLocus S)
  exact CompHaus.of {x : X // x ∈ operatorCommutingLocus S}

noncomputable def operatorCommutingLocusCompHausInclusion
    (S : NoncommutativeObservableSystem X A ι) :
    operatorCommutingLocusCompHaus S ⟶ CompHaus.of X := by
  letI : CompactSpace {x : X // x ∈ operatorCommutingLocus S} :=
    isCompact_iff_compactSpace.mp (isCompact_operatorCommutingLocus S)
  change CompHaus.of {x : X // x ∈ operatorCommutingLocus S} ⟶ CompHaus.of X
  exact ⟨TopCat.ofHom
    { toFun := Subtype.val
      continuous_toFun := continuous_subtype_val }⟩

theorem operatorCommutingLocusCompHausInclusion_apply
    (S : NoncommutativeObservableSystem X A ι)
    (x : {x : X // x ∈ operatorCommutingLocus S}) :
    operatorCommutingLocusCompHausInclusion S x = x.1 := by
  change x.1 = x.1
  rfl

end InfoGeometry.Topology

end
