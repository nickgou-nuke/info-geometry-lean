import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.GroupTheory.DoubleCosetOrbit

namespace InfoGeometry.Algebra.Zorn.G2BruhatCellIntersectionCard

open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.GroupTheory.DoubleCoset
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-!
The exact finite cardinality boundary for a concrete Bruhat cell.  The
remaining root-theoretic input is isolated in the cardinality of the
intersection subgroup; no automorphism enumeration occurs here.
-/

theorem concreteBruhatCell_card_mul_intersection_card
    (w : SplitOctF2Aut)
    [Fintype {x : SplitOctF2Aut //
      x ∈ concreteBruhatCell w}]
    [Fintype (MulAction.orbit
      (unipotentSubgroup × unipotentSubgroup) w)]
    [Fintype (MulAction.stabilizer
      (unipotentSubgroup × unipotentSubgroup) w)]
    [Fintype {x : SplitOctF2Aut //
      x ∈ doubleCoset unipotentSubgroup w unipotentSubgroup}]
    [Fintype (intersectionSubgroup unipotentSubgroup
      (conjugateSubgroup w unipotentSubgroup))] :
    Fintype.card {x : SplitOctF2Aut // x ∈ concreteBruhatCell w} *
    Fintype.card (intersectionSubgroup unipotentSubgroup
          (conjugateSubgroup w unipotentSubgroup)) = 4096 := by
  letI : Fintype unipotentSubgroup := Fintype.ofFinite _
  letI : Fintype SplitOctF2Aut := Fintype.ofFinite _
  have hdouble := doubleCoset_card_mul_intersection_card
    unipotentSubgroup unipotentSubgroup w
  have hcell : concreteBruhatCell w =
      doubleCoset unipotentSubgroup w unipotentSubgroup := by
    exact concreteBruhatCell_eq_exact_unipotentCell w
  have hcard : Fintype.card {x : SplitOctF2Aut //
      x ∈ concreteBruhatCell w} =
      Fintype.card {x : SplitOctF2Aut //
        x ∈ doubleCoset unipotentSubgroup w unipotentSubgroup} := by
    exact Fintype.card_congr (Equiv.setCongr hcell)
  rw [hcard]
  rw [hdouble]
  have hU : Fintype.card unipotentSubgroup = 64 := by
    simpa [Nat.card_eq_fintype_card] using unipotentSubgroup_card
  rw [hU]

theorem identity_intersectionSubgroup_eq_unipotentSubgroup :
    intersectionSubgroup unipotentSubgroup
        (conjugateSubgroup (1 : SplitOctF2Aut) unipotentSubgroup) =
      unipotentSubgroup := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, by simpa [conjugateSubgroup] using hx⟩

theorem identity_intersection_card :
    Nat.card (intersectionSubgroup unipotentSubgroup
      (conjugateSubgroup (1 : SplitOctF2Aut) unipotentSubgroup)) = 64 := by
  rw [identity_intersectionSubgroup_eq_unipotentSubgroup]
  exact unipotentSubgroup_card

theorem identity_bruhatCell_card
    [Fintype {x : SplitOctF2Aut //
      x ∈ concreteBruhatCell (1 : SplitOctF2Aut)}]
    [Fintype (MulAction.orbit
      (unipotentSubgroup × unipotentSubgroup) (1 : SplitOctF2Aut))]
    [Fintype (MulAction.stabilizer
      (unipotentSubgroup × unipotentSubgroup) (1 : SplitOctF2Aut))]
    [Fintype {x : SplitOctF2Aut //
      x ∈ doubleCoset unipotentSubgroup (1 : SplitOctF2Aut)
        unipotentSubgroup}] :
    Fintype.card {x : SplitOctF2Aut //
      x ∈ concreteBruhatCell (1 : SplitOctF2Aut)} = 64 := by
  letI : Fintype unipotentSubgroup := Fintype.ofFinite _
  letI : Fintype SplitOctF2Aut := Fintype.ofFinite _
  letI : Fintype (intersectionSubgroup unipotentSubgroup
      (conjugateSubgroup (1 : SplitOctF2Aut) unipotentSubgroup)) :=
    Fintype.ofFinite _
  have hprod := concreteBruhatCell_card_mul_intersection_card
    (1 : SplitOctF2Aut)
  have hI : Fintype.card (intersectionSubgroup unipotentSubgroup
      (conjugateSubgroup (1 : SplitOctF2Aut) unipotentSubgroup)) = 64 := by
    simpa [Nat.card_eq_fintype_card] using identity_intersection_card
  rw [hI] at hprod
  omega

end InfoGeometry.Algebra.Zorn.G2BruhatCellIntersectionCard
