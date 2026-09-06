import InfoGeometry.Core.Foundations
import InfoGeometry.Algebra.Zorn.G2ConcreteGeneratorInfrastructure

/-!
# Stabilizer lift for the concrete `G₂(2)` Bruhat covering

The Borel and simple-reflection invariance facts are kept separate.  The
former uses subgroup inverses; the latter uses the involutivity of the two
concrete Weyl generators.  Global exhaustion remains conditional on the
independent generation theorem for the ambient automorphism group.
-/

namespace InfoGeometry.Algebra.Zorn.G2ConcreteBruhatExhaustion

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteGeneratorInfrastructure
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

theorem borel_mem_leftStabilizer
    {b : SplitOctF2Aut} (hb : b ∈ unipotentSubgroup) :
    b ∈ InfoGeometry.Foundations.leftStabilizer
      (concreteBruhatCovering : Set SplitOctF2Aut) := by
  intro g
  constructor
  · intro hg
    exact concreteBruhatCovering_left_mul_borel b hb hg
  · intro hbg
    have hbinv : b⁻¹ ∈ unipotentSubgroup :=
      unipotentSubgroup.inv_mem hb
    have h := concreteBruhatCovering_left_mul_borel b⁻¹ hbinv hbg
    simpa [mul_assoc] using h

theorem simpleReflection_mem_leftStabilizer_of_transition
    (h : ConcreteBN2Transition)
    {r : SplitOctF2Aut}
    (hr : r ∈ ({s, t} : Set SplitOctF2Aut)) :
    r ∈ InfoGeometry.Foundations.leftStabilizer
      (concreteBruhatCovering : Set SplitOctF2Aut) := by
  apply InfoGeometry.Foundations.mem_leftStabilizer_of_involution_mapsTo
  · rcases hr with rfl | rfl
    · exact s_sq
    · exact t_sq
  · intro g hg
    exact concreteBruhatCovering_left_mul_simple_of_transition h r hr hg

theorem concreteBNGenerators_le_leftStabilizer
    (h : ConcreteBN2Transition) :
    ((unipotentSubgroup : Set SplitOctF2Aut) ∪
      ({s, t} : Set SplitOctF2Aut)) ⊆
      InfoGeometry.Foundations.leftStabilizer
        (concreteBruhatCovering : Set SplitOctF2Aut) := by
  intro x hx
  rcases hx with hxB | hxW
  · exact borel_mem_leftStabilizer hxB
  · exact simpleReflection_mem_leftStabilizer_of_transition h hxW

theorem concreteBNGeneratorSubgroup_subset_bruhatCovering
    (htrans : ConcreteBN2Transition) :
    (concreteBNGeneratorSubgroup : Set SplitOctF2Aut) ⊆
      concreteBruhatCovering := by
  apply InfoGeometry.Foundations.closure_subset_of_leftStabilizer
    concreteBruhatCovering
  · apply mem_concreteBruhatCovering_of_cell (0, false)
    rw [weylNF_zero_false, concreteBruhatCell_one_eq_sylow]
    exact Subgroup.one_mem _
  · exact concreteBNGenerators_le_leftStabilizer htrans

theorem concreteBruhatCovering_eq_univ
    (htrans : ConcreteBN2Transition)
    (hgen : Subgroup.closure
      ((unipotentSubgroup : Set SplitOctF2Aut) ∪
        ({s, t} : Set SplitOctF2Aut)) = ⊤) :
    concreteBruhatCovering = Set.univ := by
  apply InfoGeometry.Foundations.tits_exhaustion_of_closure_top
    (concreteBruhatCovering : Set SplitOctF2Aut)
  · apply mem_concreteBruhatCovering_of_cell (0, false)
    simpa [weylNF_zero_false, concreteBruhatCell_one_eq_sylow] using
      (unipotentSubgroup.one_mem :
        (1 : SplitOctF2Aut) ∈ unipotentSubgroup)
  · exact hgen
  · exact concreteBNGenerators_le_leftStabilizer htrans

end InfoGeometry.Algebra.Zorn.G2ConcreteBruhatExhaustion
