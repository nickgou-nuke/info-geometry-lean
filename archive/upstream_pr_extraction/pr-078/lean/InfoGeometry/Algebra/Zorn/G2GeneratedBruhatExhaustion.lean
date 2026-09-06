import InfoGeometry.Core.TitsExhaustion
import InfoGeometry.Algebra.Zorn.G2ConcreteGeneratorInfrastructure

/-! Non-circular Bruhat exhaustion for the concrete generated subgroup. -/

namespace InfoGeometry.Algebra.Zorn.G2GeneratedBruhatExhaustion

open InfoGeometry.Foundations
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2ConcreteGeneratorInfrastructure

theorem unipotent_mem_covering_leftStabilizer
    {b : SplitOctF2Aut} (hb : b ∈ unipotentSubgroup) :
    b ∈ leftStabilizer concreteBruhatCovering := by
  intro g
  constructor
  · intro hg
    exact concreteBruhatCovering_left_mul_borel b hb hg
  · intro hbg
    have hbinv : b⁻¹ ∈ unipotentSubgroup := unipotentSubgroup.inv_mem hb
    have h := concreteBruhatCovering_left_mul_borel b⁻¹ hbinv hbg
    simpa [mul_assoc] using h

theorem simpleReflection_mem_covering_leftStabilizer
    (htrans : ConcreteBN2Transition) {r : SplitOctF2Aut}
    (hr : r ∈ ({s, t} : Set SplitOctF2Aut)) :
    r ∈ leftStabilizer concreteBruhatCovering := by
  have hsq : r * r = 1 := by
    rcases hr with rfl | rfl
    · exact s_sq
    · exact t_sq
  apply InfoGeometry.Foundations.mem_leftStabilizer_of_involutive_left_invariant
    concreteBruhatCovering hsq
  intro g hg
  exact concreteBruhatCovering_left_mul_simple_of_transition htrans r hr hg

theorem concreteBNGenerators_mem_covering_leftStabilizer
    (htrans : ConcreteBN2Transition) :
    ((unipotentSubgroup : Set SplitOctF2Aut) ∪ ({s, t} : Set SplitOctF2Aut)) ⊆
      leftStabilizer concreteBruhatCovering := by
  intro x hx
  rcases hx with hxU | hxW
  · exact unipotent_mem_covering_leftStabilizer hxU
  · exact simpleReflection_mem_covering_leftStabilizer htrans hxW

theorem one_mem_concreteBruhatCovering :
    (1 : SplitOctF2Aut) ∈ concreteBruhatCovering := by
  apply Set.mem_iUnion.mpr
  refine ⟨(0, false), ?_⟩
  simpa [weylNF_zero_false] using weyl_mem_concreteBruhatCell (1 : SplitOctF2Aut)

theorem concreteBNGeneratorSubgroup_subset_bruhatCovering
    (htrans : ConcreteBN2Transition) :
    (concreteBNGeneratorSubgroup : Set SplitOctF2Aut) ⊆ concreteBruhatCovering := by
  have hclosure :
      (Subgroup.closure
        ((unipotentSubgroup : Set SplitOctF2Aut) ∪ ({s, t} : Set SplitOctF2Aut)) :
        Set SplitOctF2Aut) ⊆ concreteBruhatCovering :=
    closure_subset_of_leftStabilizer concreteBruhatCovering
      one_mem_concreteBruhatCovering
      ((unipotentSubgroup : Set SplitOctF2Aut) ∪ ({s, t} : Set SplitOctF2Aut))
      (concreteBNGenerators_mem_covering_leftStabilizer htrans)
  simpa [concreteBNGeneratorSubgroup] using hclosure

theorem mem_concreteBruhatCovering_of_mem_concreteBNGeneratorSubgroup
    (htrans : ConcreteBN2Transition) {g : SplitOctF2Aut}
    (hg : g ∈ concreteBNGeneratorSubgroup) : g ∈ concreteBruhatCovering :=
  concreteBNGeneratorSubgroup_subset_bruhatCovering htrans hg

theorem concreteBruhatCovering_eq_univ_of_generator_top
    (htrans : ConcreteBN2Transition)
    (hgen : concreteBNGeneratorSubgroup = ⊤) :
    concreteBruhatCovering = Set.univ := by
  ext g
  simp only [Set.mem_univ, iff_true]
  apply concreteBNGeneratorSubgroup_subset_bruhatCovering htrans
  rw [hgen]
  exact Subgroup.mem_top g

end InfoGeometry.Algebra.Zorn.G2GeneratedBruhatExhaustion
