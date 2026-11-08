import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/-!
# Concrete Bruhat index transport

This owner exposes the operational invariant needed by the PC peeling
pipeline: multiplying an element of a concrete Bruhat cell on either side by
a verified PC word keeps it in that same cell.  It deliberately does not
define a global index function or assert pairwise cell disjointness.
-/

namespace InfoGeometry.Algebra.Zorn.G2BruhatIndexTransport

open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem pcWord_mem_sylow (e : PCWordExp) :
    G2TwoSylowSubgroup.pcWord e ∈ sylowTwoSubgroup := by
  exact G2TwoSylowSubgroup.pcWord_mem_sylow e

theorem pcWord_left_right_preserves_cell
    (p : WeylG2) (g : SplitOctF2Aut)
    (hg : g ∈ concreteBruhatCell (weylNF p.1 p.2))
    (a d : PCWordExp) :
    G2TwoSylowSubgroup.pcWord a * g *
        G2TwoSylowSubgroup.pcWord d ∈
      concreteBruhatCell (weylNF p.1 p.2) := by
  have hleft :
      G2TwoSylowSubgroup.pcWord a * g ∈
        concreteBruhatCell (weylNF p.1 p.2) :=
    concreteBruhatCell_left_mul
      (weylNF p.1 p.2)
      (G2TwoSylowSubgroup.pcWord a) g
      (pcWord_mem_sylow a) hg
  exact concreteBruhatCell_right_mul
    (weylNF p.1 p.2)
    (G2TwoSylowSubgroup.pcWord d)
    (G2TwoSylowSubgroup.pcWord a * g)
    (pcWord_mem_sylow d) hleft

theorem pcWord_two_sided_preserves_indexed_cell
    (p : WeylG2) (g : SplitOctF2Aut)
    (hg : g ∈ concreteBruhatCell (weylNF p.1 p.2))
    {uL uR : SplitOctF2Aut}
    (huL : uL ∈ sylowTwoSubgroup)
    (huR : uR ∈ sylowTwoSubgroup) :
    uL * g * uR ∈ concreteBruhatCell (weylNF p.1 p.2) := by
  have hleft : uL * g ∈ concreteBruhatCell (weylNF p.1 p.2) :=
    concreteBruhatCell_left_mul
      (weylNF p.1 p.2) uL g huL hg
  exact concreteBruhatCell_right_mul
    (weylNF p.1 p.2) uR (uL * g) huR hleft

theorem bruhatIndex_left_right_pc_invariant
    (g : SplitOctF2Aut) (p : WeylG2)
    (hg : g ∈ concreteBruhatCell (weylNF p.1 p.2))
    {uL uR : SplitOctF2Aut}
    (huL : uL ∈ sylowTwoSubgroup)
    (huR : uR ∈ sylowTwoSubgroup) :
    uL * g * uR ∈ concreteBruhatCell (weylNF p.1 p.2) :=
  pcWord_two_sided_preserves_indexed_cell p g hg huL huR

end InfoGeometry.Algebra.Zorn.G2BruhatIndexTransport
