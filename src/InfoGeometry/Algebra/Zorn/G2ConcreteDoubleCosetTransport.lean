import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.Zorn.G2ConcreteDoubleCosetTransport

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

/-! Concrete transport inside a fixed Bruhat double coset. -/

theorem concreteBruhatCell_mul_borel
    (w g b₁ b₂ : SplitOctF2Aut)
    (hb₁ : b₁ ∈ sylowTwoSubgroup)
    (hb₂ : b₂ ∈ sylowTwoSubgroup)
    (hg : g ∈ concreteBruhatCell w) :
    b₁ * g * b₂ ∈ concreteBruhatCell w := by
  exact concreteBruhatCell_right_mul w b₂ (b₁ * g) hb₂
    (concreteBruhatCell_left_mul w b₁ g hb₁ hg)

theorem simple_reflection_mul_identity_cell
    (r : SplitOctF2Aut) (hr : r ∈ ({s, t} : Set SplitOctF2Aut))
    (g : SplitOctF2Aut)
    (hg : g ∈ concreteBruhatCell 1) :
    r * g ∈ concreteBruhatCell (r * 1) := by
  have hrg : r = s ∨ r = t := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hr
  have hgB : g ∈ sylowTwoSubgroup := by
    have hcell : concreteBruhatCell 1 =
        (sylowTwoSubgroup : Set SplitOctF2Aut) :=
      concreteBruhatCell_one_eq_sylow
    change g ∈ (sylowTwoSubgroup : Set SplitOctF2Aut)
    rw [← hcell]
    exact hg
  rcases hrg with rfl | rfl
  · simpa only [_root_.mul_one] using simple_reflection_s_mul_borel g hgB
  · simpa only [_root_.mul_one] using simple_reflection_t_mul_borel g hgB

end InfoGeometry.Algebra.Zorn.G2ConcreteDoubleCosetTransport
