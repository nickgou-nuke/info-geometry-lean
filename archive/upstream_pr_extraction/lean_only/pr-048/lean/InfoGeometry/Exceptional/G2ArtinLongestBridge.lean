import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import Mathlib.Tactic

/-!
# G₂ Artin / longest-element bridge

This owner exposes the theorem-safe relation between the concrete split-octonion
Weyl automorphisms and the Artin system of Coxeter type `G₂ = I₂(6)`.

It deliberately does **not** introduce a homomorphism from the ordinary
three-strand braid group `B₃`: the standard Artin relation of `B₃` has length
three, while the `G₂` simple reflections satisfy the length-six relation

`ststst = tststs`.

The concrete repository already proves this six-braid relation, the Coxeter
element `c = st` of order six, and `c^3 = swapCartanAut`.  We package
`w₀ := c^3` as the longest Weyl element and record its involutivity and its
explicit chiral-sheet swap on a basis vector.
-/

noncomputable section

namespace InfoGeometry.Exceptional.G2ArtinLongestBridge

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- The concrete Coxeter product of the two simple `G₂` reflections. -/
theorem simple_reflection_product_eq_coxeter : s * t = c := by
  dsimp [t]
  calc
    s * (s * c) = (s * s) * c := by simp [mul_assoc]
    _ = 1 * c := by rw [s_sq]
    _ = c := by simp

/-- The longest element in the concrete `G₂` Weyl realization. -/
noncomputable def longestElement : SplitOctF2Aut := c ^ 3

/-- The longest element is exactly the Cartan/chiral swap already present in
split-octonion automorphism infrastructure. -/
theorem longestElement_eq_swapCartan :
    longestElement = swapCartanAut := by
  exact c_pow_three_eq_swapCartan

/-- The longest Weyl element has order dividing two. -/
theorem longestElement_sq :
    longestElement * longestElement = 1 := by
  calc
    longestElement * longestElement = c ^ 3 * c ^ 3 := rfl
    _ = c ^ 6 := by rw [← pow_add]
    _ = 1 := c_pow_six

/-- `w₀` is nontrivial. -/
theorem longestElement_ne_one : longestElement ≠ 1 := by
  simpa [longestElement] using c_pow_three_ne_one

/-- The concrete longest element is the cube of the Coxeter product `(st)`. -/
theorem longestElement_eq_st_cube :
    longestElement = (s * t) ^ 3 := by
  rw [simple_reflection_product_eq_coxeter]
  rfl

/-- Readback of the native six-term Artin relation for the `G₂` simple
reflections. -/
theorem g2_artin_six_relation :
    s * t * s * t * s * t = t * s * t * s * t * s :=
  st_artin_braid_relation

/-- The longest element exchanges one explicit positive/negative root-basis
pair.  This is an algebraic chiral-sheet swap theorem, not a CPT or Tomita
identification. -/
theorem longestElement_up0 :
    longestElement.1 up0 = down0 := by
  exact c_cube_up0

end InfoGeometry.Exceptional.G2ArtinLongestBridge
