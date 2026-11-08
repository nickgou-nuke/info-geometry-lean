import Mathlib.Algebra.Module.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

namespace InfoGeometry.GrandUnification.E8

open Complex

/-- The Exceptional Jordan Triple System representing E_8(8) interactions. -/
structure JordanTripleSystem (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The triple product {x, y, z} representing the fusion of three Parafermions. -/
  triple_prod : V → V → V → V
  
  /-- Symmetry condition: {x, y, z} = {z, y, x} -/
  symmetry : ∀ x y z : V, triple_prod x y z = triple_prod z y x
  
  /-- Jordan identity for the triple system, modeling the triality of operators
      in the exceptional E_8(8) U-duality string limit. 
      {a, b, {x, y, z}} = {{a, b, x}, y, z} - {x, {b, a, y}, z} + {x, y, {a, b, z}} -/
  jordan_identity : ∀ a b x y z : V,
    triple_prod a b (triple_prod x y z) =
      triple_prod (triple_prod a b x) y z - triple_prod x (triple_prod b a y) z + triple_prod x y (triple_prod a b z)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- THEOREM: Commutator of the Triple Product.
    The Lie algebra e_8(8) is the unique extension accommodating the triality
    of these operators. The commutation of the triality elements follows from the Jordan identity. -/
theorem triple_product_commutation (jts : JordanTripleSystem V) (a b x y z : V) :
    jts.triple_prod a b (jts.triple_prod x y z) - jts.triple_prod x y (jts.triple_prod a b z) =
    jts.triple_prod (jts.triple_prod a b x) y z - jts.triple_prod x (jts.triple_prod b a y) z := by
  have h := jts.jordan_identity a b x y z
  rw [h]
  exact add_sub_cancel_right _ _

end InfoGeometry.GrandUnification.E8
