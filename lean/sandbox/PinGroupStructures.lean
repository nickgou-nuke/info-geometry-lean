import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

/-!
# Geometric Pin structures via Semidirect Products
-/

namespace InfoGeometry.Topology.PinStructures

/-- The canonical involution on any abelian group mapping $x \mapsto x^{-1}$. -/
def inversionAut (G : Type*) [CommGroup G] : MulAut G where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x
  map_mul' x y := mul_inv x y

/-- The $\mathbb{Z}_2$ action on a commutative group by inversion. -/
def z2InversionAction (G : Type*) [CommGroup G] : Multiplicative (ZMod 2) →* MulAut G where
  toFun z := if z = 1 then 1 else inversionAut G
  map_one' := by simp
  map_mul' x y := by
    fin_cases x <;> fin_cases y
    all_goals
      have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
      ext g
      norm_num [inversionAut, ← ofAdd_add, htwo]
      all_goals
        rw [if_pos htwo]
        simp

end InfoGeometry.Topology.PinStructures
