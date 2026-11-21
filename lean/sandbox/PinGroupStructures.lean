/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
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
  toFun z := inversionAut G ^ z.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    have hinv : inversionAut G * inversionAut G = 1 := by
      ext g
      simp [inversionAut]
    change inversionAut G ^ (x.toAdd + y.toAdd).val =
      (inversionAut G ^ x.toAdd.val) * (inversionAut G ^ y.toAdd.val)
    rw [ZMod.val_add]
    have hx : x.toAdd.val < 2 := ZMod.val_lt x.toAdd
    have hy : y.toAdd.val < 2 := ZMod.val_lt y.toAdd
    interval_cases x.toAdd.val <;> interval_cases y.toAdd.val <;>
      norm_num [inversionAut, hinv]; try exact hinv.symm

end InfoGeometry.Topology.PinStructures
