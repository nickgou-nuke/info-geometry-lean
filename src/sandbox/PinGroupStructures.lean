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

private lemma zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have ha : a.val < 2 := a.val_lt
  interval_cases hv : a.val
  · left
    rw [← ZMod.natCast_zmod_val a, hv]
    norm_num
  · right
    rw [← ZMod.natCast_zmod_val a, hv]
    norm_num

private lemma inversionAut_sq (G : Type*) [CommGroup G] :
    inversionAut G * inversionAut G = 1 := by
  ext g
  simp [inversionAut]

/-- The $\mathbb{Z}_2$ action on a commutative group by inversion. -/
def z2InversionAction (G : Type*) [CommGroup G] : Multiplicative (ZMod 2) →* MulAut G where
  toFun z := if z.toAdd = 0 then 1 else inversionAut G
  map_one' := by simp
  map_mul' x y := by
    let a := x.toAdd
    let b := y.toAdd
    change (if a + b = 0 then 1 else inversionAut G) =
      (if a = 0 then 1 else inversionAut G) *
        (if b = 0 then 1 else inversionAut G)
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    have h11 : (1 : ZMod 2) + 1 = 0 := by
      calc (1 : ZMod 2) + 1 = (2 : ZMod 2) := by norm_num
        _ = 0 := htwo
    rcases zmodTwo_eq_zero_or_one a with ha | ha <;>
      rcases zmodTwo_eq_zero_or_one b with hb | hb
    all_goals simp [ha, hb, h11, inversionAut_sq]

end InfoGeometry.Topology.PinStructures
