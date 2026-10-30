/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.NativeZornChiralExchangeTopological

/-!
# The native chiral exchange reverses the Zorn product

`nativeChiralExchange` is an involutive topological sheet exchange.  The
native Zorn product contains an oriented cross-product term, so the exchange
is not multiplicative in the original order. The exact replacement is that it
is an involutive anti-automorphism: it sends `X * Y` to the exchanged product
in reverse order. This does not imply an unconditional `S₃` action on the
Zorn algebra from the dihedral readout relations alone.
-/

namespace InfoGeometry.Topology.NativeZornChiralExchangeTopological

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

noncomputable section

/-- The chiral sheet exchange reverses the order of the native Zorn product.
Thus its failure to be multiplicative is exactly explained by the opposite
product; it is an involutive anti-automorphism on this carrier. -/
theorem nativeChiralExchange_mul_reverse (X Y : Zorn) :
    nativeChiralExchange (X * Y) = nativeChiralExchange Y * nativeChiralExchange X := by
  ext <;>
    simp [nativeChiralExchange, mul, Vec3.dot, Vec3.cross, Vec3.add,
      Vec3.sub, Vec3.smul] <;>
    ring_nf

/-- The native sheet exchange is a multiplicative equivalence to the opposite
carrier. `MulEquiv` requires no associativity of the Zorn multiplication. -/
def nativeChiralExchangeMulOpposite : Zorn ≃* Zornᵐᵒᵖ where
  toFun X := MulOpposite.op (nativeChiralExchange X)
  invFun X := nativeChiralExchange (MulOpposite.unop X)
  left_inv X := nativeChiralExchange_square X
  right_inv X := by
    apply MulOpposite.unop_injective
    exact nativeChiralExchange_square (MulOpposite.unop X)
  map_mul' X Y := by
    apply MulOpposite.unop_injective
    exact nativeChiralExchange_mul_reverse X Y

/-- The proposed same-order product law is valid exactly on commuting pairs.
The unrestricted replacement is the opposite-product equivalence above. -/
theorem nativeChiralExchange_mul_iff_commute (X Y : Zorn) :
    nativeChiralExchange (X * Y) = nativeChiralExchange X * nativeChiralExchange Y ↔
      Commute X Y := by
  rw [← nativeChiralExchange_mul_reverse Y X]
  constructor
  · intro h
    have he := congrArg nativeChiralExchange h
    change X * Y = Y * X
    simpa only [nativeChiralExchange_square] using he
  · intro h
    exact congrArg nativeChiralExchange h.eq

theorem nativeChiralExchange_not_mul :
    nativeChiralExchange ((U (0 : Fin 3)) * U (1 : Fin 3)) ≠
      nativeChiralExchange (U (0 : Fin 3)) *
        nativeChiralExchange (U (1 : Fin 3)) := by
  intro h
  have hv := congrArg (fun X : Zorn => X.v 2) h
  simp [nativeChiralExchange, mul, U, Vec3.basis, Vec3.dot, Vec3.cross,
    Vec3.add, Vec3.sub, Vec3.smul] at hv
  norm_num at hv

end
end InfoGeometry.Topology.NativeZornChiralExchangeTopological
