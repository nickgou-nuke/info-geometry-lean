import Mathlib
import InfoGeometry.Topology.NativeZornChiralExchangeTopological

/-!
# The native chiral exchange is not a Zorn-product automorphism

`nativeChiralExchange` is an involutive topological sheet exchange.  The
native Zorn product contains an oriented cross-product term, so the exchange
cannot be promoted to an algebra automorphism without an additional
orientation/sign correction.  This owner records a concrete counterexample;
it prevents an unconditional `S₃` covariance claim from being inferred from
the already-proved dihedral readout relations.
-/

namespace InfoGeometry.Topology.NativeZornChiralExchangeTopological

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

noncomputable section

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
