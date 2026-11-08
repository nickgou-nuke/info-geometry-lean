import Mathlib.Topology.Order.HullKernel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.Meta.BridgeTarget

/-!
# InfoGeometry.Arithmetic.PrimitiveSetHullKernelBridge

Bridge between the repo's primitive-set predicate and Mathlib's
hull-kernel Galois connection.

This file does not prove a new primitive-set theorem. It specializes the
already-proved `PrimitiveSpectrum.gc` to the carrier set of primitive supports
and records the resulting closure operator. The primitive-set content stays in
`PrimitiveSetsAbove`; the order-theoretic hull/kernel content stays in Mathlib.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimitiveSetHullKernelBridge

open OrderDual
open PrimitiveSpectrum
open InfoGeometry.Arithmetic

/-- The carrier set of primitive supports inside `Set ℕ`. -/
def PrimitiveSetCarrier : Set (Set ℕ) := {A | PrimitiveSet A}

/--
The family of primitive support sets can be used as the carrier set `T` in
Mathlib's hull-kernel Galois connection.

This is a direct specialization of `PrimitiveSpectrum.gc`; the bridge is the
carrier-level instantiation, not a new theorem.
-/
@[bridge_target_tag]
theorem primitiveSetCarrier_hullKernel_gc :
    GaloisConnection
      (fun S : Set PrimitiveSetCarrier =>
        OrderDual.toDual (PrimitiveSpectrum.kernel (T := PrimitiveSetCarrier) S))
      (fun a : (Set ℕ)ᵒᵈ =>
        PrimitiveSpectrum.hull PrimitiveSetCarrier (OrderDual.ofDual a)) := by
  simpa [PrimitiveSetCarrier] using
    (PrimitiveSpectrum.gc (α := Set ℕ) (T := PrimitiveSetCarrier))

/--
The hull-kernel closure operator specialized to the primitive support
carrier.

This is the closure side of the same Galois connection.
-/
@[bridge_target_tag]
theorem primitiveSetCarrier_hullKernel_closureOperator
    (S : Set PrimitiveSetCarrier) :
    (PrimitiveSpectrum.gc (α := Set ℕ) (T := PrimitiveSetCarrier)).closureOperator S
      = PrimitiveSpectrum.hull PrimitiveSetCarrier
          (PrimitiveSpectrum.kernel (T := PrimitiveSetCarrier) S) := by
  simpa [PrimitiveSetCarrier] using
    (PrimitiveSpectrum.gc_closureOperator (T := PrimitiveSetCarrier) S)

end InfoGeometry.Arithmetic.PrimitiveSetHullKernelBridge
