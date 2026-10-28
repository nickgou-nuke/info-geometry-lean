/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus

/-!
# Complete Lie--Jordan composition octet and cyclic trace duality

The five existing boundary identities are reused. This module supplies the
remaining three identities and the signed readouts. All equalities are in
`Module.End R A`; coefficients in `A` are never assumed to commute. Neither
sandwich action is called a positive or normalized quantum channel here.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanOctet

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The other order of the mixed symmetric composition. -/
theorem lie_jordan_sum (u v : A) :
    LieAlgebra.ad R A u * jordanLeft (R := R) v +
      LieAlgebra.ad R A v * jordanLeft (R := R) u =
        LieAlgebra.ad R A (u * v + v * u) := by
  ext x
  change (u * (v * x + x * v) - (v * x + x * v) * u) +
    (v * (u * x + x * u) - (u * x + x * u) * v) =
    (u * v + v * u) * x - x * (u * v + v * u)
  noncomm_ring

/-- The pure Jordan difference is an inner derivation. -/
theorem jordan_jordan_difference (u v : A) :
    jordanLeft (R := R) u * jordanLeft (R := R) v -
      jordanLeft (R := R) v * jordanLeft (R := R) u =
        LieAlgebra.ad R A (u * v - v * u) := by
  ext x
  exact InfoGeometry.Core.JordanMultiplicationClosure.commutator_apply u v x

/-- Reversing the mixed order reverses the signed sandwich correction. -/
theorem jordan_lie_difference (u v : A) :
    jordanLeft (R := R) u * LieAlgebra.ad R A v -
      jordanLeft (R := R) v * LieAlgebra.ad R A u =
        jordanLeft (R := R) (u * v - v * u) -
          2 • orientedTransport (R := R) u v := by
  ext x
  change (u * (v * x - x * v) + (v * x - x * v) * u) -
    (v * (u * x - x * u) + (u * x - x * u) * v) =
    (u * v - v * u) * x + x * (u * v - v * u) -
      2 • (u * x * v - v * x * u)
  simp only [two_nsmul]
  noncomm_ring

/-- A division-free extraction of Jordan multiplication by the symmetric product. -/
theorem twice_symmetric_jordan_readout (u v : A) :
    (jordanLeft (R := R) u * jordanLeft (R := R) v +
      jordanLeft (R := R) v * jordanLeft (R := R) u) +
    (LieAlgebra.ad R A u * LieAlgebra.ad R A v +
      LieAlgebra.ad R A v * LieAlgebra.ad R A u) =
        2 • jordanLeft (R := R) (u * v + v * u) := by
  rw [jordan_jordan_sum, lie_lie_sum]
  simp only [two_nsmul]
  abel

/-- A division-free extraction of Jordan multiplication by the commutator. -/
theorem twice_skew_jordan_readout (u v : A) :
    (LieAlgebra.ad R A u * jordanLeft (R := R) v -
      LieAlgebra.ad R A v * jordanLeft (R := R) u) +
    (jordanLeft (R := R) u * LieAlgebra.ad R A v -
      jordanLeft (R := R) v * LieAlgebra.ad R A u) =
        2 • jordanLeft (R := R) (u * v - v * u) := by
  rw [lie_jordan_difference, jordan_lie_difference]
  simp only [two_nsmul]
  abel

/-- The signed action is recoverable up to multiplication by four over any base. -/
theorem fourfold_oriented_readout (u v : A) :
    (LieAlgebra.ad R A u * jordanLeft (R := R) v -
      LieAlgebra.ad R A v * jordanLeft (R := R) u) -
    (jordanLeft (R := R) u * LieAlgebra.ad R A v -
      jordanLeft (R := R) v * LieAlgebra.ad R A u) =
        (4 : ℕ) • orientedTransport (R := R) u v := by
  rw [lie_jordan_difference, jordan_lie_difference]
  simp only [show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul]
  abel

@[simp] theorem orientedTransport_one (u v : A) :
    orientedTransport (R := R) u v 1 = u * v - v * u := by
  simp only [orientedTransport_apply, mul_one]

theorem crossTransport_exchange (u v : A) :
    crossTransport (R := R) v u = crossTransport (R := R) u v := by
  ext x
  change v * x * u + u * x * v = u * x * v + v * x * u
  exact add_comm _ _

theorem orientedTransport_exchange (u v : A) :
    orientedTransport (R := R) v u = -orientedTransport (R := R) u v := by
  ext x
  change v * x * u - u * x * v = -(u * x * v - v * x * u)
  abel

section Trace

variable {G : Type*} [AddCommGroup G]
variable (tau : A →+ G) (hcyc : ∀ a b : A, tau (a * b) = tau (b * a))

include hcyc

/-- The minus sign in the signed trace readout follows from cyclicity alone. -/
theorem trace_orientedTransport (u v x : A) :
    tau (orientedTransport (R := R) u v x) = -tau ((u * v - v * u) * x) := by
  simp only [orientedTransport_apply, sub_mul, map_sub]
  have hu : tau (u * x * v) = tau (v * u * x) := by
    rw [hcyc (u * x) v, ← mul_assoc]
  have hv : tau (v * x * u) = tau (u * v * x) := by
    rw [hcyc (v * x) u, ← mul_assoc]
  rw [hu, hv]
  abel

/-- Symmetry is for the cyclic bilinear pairing, not a Hilbert adjoint claim. -/
theorem cross_trace_duality (u v x y : A) :
    tau (crossTransport (R := R) u v x * y) =
      tau (x * crossTransport (R := R) u v y) := by
  have hu : tau (u * x * v * y) = tau (x * (v * y * u)) := by
    calc
      _ = tau (u * (x * (v * y))) := by simp only [mul_assoc]
      _ = tau ((x * (v * y)) * u) := hcyc _ _
      _ = _ := by simp only [mul_assoc]
  have hv : tau (v * x * u * y) = tau (x * (u * y * v)) := by
    calc
      _ = tau (v * (x * (u * y))) := by simp only [mul_assoc]
      _ = tau ((x * (u * y)) * v) := hcyc _ _
      _ = _ := by simp only [mul_assoc]
  simp only [crossTransport_apply, add_mul, mul_add, map_add]
  rw [hu, hv, add_comm]

/-- The signed action is skew for the same cyclic pairing. -/
theorem oriented_trace_duality (u v x y : A) :
    tau (orientedTransport (R := R) u v x * y) =
      -tau (x * orientedTransport (R := R) u v y) := by
  have hu : tau (u * x * v * y) = tau (x * (v * y * u)) := by
    calc
      _ = tau (u * (x * (v * y))) := by simp only [mul_assoc]
      _ = tau ((x * (v * y)) * u) := hcyc _ _
      _ = _ := by simp only [mul_assoc]
  have hv : tau (v * x * u * y) = tau (x * (u * y * v)) := by
    calc
      _ = tau (v * (x * (u * y))) := by simp only [mul_assoc]
      _ = tau ((x * (u * y)) * v) := hcyc _ _
      _ = _ := by simp only [mul_assoc]
  simp only [orientedTransport_apply, sub_mul, mul_sub, map_sub]
  rw [hu, hv]
  abel

end Trace

end InfoGeometry.OperatorAlgebra.LieJordanOctet
