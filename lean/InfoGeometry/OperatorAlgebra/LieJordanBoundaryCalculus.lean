/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Exact noncommutative boundary-superoperator calculus

The unsigned and signed sandwich terms are retained separately. In particular,
`ad_u J_v - ad_v J_u` is not `J_[u,v]`: it has an additional signed sandwich
term. A genuine square-zero operator is obtained on `A × A`, rather than
claiming that `ad_u` itself squares to zero whenever `u² = 0`.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus

attribute [local instance 100] LieRing.ofAssociativeRing

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.Core.JordanAssociator
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Two-sided symmetric sandwich action, without an implicit adjoint condition. -/
def crossTransport (u v : A) : Module.End R A where
  toFun x := u * x * v + v * x * u
  map_add' x y := by simp only [mul_add, add_mul]; abel
  map_smul' r x := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, RingHom.id_apply]

/-- The antisymmetric sandwich action is the omitted mixed-difference defect. -/
def orientedTransport (u v : A) : Module.End R A where
  toFun x := u * x * v - v * x * u
  map_add' x y := by simp only [mul_add, add_mul]; abel
  map_smul' r x := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub, RingHom.id_apply]

@[simp] theorem crossTransport_apply (u v x : A) :
    crossTransport (R := R) u v x = u * x * v + v * x * u := rfl

@[simp] theorem orientedTransport_apply (u v x : A) :
    orientedTransport (R := R) u v x = u * x * v - v * x * u := rfl

/-- Mixed symmetric composition cancels all two-sided terms. -/
theorem jordan_lie_sum (u v : A) :
    jordanLeft (R := R) u * LieAlgebra.ad R A v +
      jordanLeft (R := R) v * LieAlgebra.ad R A u =
        LieAlgebra.ad R A (u * v + v * u) := by
  ext x
  change (u * (v * x - x * v) + (v * x - x * v) * u) +
    (v * (u * x - x * u) + (u * x - x * u) * v) =
    (u * v + v * u) * x - x * (u * v + v * u)
  noncomm_ring

/-- Corrected mixed antisymmetric composition, with its noncommutative defect. -/
theorem lie_jordan_difference (u v : A) :
    LieAlgebra.ad R A u * jordanLeft (R := R) v -
      LieAlgebra.ad R A v * jordanLeft (R := R) u =
        jordanLeft (R := R) (u * v - v * u) +
          2 • orientedTransport (R := R) u v := by
  ext x
  change (u * (v * x + x * v) - (v * x + x * v) * u) -
    (v * (u * x + x * u) - (u * x + x * u) * v) =
    (u * v - v * u) * x + x * (u * v - v * u) +
      2 • (u * x * v - v * x * u)
  simp only [two_nsmul]
  noncomm_ring

/-- The ordinary commutator of adjoint operators reuses the ring owner. -/
theorem lie_lie_difference (u v : A) :
    LieAlgebra.ad R A u * LieAlgebra.ad R A v -
      LieAlgebra.ad R A v * LieAlgebra.ad R A u =
        LieAlgebra.ad R A (u * v - v * u) := by
  ext x
  exact commutator_operator_commutator u v x

theorem jordan_jordan_sum (u v : A) :
    jordanLeft (R := R) u * jordanLeft (R := R) v +
      jordanLeft (R := R) v * jordanLeft (R := R) u =
        jordanLeft (R := R) (u * v + v * u) +
          2 • crossTransport (R := R) u v := by
  ext x
  change (u * (v * x + x * v) + (v * x + x * v) * u) +
    (v * (u * x + x * u) + (u * x + x * u) * v) =
    (u * v + v * u) * x + x * (u * v + v * u) +
      2 • (u * x * v + v * x * u)
  simp only [two_nsmul]
  noncomm_ring

theorem lie_lie_sum (u v : A) :
    LieAlgebra.ad R A u * LieAlgebra.ad R A v +
      LieAlgebra.ad R A v * LieAlgebra.ad R A u =
        jordanLeft (R := R) (u * v + v * u) -
          2 • crossTransport (R := R) u v := by
  ext x
  change (u * (v * x - x * v) - (v * x - x * v) * u) +
    (v * (u * x - x * u) - (u * x - x * u) * v) =
    (u * v + v * u) * x + x * (u * v + v * u) -
      2 • (u * x * v + v * x * u)
  simp only [two_nsmul]
  noncomm_ring

/-- Exact fourfold readout; division by four is not assumed. -/
theorem fourfold_cross_readout (u v : A) :
    (jordanLeft (R := R) u * jordanLeft (R := R) v +
      jordanLeft (R := R) v * jordanLeft (R := R) u) -
    (LieAlgebra.ad R A u * LieAlgebra.ad R A v +
      LieAlgebra.ad R A v * LieAlgebra.ad R A u) =
        (4 : ℕ) • crossTransport (R := R) u v := by
  rw [jordan_jordan_sum, lie_lie_sum]
  simp only [show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul]
  abel

/-- A doubled boundary operator uses the Lie action in one block and the
Jordan action in the other; neither block is a scalar replacement. -/
def boundary (u : A) : Module.End R (A × A) where
  toFun z := (LieAlgebra.ad R A u z.2, jordanLeft (R := R) u z.1)
  map_add' z w := by
    change (LieAlgebra.ad R A u (z.2 + w.2), jordanLeft (R := R) u (z.1 + w.1)) = _
    rw [map_add, map_add]
    rfl
  map_smul' r z := by
    change (LieAlgebra.ad R A u (r • z.2), jordanLeft (R := R) u (r • z.1)) = _
    rw [map_smul, map_smul]
    rfl

/-- Its square is the adjoint action of the coefficient square on both copies. -/
theorem boundary_sq (u : A) :
    boundary (R := R) u * boundary (R := R) u =
      liftOp (LieAlgebra.ad R A (u * u)) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · change u * (u * z.1 + z.1 * u) - (u * z.1 + z.1 * u) * u =
      (u * u) * z.1 - z.1 * (u * u)
    noncomm_ring
  · change u * (u * z.2 - z.2 * u) + (u * z.2 - z.2 * u) * u =
      (u * u) * z.2 - z.2 * (u * u)
    noncomm_ring

theorem boundary_square_zero {u : A} (hu : u * u = 0) :
    boundary (R := R) u * boundary (R := R) u = 0 := by
  rw [boundary_sq, hu]
  apply LinearMap.ext
  intro z
  change (0 * z.1 - z.1 * 0, 0 * z.2 - z.2 * 0) = (0, 0)
  simp

/-- The actual native image/kernel condition of a differential. -/
theorem boundary_range_le_ker {u : A} (hu : u * u = 0) :
    LinearMap.range (boundary (R := R) u) ≤ LinearMap.ker (boundary (R := R) u) := by
  rintro z ⟨x, rfl⟩
  change boundary (R := R) u (boundary (R := R) u x) = 0
  exact congrArg (fun t : Module.End R (A × A) => t x) (boundary_square_zero hu)

/-- The anticommutator of two boundaries acts by the quadratic coefficient. -/
theorem boundary_anticommutator (u v : A) :
    boundary (R := R) u * boundary (R := R) v +
      boundary (R := R) v * boundary (R := R) u =
        liftOp (LieAlgebra.ad R A (u * v + v * u)) := by
  apply LinearMap.ext
  intro z
  apply Prod.ext
  · change (u * (v * z.1 + z.1 * v) - (v * z.1 + z.1 * v) * u) +
      (v * (u * z.1 + z.1 * u) - (u * z.1 + z.1 * u) * v) =
      (u * v + v * u) * z.1 - z.1 * (u * v + v * u)
    noncomm_ring
  · change (u * (v * z.2 - z.2 * v) + (v * z.2 - z.2 * v) * u) +
      (v * (u * z.2 - z.2 * u) + (u * z.2 - z.2 * u) * v) =
      (u * v + v * u) * z.2 - z.2 * (u * v + v * u)
    noncomm_ring

/-- The bare adjoint action is not in general a differential. -/
theorem ad_square_of_square_zero {u : A} (hu : u * u = 0) (x : A) :
    LieAlgebra.ad R A u (LieAlgebra.ad R A u x) = -(2 • (u * x * u)) := by
  change u * (u * x - x * u) - (u * x - x * u) * u = _
  calc
    _ = (u * u) * x - 2 • (u * x * u) + x * (u * u) := by
      simp only [two_nsmul]
      noncomm_ring
    _ = _ := by rw [hu]; simp

@[simp] theorem crossTransport_one (u v : A) :
    crossTransport (R := R) u v 1 = u * v + v * u := by
  simp only [crossTransport_apply, mul_one]

/-- Cyclic trace balance has no commutation hypothesis on the input. -/
theorem trace_crossTransport {G : Type*} [AddCommGroup G]
    (tau : A →+ G) (hcyc : ∀ a b : A, tau (a * b) = tau (b * a)) (u v x : A) :
    tau (crossTransport (R := R) u v x) = tau ((u * v + v * u) * x) := by
  simp only [crossTransport_apply, add_mul, map_add]
  have hu : tau (u * x * v) = tau (v * u * x) := by
    rw [hcyc (u * x) v, ← mul_assoc]
  have hv : tau (v * x * u) = tau (u * v * x) := by
    rw [hcyc (v * x) u, ← mul_assoc]
  rw [hu, hv, add_comm]

theorem map_crossTransport {B : Type*} [Ring B] [Algebra R B]
    (f : A →+* B) (u v x : A) :
    f (crossTransport (R := R) u v x) =
      crossTransport (R := R) (f u) (f v) (f x) := by
  simp only [crossTransport_apply, map_add, map_mul]

theorem map_orientedTransport {B : Type*} [Ring B] [Algebra R B]
    (f : A →+* B) (u v x : A) :
    f (orientedTransport (R := R) u v x) =
      orientedTransport (R := R) (f u) (f v) (f x) := by
  simp only [orientedTransport_apply, map_sub, map_mul]

end InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
