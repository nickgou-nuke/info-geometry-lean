/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
import InfoGeometry.Canonical.HilbertSchmidtMatrixPairing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# The positive real matrix adjoint, energy, and harmonic kernel

The pairing is the existing full-matrix Hilbert--Schmidt pairing Tr(XᵀY),
not the indefinite cyclic pairing Tr(XY) or a Krein adjoint.
-/

namespace InfoGeometry.OperatorAlgebra.LieJordanHodgePairing

attribute [local instance 100] LieRing.ofAssociativeRing

open Matrix HilbertSchmidtMatrix
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "hs" => hilbertSchmidtPairing

theorem pairing_add_left (x y z : Mat) : hs (x + y) z = hs x z + hs y z := by
  simp [hilbertSchmidtPairing, add_mul]

theorem pairing_add_right (x y z : Mat) : hs x (y + z) = hs x y + hs x z := by
  simp [hilbertSchmidtPairing, mul_add]

theorem pairing_sub_left (x y z : Mat) : hs (x - y) z = hs x z - hs y z := by
  simp [hilbertSchmidtPairing, sub_mul]

theorem pairing_sub_right (x y z : Mat) : hs x (y - z) = hs x y - hs x z := by
  simp [hilbertSchmidtPairing, mul_sub]

theorem pairing_self_eq_zero_iff (x : Mat) : hs x x = 0 ↔ x = 0 := by
  have ht : xᴴ = xᵀ := by ext i j; simp
  simpa only [hilbertSchmidtPairing, ht] using
    (Matrix.trace_conjTranspose_mul_self_eq_zero_iff (A := x))

theorem pairing_mul_left (u x y : Mat) : hs (u * x) y = hs x (uᵀ * y) := by
  simp only [hilbertSchmidtPairing, transpose_mul, mul_assoc]

theorem pairing_mul_right (u x y : Mat) : hs (x * u) y = hs x (y * uᵀ) := by
  calc
    _ = trace (uᵀ * (xᵀ * y)) := by
      simp only [hilbertSchmidtPairing, transpose_mul, mul_assoc]
    _ = trace ((xᵀ * y) * uᵀ) := trace_mul_comm _ _
    _ = _ := by simp only [hilbertSchmidtPairing, mul_assoc]

/-- The positive Hilbert--Schmidt adjoint of ad(u) is ad(uᵀ). -/
theorem pairing_ad (u x y : Mat) :
    hs (LieAlgebra.ad ℝ Mat u x) y = hs x (LieAlgebra.ad ℝ Mat uᵀ y) := by
  change hs (u * x - x * u) y = hs x (uᵀ * y - y * uᵀ)
  rw [pairing_sub_left, pairing_sub_right, pairing_mul_left, pairing_mul_right]

theorem pairing_jordan (u x y : Mat) :
    hs (jordanLeft (R := ℝ) u x) y = hs x (jordanLeft (R := ℝ) uᵀ y) := by
  change hs (u * x + x * u) y = hs x (uᵀ * y + y * uᵀ)
  rw [pairing_add_left, pairing_add_right, pairing_mul_left, pairing_mul_right]

/-- Positive pairing on both full matrix copies. -/
def doubledPair (z w : Mat × Mat) : ℝ := hs z.1 w.1 + hs z.2 w.2

theorem doubledPair_symm (z w : Mat × Mat) : doubledPair z w = doubledPair w z := by
  simp only [doubledPair, hilbertSchmidt_symmetry]

theorem doubledPair_add_right (z w t : Mat × Mat) :
    doubledPair z (w + t) = doubledPair z w + doubledPair z t := by
  change hs z.1 (w.1 + t.1) + hs z.2 (w.2 + t.2) = _
  rw [pairing_add_right, pairing_add_right]
  unfold doubledPair
  abel

theorem doubledPair_nonneg (z : Mat × Mat) : 0 ≤ doubledPair z z :=
  add_nonneg (hilbertSchmidt_pos_semidef z.1) (hilbertSchmidt_pos_semidef z.2)

theorem doubledPair_self_eq_zero_iff (z : Mat × Mat) :
    doubledPair z z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h1 := hilbertSchmidt_pos_semidef z.1
    have h2 := hilbertSchmidt_pos_semidef z.2
    have hz1 : hs z.1 z.1 = 0 := by unfold doubledPair at hz; linarith
    have hz2 : hs z.2 z.2 = 0 := by unfold doubledPair at hz; linarith
    exact Prod.ext ((pairing_self_eq_zero_iff _).mp hz1)
      ((pairing_self_eq_zero_iff _).mp hz2)
  · rintro rfl
    simp [doubledPair, hilbertSchmidtPairing]

/-- The exchanged transpose boundary satisfies the actual adjoint identity. -/
theorem boundary_adjoint_pairing (u : Mat) (z w : Mat × Mat) :
    doubledPair (boundary (R := ℝ) u z) w =
      doubledPair z (coboundary (R := ℝ) uᵀ w) := by
  change hs (LieAlgebra.ad ℝ Mat u z.2) w.1 +
    hs (jordanLeft (R := ℝ) u z.1) w.2 =
    hs z.1 (jordanLeft (R := ℝ) uᵀ w.2) +
      hs z.2 (LieAlgebra.ad ℝ Mat uᵀ w.1)
  rw [pairing_ad, pairing_jordan, add_comm]

theorem coboundary_adjoint_pairing (u : Mat) (z w : Mat × Mat) :
    doubledPair (coboundary (R := ℝ) uᵀ z) w =
      doubledPair z (boundary (R := ℝ) u w) := by
  rw [doubledPair_symm, ← boundary_adjoint_pairing, doubledPair_symm]

/-- Exact sum of squares; no coefficient commutation and no gap hypothesis. -/
theorem hodge_energy (u : Mat) (z : Mat × Mat) :
    doubledPair z (liftOp (jordanLeft (R := ℝ) (u * uᵀ + uᵀ * u)) z) =
      doubledPair (boundary (R := ℝ) u z) (boundary (R := ℝ) u z) +
      doubledPair (coboundary (R := ℝ) uᵀ z) (coboundary (R := ℝ) uᵀ z) := by
  rw [← boundary_coboundary_anticommutator]
  change doubledPair z (boundary (R := ℝ) u (coboundary (R := ℝ) uᵀ z) +
    coboundary (R := ℝ) uᵀ (boundary (R := ℝ) u z)) = _
  rw [doubledPair_add_right, ← coboundary_adjoint_pairing, ← boundary_adjoint_pairing]
  exact add_comm _ _

theorem hodge_energy_nonneg (u : Mat) (z : Mat × Mat) :
    0 ≤ doubledPair z (liftOp (jordanLeft (R := ℝ) (u * uᵀ + uᵀ * u)) z) := by
  rw [hodge_energy]
  exact add_nonneg (doubledPair_nonneg _) (doubledPair_nonneg _)

/-- The zero-energy space is exactly the common kernel, including all zero modes. -/
theorem hodge_energy_zero_iff (u : Mat) (z : Mat × Mat) :
    doubledPair z (liftOp (jordanLeft (R := ℝ) (u * uᵀ + uᵀ * u)) z) = 0 ↔
      boundary (R := ℝ) u z = 0 ∧ coboundary (R := ℝ) uᵀ z = 0 := by
  rw [hodge_energy]
  constructor
  · intro hz
    have hd := doubledPair_nonneg (boundary (R := ℝ) u z)
    have hc := doubledPair_nonneg (coboundary (R := ℝ) uᵀ z)
    constructor
    · apply (doubledPair_self_eq_zero_iff _).mp
      linarith
    · apply (doubledPair_self_eq_zero_iff _).mp
      linarith
  · rintro ⟨hd, hc⟩
    simp [hd, hc, doubledPair, hilbertSchmidtPairing]

end InfoGeometry.OperatorAlgebra.LieJordanHodgePairing
