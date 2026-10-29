/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanHodgePairing
import InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Native Hilbert realization of the full real doubled matrix algebra

Flattening is an explicit linear equivalence, not a diagonal restriction.
The complete matrix multiplication operators are transported and retain order.
The positive adjoint is Mathlib's `ContinuousLinearMap.adjoint`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LieJordanHodgeHilbert

open Matrix HilbertSchmidtMatrix
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
open InfoGeometry.OperatorAlgebra.LieJordanHodgePairing
open InfoGeometry.OperatorAlgebra.BoundedHomotopyCoercivity

/-- Two full matrix copies with their Euclidean, rather than supremum, norm. -/
abbrev HS (n : ℕ) := EuclideanSpace ℝ (Bool × Fin n × Fin n)

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Every matrix entry is retained. The transposed index convention matches
exactly the existing trace-pairing sum formula. -/
def encode (n : ℕ) :
    (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) ≃ₗ[ℝ] HS n where
  toFun z := WithLp.toLp 2 (fun t =>
    if t.1 then z.2 t.2.2 t.2.1 else z.1 t.2.2 t.2.1)
  invFun f := (fun i j => f (false, j, i), fun i j => f (true, j, i))
  left_inv z := rfl
  right_inv f := by
    ext ⟨b, i, j⟩
    cases b <;> rfl
  map_add' z w := by
    ext ⟨b, i, j⟩
    cases b <;> rfl
  map_smul' r z := by
    ext ⟨b, i, j⟩
    cases b <;> rfl

theorem inner_encode (z w : Mat × Mat) :
    inner ℝ (encode n z) (encode n w) = doubledPair z w := by
  simp [PiLp.inner_apply, encode, doubledPair, hilbertSchmidtPairing_eq_sum,
    Fintype.sum_prod_type, add_comm, mul_comm]

theorem norm_encode_sq (z : Mat × Mat) :
    ‖encode n z‖ ^ 2 = doubledPair z z := by
  rw [← real_inner_self_eq_norm_sq, inner_encode]

/-- Transport of the actual matrix endomorphism, with native continuity. -/
def realize (T : Module.End ℝ (Mat × Mat)) : HS n →L[ℝ] HS n :=
  LinearMap.toContinuousLinearMap
    ((encode n).toLinearMap.comp (T.comp (encode n).symm.toLinearMap))

@[simp] theorem realize_apply (T : Module.End ℝ (Mat × Mat)) (x : HS n) :
    realize T x = encode n (T ((encode n).symm x)) := rfl

@[simp] theorem realize_encode (T : Module.End ℝ (Mat × Mat)) (z : Mat × Mat) :
    realize T (encode n z) = encode n (T z) := by
  simp only [realize_apply, LinearEquiv.symm_apply_apply]

theorem realize_add (T U : Module.End ℝ (Mat × Mat)) :
    realize (T + U) = realize T + realize U := by
  ext x
  change encode n (T ((encode n).symm x) + U ((encode n).symm x)) = _
  rw [map_add]
  rfl

theorem realize_mul (T U : Module.End ℝ (Mat × Mat)) :
    realize (T * U) = realize T * realize U := by
  ext x
  change encode n (T (U ((encode n).symm x))) =
    encode n (T ((encode n).symm (encode n (U ((encode n).symm x)))))
  rw [LinearEquiv.symm_apply_apply]

/-- Genuine positive Hilbert adjoint, not an assumed adjoint field. -/
theorem adjoint_boundary (u : Mat) :
    ContinuousLinearMap.adjoint (realize (boundary (R := ℝ) u)) =
      realize (coboundary (R := ℝ) uᵀ) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  obtain ⟨z, rfl⟩ := (encode n).surjective x
  obtain ⟨w, rfl⟩ := (encode n).surjective y
  simp only [realize_encode, inner_encode]
  exact coboundary_adjoint_pairing u z w

/-- The algebraic exchanged identity is the actual positive Hodge operator. -/
theorem hodge_realization (u : Mat) :
    hodge (realize (boundary (R := ℝ) u)) =
      realize (liftOp (jordanLeft (R := ℝ) (u * uᵀ + uᵀ * u))) := by
  unfold hodge
  rw [adjoint_boundary, ← realize_mul, ← realize_mul, ← realize_add,
    boundary_coboundary_anticommutator]

/-- Concrete full-matrix consumer of the abstract bounded-homotopy estimate. -/
theorem matrix_coercivity_of_homotopy
    (u : Mat) (h P : HS n →L[ℝ] HS n)
    (hc : realize (boundary (R := ℝ) u) * h +
      h * realize (boundary (R := ℝ) u) = 1 - P)
    {C : ℝ} (hC : 0 < C) (hb : ‖h‖ ≤ C)
    (z : Mat × Mat) (hz : P (encode n z) = 0) :
    (1 / (2 * C ^ 2)) * doubledPair z z ≤
      doubledPair z (liftOp (jordanLeft (R := ℝ) (u * uᵀ + uᵀ * u)) z) := by
  have he := coercivity_of_homotopy
    (realize (boundary (R := ℝ) u)) h P hc hC hb (encode n z) hz
  simpa only [hodge_realization, realize_encode, inner_encode, norm_encode_sq] using he

end InfoGeometry.OperatorAlgebra.LieJordanHodgeHilbert
