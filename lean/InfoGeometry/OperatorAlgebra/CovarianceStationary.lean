/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.CovarianceContraction
import Mathlib.Analysis.Matrix.Order

/-!
# Positive stationary covariance in the native matrix operator norm

Full finite complex matrices carry Mathlib's `Matrix.Norms.L2Operator`
instances. The norm is the operator norm transported from Euclidean-space
endomorphisms; no entrywise norm or simultaneous diagonalization is used.

For a strict contraction `T` and positive semidefinite innovation `Q`, the
actual Banach fixed point is positive semidefinite. The proof takes the limit
of the positive covariance iterates from zero and uses Mathlib's closedness
of the positive semidefinite matrix cone. Uniqueness and convergence then
specialize the existing operator contraction theorems.
-/

namespace InfoGeometry.OperatorAlgebra.CovarianceStationary

open Filter
open scoped Topology ComplexOrder Matrix.Norms.L2Operator
open InfoGeometry.OperatorAlgebra.CovarianceTransport
open InfoGeometry.OperatorAlgebra.CovarianceDynamics
open InfoGeometry.OperatorAlgebra.CovarianceContraction

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- Closedness of the PSD cone makes the constructed Banach fixed point positive. -/
theorem fixedPoint_posSemidef (T Q : Mat) (hT : ‖T‖ < 1) (hQ : Q.PosSemidef) :
    (ContractingWith.fixedPoint (covarianceStep T Q)
      (covarianceStep_contracting T Q hT)).PosSemidef := by
  exact Matrix.posSemidef_is_closed.mem_of_tendsto
    ((covarianceStep_contracting T Q hT).tendsto_iterate_fixedPoint (0 : Mat))
    (Filter.Eventually.of_forall fun k =>
      covariance_iterate_posSemidef T (Matrix.PosSemidef.zero : (0 : Mat).PosSemidef) hQ k)

/-- Strict operator contraction constructs the unique positive stationary covariance. -/
theorem existsUnique_posSemidef_stationary (T Q : Mat)
    (hT : ‖T‖ < 1) (hQ : Q.PosSemidef) :
    ∃! S : Mat, S.PosSemidef ∧ covarianceStep T Q S = S := by
  let h := covarianceStep_contracting T Q hT
  refine ⟨ContractingWith.fixedPoint (covarianceStep T Q) h,
    ⟨fixedPoint_posSemidef T Q hT hQ, h.fixedPoint_isFixedPt⟩, ?_⟩
  intro S hS
  exact h.fixedPoint_unique hS.2

/-- Every initial full matrix converges to any stationary matrix of the contraction. -/
theorem tendsto_covariance_iterates (T Q : Mat) (hT : ‖T‖ < 1)
    {S : Mat} (hS : covarianceStep T Q S = S) (C : Mat) :
    Tendsto (fun k : ℕ => (covarianceStep T Q)^[k] C) atTop (𝓝 S) := by
  have h := covarianceStep_contracting T Q hT
  rw [h.fixedPoint_unique hS]
  exact h.tendsto_iterate_fixedPoint C

end InfoGeometry.OperatorAlgebra.CovarianceStationary
