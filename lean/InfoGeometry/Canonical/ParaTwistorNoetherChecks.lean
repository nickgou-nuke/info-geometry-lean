/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorDirichlet.MatrixLegendreResidual
import InfoGeometry.Twistor.RealLorentzTwistorIncidence
import InfoGeometry.Clifford.AnticommutatorSymmetry
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceTriple
import InfoGeometry.Core.JordanMultiplicationClosure
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Concrete consumers and boundaries for the para/twistor algebraic intake

These consumers use a coupled positive quadratic form, real Lorentz graph
incidence, and the two real matrix units in dimension two. The same matrix
units give a nonzero Peirce triple and a two-dimensional represented Clifford
pairing. A swap unit and a noncentral diagonal generator exercise the finite
and infinitesimal intertwining theorems.

The boundary examples include coincident spacetime points, timelike separation
without a nonzero common twistor, a Peirce triple that does not vanish, and a
nonzero trace rate when the commuting-generator hypothesis is absent. The
trace identity is algebraic; no curve or conservation-along-trajectories result
is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ParaTwistorNoetherChecks

open Matrix
open InfoGeometry.OperatorAlgebra.OperatorDirichlet
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Twistor.RealLorentzTwistorIncidence
open InfoGeometry.Twistor.RealTwistorIncidence (Carrier)
open InfoGeometry.Clifford.AnticommutatorSymmetry

#check InfoGeometry.OperatorAlgebra.OperatorDirichlet.quadraticFenchelGap_eq_residual
#check InfoGeometry.OperatorAlgebra.OperatorDirichlet.supplied_inverse_legendre_isGreatest
#check InfoGeometry.OperatorAlgebra.OperatorDirichlet.supplied_inverse_legendre_csSup
#check InfoGeometry.Twistor.RealLorentzTwistorIncidence.null_iff_shared_nonzero_twistor
#check InfoGeometry.Clifford.AnticommutatorSymmetry.pairing_eq_of_unit_conjugation_intertwining
#check InfoGeometry.Clifford.AnticommutatorSymmetry.pairing_skew_of_commutator_intertwining
#check InfoGeometry.Clifford.AnticommutatorSymmetry.linearMapOfUnitConjugationIntertwining
#check InfoGeometry.Clifford.AnticommutatorSymmetry.linearMapOfCommutatorIntertwining
#check InfoGeometry.OperatorAlgebra.PeirceSpine.jordanTriple_conePlus_compression
#check InfoGeometry.OperatorAlgebra.PeirceSpine.jordanTriple_coneMinus_compression
#check InfoGeometry.OperatorAlgebra.PeirceSpine.symm_associator_conePlus

/-! ## A non-diagonal quadratic form and its attained conjugate -/

private def quadraticG : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 1]
private def quadraticGInv : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 2]

private theorem quadraticGInv_symmetric : quadraticGInvᵀ = quadraticGInv := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [quadraticGInv, Matrix.transpose_apply]

private theorem quadraticG_mul_inv : quadraticG * quadraticGInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quadraticG, quadraticGInv, Matrix.mul_apply, Fin.sum_univ_two]

private theorem quadraticGInv_nonneg (z : Fin 2 → ℝ) :
    0 ≤ quadForm quadraticGInv z := by
  have hform : quadForm quadraticGInv z = (z 0 - z 1) ^ 2 + z 1 ^ 2 := by
    simp [quadForm, quadraticGInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [hform]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The example genuinely has a coupling between its two coordinates. -/
theorem quadratic_example_offDiagonal_ne_zero : quadraticG 0 1 ≠ 0 := by
  norm_num [quadraticG]

/-- The supplied-inverse API gives a greatest value for a coupled quadratic,
with positivity proved as a sum of two squares. -/
theorem coupled_quadratic_legendre_isGreatest (y : Fin 2 → ℝ) :
    IsGreatest (Set.range fun x : Fin 2 → ℝ =>
      x ⬝ᵥ y - (1 / 2) * quadForm quadraticG x)
      ((1 / 2) * quadForm quadraticGInv y) :=
  supplied_inverse_legendre_isGreatest quadraticGInv_symmetric quadraticG_mul_inv
    quadraticGInv_nonneg y

/-! ## Coincident, distinct null, and timelike graph planes -/

/-- Coincidence is included in the null-incidence theorem. -/
theorem coincident_graphs_have_nonzero_twistor (x : Spacetime) :
    ∃ z : Carrier Spinor Spinor, z ≠ 0 ∧
      z ∈ spacetimeIncidenceSpace x ∧ z ∈ spacetimeIncidenceSpace x := by
  apply (null_iff_shared_nonzero_twistor x x).mp
  simp [lorentzQuadratic]

/-- A distinct lightlike point shares a nonzero twistor with the origin. -/
theorem lightlike_graphs_have_nonzero_twistor :
    ∃ z : Carrier Spinor Spinor, z ≠ 0 ∧
      z ∈ spacetimeIncidenceSpace ![1, 1, 0, 0] ∧
      z ∈ spacetimeIncidenceSpace 0 := by
  apply (null_iff_shared_nonzero_twistor ![1, 1, 0, 0] 0).mp
  norm_num [lorentzQuadratic]

/-- Timelike separation excludes a nonzero common vector in the graph planes. -/
theorem timelike_graphs_have_no_nonzero_twistor :
    ¬ ∃ z : Carrier Spinor Spinor, z ≠ 0 ∧
      z ∈ spacetimeIncidenceSpace ![1, 0, 0, 0] ∧
      z ∈ spacetimeIncidenceSpace 0 := by
  intro h
  have hnull := (null_iff_shared_nonzero_twistor ![1, 0, 0, 0] 0).mpr h
  norm_num [lorentzQuadratic] at hnull

/-! ## Nonzero Peirce multiplication in the actual real matrix ring -/

private def upperMatrixUnit : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
private def lowerMatrixUnit : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
private def cornerProjection : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

private theorem cornerProjection_idempotent :
    cornerProjection * cornerProjection = cornerProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cornerProjection, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperMatrixUnit_corner :
    conePlus cornerProjection upperMatrixUnit = upperMatrixUnit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conePlus, cornerProjection, upperMatrixUnit, Matrix.mul_apply, Fin.sum_univ_two]

/-- The concrete matrix carrier used below is noncommutative. -/
theorem matrix_units_noncommute :
    upperMatrixUnit * lowerMatrixUnit ≠ lowerMatrixUnit * upperMatrixUnit := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
  norm_num [upperMatrixUnit, lowerMatrixUnit, Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- The upper-corner support theorem applies to every middle matrix. -/
theorem matrix_unit_triple_compression (Y : Matrix (Fin 2) (Fin 2) ℝ) :
    cornerProjection * jordanTriple upperMatrixUnit Y upperMatrixUnit *
        (1 - cornerProjection) = jordanTriple upperMatrixUnit Y upperMatrixUnit := by
  simpa only [upperMatrixUnit_corner] using
    jordanTriple_conePlus_compression cornerProjection_idempotent
      upperMatrixUnit Y upperMatrixUnit

/-- The opposite-corner middle entry gives the nonzero value `2 E₁₂`. -/
theorem matrix_unit_triple_value :
    jordanTriple upperMatrixUnit lowerMatrixUnit upperMatrixUnit =
      (2 : ℝ) • upperMatrixUnit := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jordanTriple, upperMatrixUnit, lowerMatrixUnit,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Same-corner square-zero does not make the alternating-corner triple zero. -/
theorem matrix_unit_triple_ne_zero :
    jordanTriple upperMatrixUnit lowerMatrixUnit upperMatrixUnit ≠ 0 := by
  rw [matrix_unit_triple_value]
  intro h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
  norm_num [upperMatrixUnit] at h01

/-- The square-zero Jordan associator consumer also has a nonzero value. -/
theorem matrix_unit_associator_ne_zero :
    anticomm (anticomm lowerMatrixUnit upperMatrixUnit) upperMatrixUnit -
      anticomm lowerMatrixUnit (anticomm upperMatrixUnit upperMatrixUnit) ≠ 0 := by
  have h := symm_associator_conePlus cornerProjection_idempotent
    upperMatrixUnit lowerMatrixUnit
  simp only [upperMatrixUnit_corner] at h
  rw [h]
  exact matrix_unit_triple_ne_zero

/-! ## A two-generator represented pairing on the same matrix carrier -/

/-- The two null generators are the same noncommuting matrix units as above. -/
private def offDiagonalLift : (Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (LinearMap.proj 0).smulRight upperMatrixUnit +
    (LinearMap.proj 1).smulRight lowerMatrixUnit

private def offDiagonalPairing (u v : Fin 2 → ℝ) : ℝ :=
  u 0 * v 1 + u 1 * v 0

private theorem offDiagonalLift_apply (u : Fin 2 → ℝ) :
    offDiagonalLift u = !![0, u 0; u 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonalLift, upperMatrixUnit, lowerMatrixUnit]

private theorem offDiagonalLift_anticomm (u v : Fin 2 → ℝ) :
    offDiagonalLift u * offDiagonalLift v + offDiagonalLift v * offDiagonalLift u =
      (1 * offDiagonalPairing u v) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  simp only [offDiagonalLift_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offDiagonalPairing] <;> ring

private def swapMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private theorem swapMatrix_sq : swapMatrix * swapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private def swapUnit : (Matrix (Fin 2) (Fin 2) ℝ)ˣ :=
  ⟨swapMatrix, swapMatrix, swapMatrix_sq, swapMatrix_sq⟩

private theorem swapUnit_intertwining (u : Fin 2 → ℝ) :
    (swapUnit : Matrix (Fin 2) (Fin 2) ℝ) * offDiagonalLift u *
        (↑(swapUnit⁻¹) : Matrix (Fin 2) (Fin 2) ℝ) =
      offDiagonalLift ![u 1, u 0] := by
  change swapMatrix * offDiagonalLift u * swapMatrix = offDiagonalLift ![u 1, u 0]
  simp only [offDiagonalLift_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- An actual matrix unit conjugation exchanges the null coordinates and
preserves their pairing by the new conditional symmetry theorem. -/
theorem offDiagonalPairing_swap_invariant (u v : Fin 2 → ℝ) :
    offDiagonalPairing ![u 1, u 0] ![v 1, v 0] = offDiagonalPairing u v :=
  pairing_eq_of_unit_conjugation_intertwining offDiagonalLift offDiagonalPairing
    1 (by norm_num) offDiagonalLift_anticomm swapUnit
    (fun w => ![w 1, w 0]) swapUnit_intertwining u v

private theorem cornerProjection_intertwining (u : Fin 2 → ℝ) :
    cornerProjection * offDiagonalLift u - offDiagonalLift u * cornerProjection =
      offDiagonalLift ![u 0, -u 1] := by
  simp only [offDiagonalLift_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cornerProjection]

/-- A noncentral diagonal generator gives a nonzero infinitesimal vector map;
the represented commutator theorem supplies its pairing-skew identity. -/
theorem offDiagonalPairing_diagonal_generator_skew (u v : Fin 2 → ℝ) :
    offDiagonalPairing ![u 0, -u 1] v +
      offDiagonalPairing u ![v 0, -v 1] = 0 :=
  pairing_skew_of_commutator_intertwining offDiagonalLift offDiagonalPairing
    1 (by norm_num) offDiagonalLift_anticomm cornerProjection
    (fun w => ![w 0, -w 1]) cornerProjection_intertwining u v

/-! ## Cyclic trace: commuting-generator rate and its boundary -/

/-- Native matrix trace turns the existing cyclic-adjoint identity into the
zero-rate formula under its commuting-generator hypothesis. -/
theorem matrix_trace_zero_rate_of_commute
    (H μ K : Matrix (Fin 2) (Fin 2) ℝ) (hHK : H * K = K * H) :
    Matrix.trace ((H * μ - μ * H) * K) = 0 := by
  have h := InfoGeometry.Core.JordanMultiplicationClosure.trace_adjoint_identity
    (Matrix.traceAddMonoidHom (Fin 2) ℝ) Matrix.trace_mul_comm H μ K
  simpa [Matrix.traceAddMonoidHom, hHK] using h

/-- Removing the commuting-generator hypothesis permits a nonzero trace rate. -/
theorem matrix_trace_rate_without_commutation :
    Matrix.trace ((cornerProjection * upperMatrixUnit -
      upperMatrixUnit * cornerProjection) * lowerMatrixUnit) = 1 := by
  norm_num [Matrix.trace, cornerProjection, upperMatrixUnit, lowerMatrixUnit,
    Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.ParaTwistorNoetherChecks
