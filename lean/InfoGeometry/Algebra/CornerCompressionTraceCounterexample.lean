/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CyclicQuotient
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

/-!
# Compression-defined trace need not be cyclic

This refutes only X ↦ Tr(P X P) on the ambient algebra. Ordinary full matrix
trace still exists and extends the trace of this rank-two corner.
-/

namespace InfoGeometry.Algebra.CornerCompressionTraceCounterexample

abbrev Mat3Z := Matrix (Fin 3) (Fin 3) ℤ

abbrev Mat3 (A : Type*) := Matrix (Fin 3) (Fin 3) A

/-- The two matrix units used to witness noncommutativity over any coefficient
ring. -/
def matrixUnit01 {A : Type*} [Ring A] : Matrix (Fin 3) (Fin 3) A :=
  Matrix.single (0 : Fin 3) 1 (1 : A)

def matrixUnit10 {A : Type*} [Ring A] : Matrix (Fin 3) (Fin 3) A :=
  Matrix.single (1 : Fin 3) 0 (1 : A)

/-- Matrix units give a carrier-matched noncommutativity witness over every
nontrivial coefficient ring. -/
theorem matrix3_noncommutativity_witness
    {A : Type*} [Ring A] [Nontrivial A] :
    matrixUnit01 (A := A) * matrixUnit10 (A := A) ≠
      matrixUnit10 (A := A) * matrixUnit01 (A := A) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M 0 0) h
  simp [matrixUnit01, matrixUnit10, Matrix.mul_apply, Matrix.single_apply] at h00

/-- The rank-two coordinate projector over an arbitrary coefficient ring. -/
def rankTwoProjector {A : Type*} [Ring A] : Mat3 A :=
  fun i j => if i = j ∧ i.val < 2 then 1 else 0

/-- The trace-commutator defect internal to the retained two-coordinate corner.
The ordered products are kept explicit because coefficient multiplication need
not commute. -/
def internalCornerTraceDefect {A : Type*} [Ring A]
    (X Y : Mat3 A) : A :=
  (X 0 0 * Y 0 0 - Y 0 0 * X 0 0) +
  (X 0 1 * Y 1 0 - Y 0 1 * X 1 0) +
  (X 1 0 * Y 0 1 - Y 1 0 * X 0 1) +
  (X 1 1 * Y 1 1 - Y 1 1 * X 1 1)

/-- Net ordered product flux through the omitted third coordinate. -/
def omittedCoordinateTraceFlux {A : Type*} [Ring A]
    (X Y : Mat3 A) : A :=
  X 0 2 * Y 2 0 + X 1 2 * Y 2 1 -
    (Y 0 2 * X 2 0 + Y 1 2 * X 2 1)

/-- Exact noncommutative decomposition of the compressed commutator trace:
the anomaly is the sum of an internal corner trace defect and flux through
the omitted coordinate. -/
theorem compressed_commutator_trace_decomposition
    {A : Type*} [Ring A] (X Y : Mat3 A) :
    Matrix.trace (rankTwoProjector * (X * Y - Y * X) * rankTwoProjector) =
      internalCornerTraceDefect X Y + omittedCoordinateTraceFlux X Y := by
  simp [rankTwoProjector, internalCornerTraceDefect,
    omittedCoordinateTraceFlux, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ]
  noncomm_ring

/-- Pairwise cyclicity of the compressed trace holds exactly when the internal
noncommutative corner defect is canceled by flux through the omitted
coordinate.  The criterion permits cancellation between these two terms; it
does not assume either term vanishes separately. -/
theorem compressed_trace_cyclic_on_pair_iff_flux_balance
    {A : Type*} [Ring A] (X Y : Mat3 A) :
    Matrix.trace (rankTwoProjector * (X * Y) * rankTwoProjector) =
        Matrix.trace (rankTwoProjector * (Y * X) * rankTwoProjector) ↔
      internalCornerTraceDefect X Y + omittedCoordinateTraceFlux X Y = 0 := by
  have htrace :
      Matrix.trace (rankTwoProjector * (X * Y - Y * X) * rankTwoProjector) =
        Matrix.trace (rankTwoProjector * (X * Y) * rankTwoProjector) -
          Matrix.trace (rankTwoProjector * (Y * X) * rankTwoProjector) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  constructor
  · intro hcyclic
    have hdiff := sub_eq_zero.mpr hcyclic
    have hcomm := htrace.trans hdiff
    rw [compressed_commutator_trace_decomposition] at hcomm
    exact hcomm
  · intro hbalance
    have hcomm :
        Matrix.trace (rankTwoProjector * (X * Y - Y * X) * rankTwoProjector) = 0 := by
      rw [compressed_commutator_trace_decomposition]
      exact hbalance
    have hdiff := htrace.symm.trans hcomm
    exact sub_eq_zero.mp hdiff

/-- Matrix unit entering the retained corner from the omitted third
coordinate. -/
def enterOmittedCoordinate {A : Type*} [Ring A] : Mat3 A :=
  Matrix.single (0 : Fin 3) 2 (1 : A)

/-- Matrix unit returning from the retained corner to the omitted coordinate. -/
def leaveOmittedCoordinate {A : Type*} [Ring A] : Mat3 A :=
  Matrix.single (2 : Fin 3) 0 (1 : A)

/-- The two cross-boundary matrix units give an exact pairwise trace witness
over every coefficient ring: the forward product contributes one retained
diagonal unit, while the reverse product lies entirely in the omitted corner. -/
theorem omitted_coordinate_matrix_units_compressed_traces
    {A : Type*} [Ring A] :
    Matrix.trace (rankTwoProjector *
        (enterOmittedCoordinate (A := A) * leaveOmittedCoordinate) *
        rankTwoProjector) = 1 ∧
      Matrix.trace (rankTwoProjector *
        (leaveOmittedCoordinate (A := A) * enterOmittedCoordinate) *
        rankTwoProjector) = 0 := by
  constructor <;>
    simp [enterOmittedCoordinate, leaveOmittedCoordinate, rankTwoProjector,
      Matrix.single_apply, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ]

/-- The compressed trace is not cyclic on the full matrix algebra over any
nontrivial coefficient ring; the failure is witnessed entirely by flux across
the omitted coordinate. -/
theorem compressed_trace_not_cyclic_of_nontrivial
    {A : Type*} [Ring A] [Nontrivial A] :
    ¬ ∀ X Y : Mat3 A,
      Matrix.trace (rankTwoProjector * (X * Y) * rankTwoProjector) =
        Matrix.trace (rankTwoProjector * (Y * X) * rankTwoProjector) := by
  intro hcyclic
  rcases omitted_coordinate_matrix_units_compressed_traces (A := A) with
    ⟨hforward, hreverse⟩
  have h := hcyclic enterOmittedCoordinate leaveOmittedCoordinate
  rw [hforward, hreverse] at h
  exact one_ne_zero h

def projector : Mat3Z := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
def enterCorner : Mat3Z := !![0, 0, 1; 0, 0, 0; 0, 0, 0]
def leaveCorner : Mat3Z := !![0, 0, 0; 0, 0, 0; 1, 0, 0]

theorem projector_idempotent : projector * projector = projector := by decide

theorem projector_not_central : projector * enterCorner ≠ enterCorner * projector := by
  decide

theorem compressed_commutator_trace :
    Matrix.trace (projector * (enterCorner * leaveCorner - leaveCorner * enterCorner) *
      projector) = 1 := by decide

/-- Exact cyclicity defect of the rank-two corner compression.  The trace of
the compressed commutator is the net matrix flux through the omitted third
coordinate. -/
theorem compressed_commutator_trace_eq_boundary_flux (X Y : Mat3Z) :
    Matrix.trace (projector * (X * Y - Y * X) * projector) =
      X 0 2 * Y 2 0 + X 1 2 * Y 2 1 -
        (Y 0 2 * X 2 0 + Y 1 2 * X 2 1) := by
  simp [projector, Matrix.trace, Matrix.vecMul, Matrix.vecHead,
    Matrix.vecTail, Matrix.cons_val_zero, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring_nf

theorem compressed_products_trace_ne :
    Matrix.trace (projector * (enterCorner * leaveCorner) * projector) ≠
      Matrix.trace (projector * (leaveCorner * enterCorner) * projector) := by decide

theorem compression_not_cyclic :
    ¬ ∀ X Y : Mat3Z, Matrix.trace (projector * (X * Y) * projector) =
      Matrix.trace (projector * (Y * X) * projector) := by
  intro h
  exact compressed_products_trace_ne (h enterCorner leaveCorner)

/-- The compression functional cannot descend to the additive cyclic quotient. -/
theorem compression_no_cyclic_factor :
    ¬ ∃ f : CyclicQuotient.CyclicModule ℤ Mat3Z →ₗ[ℤ] ℤ,
      ∀ X : Mat3Z, f (CyclicQuotient.cyclicClass ℤ Mat3Z X) =
        Matrix.trace (projector * X * projector) := by
  rintro ⟨f, hf⟩
  apply compressed_products_trace_ne
  exact (hf _).symm.trans ((congrArg f
    (CyclicQuotient.cyclicClass_mul_comm ℤ Mat3Z enterCorner leaveCorner)).trans (hf _))

end InfoGeometry.Algebra.CornerCompressionTraceCounterexample
