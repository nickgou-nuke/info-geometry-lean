/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CyclicQuotient
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Compression-defined trace need not be cyclic

This refutes only X ↦ Tr(P X P) on the ambient algebra. Ordinary full matrix
trace still exists and extends the trace of this rank-two corner.
-/

namespace InfoGeometry.Algebra.CornerCompressionTraceCounterexample

section GeneralMatrix

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι]

/-- For an arbitrary idempotent matrix, the cyclicity defect of compression
is exactly the trace pairing with the commutator of the second input and the
projector. The coefficient ring is commutative so that ordinary matrix trace
is cyclic; the matrix algebra itself is generally noncommutative. -/
theorem compressed_trace_defect (P X Y : Matrix ι ι R) (hP : P * P = P) :
    Matrix.trace (P * (X * Y) * P) - Matrix.trace (P * (Y * X) * P) =
      Matrix.trace (X * (Y * P - P * Y)) := by
  have h₁ : Matrix.trace (P * (X * Y) * P) =
      Matrix.trace ((X * Y) * P) := by
    calc
      Matrix.trace (P * (X * Y) * P) = Matrix.trace (P * ((X * Y) * P)) := by
        simp only [mul_assoc]
      _ = Matrix.trace (((X * Y) * P) * P) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((X * Y) * P) := by rw [mul_assoc (X * Y) P P, hP]
  have h₂ : Matrix.trace (P * (Y * X) * P) = Matrix.trace (X * (P * Y)) := by
    calc
      Matrix.trace (P * (Y * X) * P) = Matrix.trace (P * ((Y * X) * P)) := by
        simp only [mul_assoc]
      _ = Matrix.trace (((Y * X) * P) * P) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Y * X) * P) := by rw [mul_assoc (Y * X) P P, hP]
      _ = Matrix.trace (Y * (X * P)) := by simp only [mul_assoc]
      _ = Matrix.trace ((X * P) * Y) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * (P * Y)) := by simp only [mul_assoc]
  calc
    _ = Matrix.trace ((X * Y) * P) - Matrix.trace (X * (P * Y)) := by
      rw [h₁, h₂]
    _ = Matrix.trace (X * (Y * P - P * Y)) := by
      rw [mul_sub, Matrix.trace_sub]
      simp only [mul_assoc]

/-- Exact criterion for cyclicity of a compressed trace against a fixed right
factor: it is cyclic for every left factor precisely when that right factor
commutes with the idempotent defining the compression. -/
theorem compressed_trace_cyclic_iff_commutes
    (P Y : Matrix ι ι R) (hP : P * P = P) :
    (∀ X : Matrix ι ι R,
      Matrix.trace (P * (X * Y) * P) = Matrix.trace (P * (Y * X) * P)) ↔
      Y * P = P * Y := by
  constructor
  · intro hcyclic
    have hpair (X : Matrix ι ι R) :
        Matrix.trace (X * (Y * P - P * Y)) = 0 := by
      have hdef := compressed_trace_defect P X Y hP
      rw [hcyclic X] at hdef
      simpa using hdef.symm
    have hzero : Y * P - P * Y = 0 := by
      apply (Matrix.ext_iff_trace_mul_left).2
      intro X
      simpa using hpair X
    exact sub_eq_zero.mp hzero
  · intro hcomm X
    have hdef := compressed_trace_defect P X Y hP
    rw [hcomm, sub_self, mul_zero, Matrix.trace_zero] at hdef
    exact sub_eq_zero.mp hdef

/-- Compression preserves the ambient trace on every matrix exactly when
the idempotent is the identity. This is stronger than agreement on its corner. -/
theorem compressed_trace_preserving_iff [DecidableEq ι]
    (P : Matrix ι ι R) (hP : P * P = P) :
    (∀ X : Matrix ι ι R, Matrix.trace (P * X * P) = Matrix.trace X) ↔ P = 1 := by
  have hcompression (X : Matrix ι ι R) :
      Matrix.trace (P * X * P) = Matrix.trace (X * P) := by
    calc
      _ = Matrix.trace (P * (X * P)) := by rw [mul_assoc]
      _ = Matrix.trace ((X * P) * P) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * P) := by rw [mul_assoc, hP]
  constructor
  · intro h
    apply (Matrix.ext_iff_trace_mul_left).2
    intro X
    simpa using (hcompression X).symm.trans (h X)
  · intro h X
    simp [h]

end GeneralMatrix

abbrev Mat3Z := Matrix (Fin 3) (Fin 3) ℤ

def projector : Mat3Z := !![1, 0, 0; 0, 1, 0; 0, 0, 0]
def enterCorner : Mat3Z := !![0, 0, 1; 0, 0, 0; 0, 0, 0]
def leaveCorner : Mat3Z := !![0, 0, 0; 0, 0, 0; 1, 0, 0]

theorem projector_idempotent : projector * projector = projector := by decide

theorem projector_not_central : projector * enterCorner ≠ enterCorner * projector := by
  decide

theorem compressed_commutator_trace :
    Matrix.trace (projector * (enterCorner * leaveCorner - leaveCorner * enterCorner) *
      projector) = 1 := by decide

theorem compressed_products_trace_ne :
    Matrix.trace (projector * (enterCorner * leaveCorner) * projector) ≠
      Matrix.trace (projector * (leaveCorner * enterCorner) * projector) := by
  have hdef :
      Matrix.trace (projector * (enterCorner * leaveCorner) * projector) -
        Matrix.trace (projector * (leaveCorner * enterCorner) * projector) = 1 := by
    rw [compressed_trace_defect projector enterCorner leaveCorner projector_idempotent]
    decide
  intro he
  rw [he, sub_self] at hdef
  norm_num at hdef

/-- The ordinary ambient matrix trace is cyclic and therefore descends to the
additive commutator quotient, unlike the compressed functional above. -/
def ambientTraceOnCyclicQuotient :
    CyclicQuotient.CyclicModule ℤ Mat3Z →ₗ[ℤ] ℤ :=
  CyclicQuotient.desc (Matrix.traceAddMonoidHom (Fin 3) ℤ) (by
    intro X Y
    exact Matrix.trace_mul_comm X Y)

@[simp] theorem ambientTraceOnCyclicQuotient_class (X : Mat3Z) :
    ambientTraceOnCyclicQuotient
      (CyclicQuotient.cyclicClass ℤ Mat3Z X) = Matrix.trace X := rfl

theorem ambient_trace_commutator_zero (X Y : Mat3Z) :
    Matrix.trace (X * Y - Y * X) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm X Y]
  simp

/-- On every element already supported in the projector corner, compression
and ambient trace agree. -/
theorem ambient_trace_extends_corner (X : Mat3Z)
    (hX : projector * X * projector = X) :
    Matrix.trace (projector * X * projector) = Matrix.trace X := by
  rw [hX]

/-- The failure of the compressed functional to be cyclic is measured exactly
by the commutator of the second input with the projector.  Thus the defect is
zero whenever `Y` preserves the compressed corner; it is not an unstructured
failure of trace cyclicity. -/
theorem compressed_trace_cyclic_defect (X Y : Mat3Z) :
    Matrix.trace (projector * (X * Y) * projector) -
        Matrix.trace (projector * (Y * X) * projector) =
      Matrix.trace (X * (Y * projector - projector * Y)) := by
  exact compressed_trace_defect projector X Y projector_idempotent

/-- Compression is cyclic on a pair whenever the right factor commutes with
the idempotent defining the corner. -/
theorem compressed_trace_cyclic_of_commutes (X Y : Mat3Z)
    (hYP : Y * projector = projector * Y) :
    Matrix.trace (projector * (X * Y) * projector) =
      Matrix.trace (projector * (Y * X) * projector) := by
  have h := compressed_trace_cyclic_defect X Y
  rw [hYP, sub_self] at h
  exact sub_eq_zero.mp (by simpa using h)

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
