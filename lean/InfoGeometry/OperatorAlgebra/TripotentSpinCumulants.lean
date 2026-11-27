/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-! # Tripotent spin Cartan states in a full matrix algebra

This file develops a finite-matrix Cartan family from a self-adjoint
tripotent. The state operators remain elements of `Matrix n n ℝ`; scalar
coordinates are obtained only by the explicitly stated matrix trace. The
partition and moment formulas are conditional on the actual traces of the
three spectral idempotents.
-/

noncomputable section

open Matrix

namespace InfoGeometry.OperatorAlgebra.TripotentSpinCumulants

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℝ

/-- The zero, positive, and negative spectral idempotents of a tripotent. -/
def Pzero (S : Mat) : Mat := 1 - S * S
def Pplus (S : Mat) : Mat := (1 / 2 : ℝ) • (S * S + S)
def Pminus (S : Mat) : Mat := (1 / 2 : ℝ) • (S * S - S)

/-- Algebraic spectral relations, retaining the full matrix carrier. -/
theorem tripotent_spectral_idempotents (S : Mat)
    (hS : S * S * S = S) :
    Pzero S + Pplus S + Pminus S = 1 ∧
    Pzero S * Pzero S = Pzero S ∧
    Pplus S * Pplus S = Pplus S ∧
    Pminus S * Pminus S = Pminus S ∧
    Pzero S * Pplus S = 0 ∧ Pplus S * Pzero S = 0 ∧
    Pzero S * Pminus S = 0 ∧ Pminus S * Pzero S = 0 ∧
    Pplus S * Pminus S = 0 ∧ Pminus S * Pplus S = 0 := by
  have h2 : S * S * (S * S) = S * S := by
    calc S * S * (S * S) = (S * S * S) * S := by noncomm_ring
      _ = S * S := by rw [hS]
  have h3 : S * (S * S) = S := by rw [← mul_assoc, hS]
  dsimp [Pzero, Pplus, Pminus]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    ring
  · calc (1 - S * S) * (1 - S * S)
        = 1 - (S * S + S * S) + S * S * (S * S) := by noncomm_ring
      _ = 1 - S * S := by rw [h2]; noncomm_ring
  · have hs : (S * S + S) * (S * S + S) = (2 : ℝ) • (S * S + S) := by
      calc (S * S + S) * (S * S + S)
          = S * S * (S * S) + S * S * S + S * (S * S) + S * S := by noncomm_ring
        _ = (S * S + S) + (S * S + S) := by rw [h2, hS, h3]; abel
        _ = (2 : ℝ) • (S * S + S) := (two_smul ℝ _).symm
    rw [smul_mul_assoc, mul_smul_comm, hs, smul_smul, smul_smul]
    norm_num
  · have hs : (S * S - S) * (S * S - S) = (2 : ℝ) • (S * S - S) := by
      calc (S * S - S) * (S * S - S)
          = S * S * (S * S) - S * S * S - S * (S * S) + S * S := by noncomm_ring
        _ = (S * S - S) + (S * S - S) := by rw [h2, hS, h3]; noncomm_ring
        _ = (2 : ℝ) • (S * S - S) := (two_smul ℝ _).symm
    rw [smul_mul_assoc, mul_smul_comm, hs, smul_smul, smul_smul]
    norm_num
  · rw [mul_smul_comm]
    have hs : (1 - S * S) * (S * S + S) = 0 := by
      calc (1 - S * S) * (S * S + S)
          = S * S + S - (S * S * (S * S) + S * S * S) := by noncomm_ring
        _ = 0 := by rw [h2, hS]; noncomm_ring
    rw [hs, smul_zero]
  · rw [smul_mul_assoc]
    have hs : (S * S + S) * (1 - S * S) = 0 := by
      calc (S * S + S) * (1 - S * S)
          = S * S + S - (S * S * (S * S) + S * (S * S)) := by noncomm_ring
        _ = 0 := by rw [h2, h3]; noncomm_ring
    rw [hs, smul_zero]
  · rw [mul_smul_comm]
    have hs : (1 - S * S) * (S * S - S) = 0 := by
      calc (1 - S * S) * (S * S - S)
          = S * S - S - (S * S * (S * S) - S * S * S) := by noncomm_ring
        _ = 0 := by rw [h2, hS]; noncomm_ring
    rw [hs, smul_zero]
  · rw [smul_mul_assoc]
    have hs : (S * S - S) * (1 - S * S) = 0 := by
      calc (S * S - S) * (1 - S * S)
          = S * S - S - (S * S * (S * S) - S * (S * S)) := by noncomm_ring
        _ = 0 := by rw [h2, h3]; noncomm_ring
    rw [hs, smul_zero]
  · rw [smul_mul_assoc, mul_smul_comm]
    have hs : (S * S + S) * (S * S - S) = 0 := by
      calc (S * S + S) * (S * S - S)
          = S * S * (S * S) - S * S * S + S * (S * S) - S * S := by noncomm_ring
        _ = 0 := by rw [h2, hS, h3]; noncomm_ring
    rw [hs, smul_zero, smul_zero]
  · rw [smul_mul_assoc, mul_smul_comm]
    have hs : (S * S - S) * (S * S + S) = 0 := by
      calc (S * S - S) * (S * S + S)
          = S * S * (S * S) + S * S * S - S * (S * S) - S * S := by noncomm_ring
        _ = 0 := by rw [h2, hS, h3]; noncomm_ring
    rw [hs, smul_zero, smul_zero]

/-- Explicit matrix non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem matrix_fin2_noncomm_witness :
    !![(0 : ℝ), 1; 0, 0] * !![(0 : ℝ), 0; 1, 0] ≠
      !![(0 : ℝ), 0; 1, 0] * !![(0 : ℝ), 1; 0, 0] := by
  intro h
  have h00 := congr_fun (congr_fun h 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00
  norm_num at h00

/-- The finite-matrix Cartan exponential, expressed in its three spectral
idempotents. This is a matrix operator, not a scalar or diagonal surrogate. -/
def cartanWeight (S : Mat) (θ₁ θ₂ : ℝ) : Mat :=
  Pzero S + Real.exp (θ₂ + θ₁) • Pplus S + Real.exp (θ₂ - θ₁) • Pminus S

/-- Partition-function and trace-multiplicity hypotheses for the Cartan family. -/
structure TraceMultiplicity (S : Mat) where
  tripotent : S * S * S = S
  d0 : ℝ
  d : ℝ
  trace_zero : Matrix.trace (Pzero S) = d0
  trace_plus : Matrix.trace (Pplus S) = d
  trace_minus : Matrix.trace (Pminus S) = d

namespace TraceMultiplicity

/-- The trace partition function of the matrix-valued Cartan weight. -/
def partition {S : Mat} (T : TraceMultiplicity S) (θ₁ θ₂ : ℝ) : ℝ :=
  Matrix.trace (cartanWeight S θ₁ θ₂)

private lemma scalar_partition_id (d0 d x y : ℝ) :
    d0 + Real.exp (x + y) * d + Real.exp (x - y) * d =
      d0 + 2 * d * Real.exp x * Real.cosh y := by
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_add, Real.exp_sub, div_eq_mul_inv]
  ring

private lemma scalar_spin_id (d x y : ℝ) :
    Real.exp (x + y) * d + Real.exp (x - y) * (-d) =
      2 * d * Real.exp x * Real.sinh y := by
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_add, Real.exp_sub, div_eq_mul_inv]
  ring

private lemma scalar_quad_id (d x y : ℝ) :
    Real.exp (x + y) * d + Real.exp (x - y) * d =
      2 * d * Real.exp x * Real.cosh y := by
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_add, Real.exp_sub, div_eq_mul_inv]
  ring

/-- Matrix-trace partition formula; no diagonalization is used. -/
theorem partition_eq {S : Mat} (T : TraceMultiplicity S) (θ₁ θ₂ : ℝ) :
    T.partition θ₁ θ₂ = T.d0 + 2 * T.d * Real.exp θ₂ * Real.cosh θ₁ := by
  unfold partition cartanWeight
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    smul_eq_mul, smul_eq_mul, T.trace_zero, T.trace_plus, T.trace_minus]
  exact scalar_partition_id T.d0 T.d θ₂ θ₁

/-- The two matrix-valued first moments are the full-matrix trace readouts. -/
def spinMoment {S : Mat} (T : TraceMultiplicity S) (θ₁ θ₂ : ℝ) : ℝ :=
  Matrix.trace (S * cartanWeight S θ₁ θ₂) / T.partition θ₁ θ₂

def quadrupoleMoment {S : Mat} (T : TraceMultiplicity S) (θ₁ θ₂ : ℝ) : ℝ :=
  Matrix.trace (S * S * cartanWeight S θ₁ θ₂) / T.partition θ₁ θ₂

/-- Exact trace moments of `S` and `S²` for the finite matrix Cartan weight. -/
theorem moments_eq {S : Mat} (T : TraceMultiplicity S) (θ₁ θ₂ : ℝ) :
    T.spinMoment θ₁ θ₂ =
        2 * T.d * Real.exp θ₂ * Real.sinh θ₁ / T.partition θ₁ θ₂ ∧
    T.quadrupoleMoment θ₁ θ₂ =
        2 * T.d * Real.exp θ₂ * Real.cosh θ₁ / T.partition θ₁ θ₂ := by
  have hS3 : S * S * S = S := T.tripotent
  have hS4 : S * (S * S * S) = S * S := by rw [hS3]
  have hS4' : S * S * (S * S) = S * S := by simpa [mul_assoc] using hS4
  have hS_Pz : S * Pzero S = 0 := by
    dsimp [Pzero]
    calc S * (1 - S * S) = S - S * S * S := by noncomm_ring
      _ = 0 := by rw [hS3, sub_self]
  have hS_Pp : S * Pplus S = Pplus S := by
    dsimp [Pplus]
    rw [mul_smul_comm]
    congr 1
    calc S * (S * S + S) = S * S * S + S * S := by noncomm_ring
      _ = S * S + S := by rw [hS3]; abel
  have hS_Pm : S * Pminus S = -Pminus S := by
    dsimp [Pminus]
    rw [mul_smul_comm, ← smul_neg]
    congr 1
    calc S * (S * S - S) = S * S * S - S * S := by noncomm_ring
      _ = -(S * S - S) := by rw [hS3]; noncomm_ring
  have hS2_Pz : S * S * Pzero S = 0 := by
    dsimp [Pzero]
    calc S * S * (1 - S * S) = S * S - S * S * (S * S) := by noncomm_ring
      _ = 0 := by rw [hS4', sub_self]
  have hS2_Pp : S * S * Pplus S = Pplus S := by
    dsimp [Pplus]
    rw [mul_smul_comm]
    congr 1
    calc S * S * (S * S + S) = S * S * (S * S) + (S * S * S) := by noncomm_ring
      _ = S * S + S := by rw [hS4', hS3]
  have hS2_Pm : S * S * Pminus S = Pminus S := by
    dsimp [Pminus]
    rw [mul_smul_comm]
    congr 1
    calc S * S * (S * S - S) = S * S * (S * S) - (S * S * S) := by noncomm_ring
      _ = S * S - S := by rw [hS4', hS3]
  constructor
  · unfold spinMoment cartanWeight
    rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm, hS_Pz, hS_Pp, hS_Pm, zero_add]
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_neg,
      smul_eq_mul, smul_eq_mul, T.trace_plus, T.trace_minus]
    exact congrArg (· / T.partition θ₁ θ₂) (scalar_spin_id T.d θ₂ θ₁)
  · unfold quadrupoleMoment cartanWeight
    rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm, hS2_Pz, hS2_Pp, hS2_Pm, zero_add]
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, T.trace_plus, T.trace_minus]
    exact congrArg (· / T.partition θ₁ θ₂) (scalar_quad_id T.d θ₂ θ₁)

end TraceMultiplicity
end InfoGeometry.OperatorAlgebra.TripotentSpinCumulants
