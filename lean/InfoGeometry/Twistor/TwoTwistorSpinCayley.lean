/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.PerjesConventions
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Traceless two-twistor Gram invariants and Cayley rotation

The carrier is the full algebra of complex `2 × 2` matrices. The chosen
coordinate normalization is `S_i = Re(trace(H_tf * sigma_i)) / 4`, so its
squared length is `Re(trace(H_tf * H_tf)) / 8`. No Pauli--Lubanski or Wigner
identification is asserted. Matrix conjugation retains its multiplication
order; only scalar coefficient arithmetic is commutative.
-/

noncomputable section
namespace InfoGeometry.Twistor.TwoTwistorSpinCayley

open PenroseIncidence PerjesConventions
open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open Matrix
open scoped BigOperators Matrix

/-- Remove the scalar part using the actual complex matrix trace. -/
def traceFree (H : ComplexSpacetime) : ComplexSpacetime :=
  H - (H.trace / 2) • (1 : ComplexSpacetime)

/-- The quarter-trace Pauli readout; standard `sigma_2` fixes the y-axis sign. -/
def spinVector (H : ComplexSpacetime) : Fin 3 → ℝ :=
  ![(trace (traceFree H * σ1)).re / 4,
    (trace (traceFree H * σ2)).re / 4,
    (trace (traceFree H * σ3)).re / 4]

/-- Quadratic trace invariant. It is nonnegative for Hermitian input. -/
def spinNormSq (H : ComplexSpacetime) : ℝ :=
  (trace (traceFree H * traceFree H)).re / 8

/-- Hermitian coordinates with diagonal entries twice the two helicities. -/
def hermitianCoordinates (s₁ s₂ : ℝ) (τ : ℂ) : ComplexSpacetime :=
  !![((2 * s₁ : ℝ) : ℂ), τ;
      star τ, ((2 * s₂ : ℝ) : ℂ)]

@[simp] theorem hermitianCoordinates_conjTranspose (s₁ s₂ : ℝ) (τ : ℂ) :
    (hermitianCoordinates s₁ s₂ τ)ᴴ = hermitianCoordinates s₁ s₂ τ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianCoordinates]

/-- Every Hermitian matrix has these coordinates, with no diagonal restriction. -/
theorem eq_hermitianCoordinates (H : ComplexSpacetime) (hH : Hᴴ = H) :
    H = hermitianCoordinates ((H 0 0).re / 2) ((H 1 1).re / 2) (H 0 1) := by
  have h00 := congrArg Complex.im (congrFun (congrFun hH 0) 0)
  have h11 := congrArg Complex.im (congrFun (congrFun hH 1) 1)
  have h10 := congrFun (congrFun hH 1) 0
  have hi00 : (H 0 0).im = 0 := by
    have hi : -(H 0 0).im = (H 0 0).im := by simpa using h00
    linarith
  have hi11 : (H 1 1).im = 0 := by
    have hi : -(H 1 1).im = (H 1 1).im := by simpa using h11
    linarith
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext <;> simp [hermitianCoordinates, hi00]
  · simp [hermitianCoordinates]
  · simpa [hermitianCoordinates] using h10.symm
  · apply Complex.ext <;> simp [hermitianCoordinates, hi11]

@[simp] theorem trace_traceFree (H : ComplexSpacetime) : trace (traceFree H) = 0 := by
  simp [traceFree, Matrix.trace, Fin.sum_univ_two]
  ring

theorem traceFree_hermitianCoordinates (s₁ s₂ : ℝ) (τ : ℂ) :
    traceFree (hermitianCoordinates s₁ s₂ τ) =
      !![((s₁ - s₂ : ℝ) : ℂ), τ; star τ, -((s₁ - s₂ : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceFree, hermitianCoordinates, Matrix.trace, Fin.sum_univ_two] <;> ring

/-- Positive scalar square of a traceless Hermitian two-by-two matrix. -/
theorem traceFree_sq_hermitianCoordinates (s₁ s₂ : ℝ) (τ : ℂ) :
    traceFree (hermitianCoordinates s₁ s₂ τ) *
        traceFree (hermitianCoordinates s₁ s₂ τ) =
      (((s₁ - s₂) ^ 2 + Complex.normSq τ : ℝ) : ℂ) • (1 : ComplexSpacetime) := by
  simp only [traceFree_hermitianCoordinates]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_eq_conj_mul_self] <;> ring

/-- The chosen Pauli normalization gives half the usual Pauli coefficients. -/
theorem spinVector_hermitianCoordinates (s₁ s₂ : ℝ) (τ : ℂ) :
    spinVector (hermitianCoordinates s₁ s₂ τ) =
      ![τ.re / 2, -τ.im / 2, (s₁ - s₂) / 2] := by
  unfold spinVector
  simp only [traceFree_hermitianCoordinates]
  ext i
  fin_cases i <;>
    simp [σ1, σ2, σ3, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The correct trace sign is positive, and the quarter-trace factor is one eighth. -/
theorem spinNormSq_hermitianCoordinates (s₁ s₂ : ℝ) (τ : ℂ) :
    spinNormSq (hermitianCoordinates s₁ s₂ τ) =
      ((s₁ - s₂) ^ 2 + Complex.normSq τ) / 4 := by
  unfold spinNormSq
  rw [traceFree_sq_hermitianCoordinates]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/-- For arbitrary Hermitian input, the trace formula equals the Euclidean square
of the three real Pauli coordinates. -/
theorem spinNormSq_eq_sum_sq (H : ComplexSpacetime) (hH : Hᴴ = H) :
    spinNormSq H = ∑ i : Fin 3, spinVector H i ^ 2 := by
  rw [eq_hermitianCoordinates H hH, spinNormSq_hermitianCoordinates,
    spinVector_hermitianCoordinates]
  simp [Fin.sum_univ_three, Complex.normSq_apply]
  ring

theorem spinNormSq_nonneg (H : ComplexSpacetime) (hH : Hᴴ = H) :
    0 ≤ spinNormSq H := by
  rw [spinNormSq_eq_sum_sq H hH]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Cyclicity uses the two-sided inverse consequence for finite square matrices. -/
theorem trace_unitary_conjugate (H U : ComplexSpacetime) (hU : Uᴴ * U = 1) :
    trace (Uᴴ * H * U) = trace H := by
  have hright : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.trace_mul_cycle, hright, Matrix.one_mul]

/-- Removing the scalar part commutes with unitary conjugation. -/
theorem traceFree_unitary_conjugate (H U : ComplexSpacetime) (hU : Uᴴ * U = 1) :
    traceFree (Uᴴ * H * U) = Uᴴ * traceFree H * U := by
  simp only [traceFree, trace_unitary_conjugate H U hU, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]

/-- The entire quadratic invariant is preserved without assuming the input
matrix is diagonal or commuting with the frame change. -/
theorem spinNormSq_unitary_conjugate (H U : ComplexSpacetime) (hU : Uᴴ * U = 1) :
    spinNormSq (Uᴴ * H * U) = spinNormSq H := by
  have hright : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hprod : (Uᴴ * traceFree H * U) * (Uᴴ * traceFree H * U) =
      Uᴴ * (traceFree H * traceFree H) * U := by
    calc
      _ = Uᴴ * traceFree H * (U * Uᴴ) * traceFree H * U := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hright]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  simp only [spinNormSq, traceFree_unitary_conjugate H U hU, hprod,
    trace_unitary_conjugate (traceFree H * traceFree H) U hU]

/-- The actual normalized Cayley matrix, using the established Perjes scale. -/
def cayley : ComplexSpacetime := paperScale • !![(1 : ℂ), 1; -1, 1]

@[simp] theorem star_paperScale : star paperScale = paperScale := by
  simp [paperScale]

private lemma paperScale_mul_self : paperScale * paperScale = (1 / 2 : ℂ) := by
  linear_combination paperScale_sq / 2

/-- Concrete unitarity, not a field assumed in a witness structure. -/
theorem cayley_conjTranspose_mul : cayleyᴴ * cayley = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayley, Matrix.mul_apply, Fin.sum_univ_two, paperScale_mul_self] <;> ring

/-- Determinant one preserves the actual bivector, not merely its norm. -/
theorem cayley_det : cayley.det = 1 := by
  simp [cayley, Matrix.det_fin_two, paperScale_mul_self]

/-- Cayley conjugation transfers a diagonal difference to a real off-diagonal
entry with the indicated sign. -/
theorem cayley_helicity_to_crossing (s : ℝ) :
    cayleyᴴ * hermitianCoordinates s (-s) 0 * cayley =
      hermitianCoordinates 0 0 (2 * (s : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayley, hermitianCoordinates, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring_nf
  all_goals have hs : paperScale ^ 2 = (1 / 2 : ℂ) := by
    simpa only [pow_two] using paperScale_mul_self
  all_goals simp only [hs]
  all_goals ring

/-- The concrete nontrivial transition preserves the quadratic spin readout. -/
theorem spinNormSq_cayley (H : ComplexSpacetime) :
    spinNormSq (cayleyᴴ * H * cayley) = spinNormSq H :=
  spinNormSq_unitary_conjugate H cayley cayley_conjTranspose_mul

end InfoGeometry.Twistor.TwoTwistorSpinCayley
