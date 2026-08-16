import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic
import InfoGeometry.OperatorAlgebra.CuntzTomitaTakesaki

/-!
# Positive finite Tomita quadratic readout

The existing finite Tomita owner proves that the modularly weighted Tomita
operator cancels to the observable conjugate transpose. This file composes
that identity with matrix multiplication and records the resulting positive
semidefinite quadratic product.  All Tomita terminology here is local to this
finite matrix proxy; no standard-form or von Neumann-algebra theorem is
asserted.
-/

namespace InfoGeometry.OperatorAlgebra

open scoped Matrix

noncomputable def tomitaQuadratic
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  X * S_tomita δ X

theorem tomitaQuadratic_eq_observable_mul_conjTranspose
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    tomitaQuadratic δ X = X * X.conjTranspose := by
  unfold tomitaQuadratic
  rw [tomita_cuntz_cancellation]

theorem tomitaQuadratic_delta_invariant
    (δ₁ δ₂ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    tomitaQuadratic δ₁ X = tomitaQuadratic δ₂ X := by
  rw [tomitaQuadratic_eq_observable_mul_conjTranspose,
    tomitaQuadratic_eq_observable_mul_conjTranspose]

/-- Right multiplication by a unitary factor does not change the quadratic readout. -/
theorem tomitaQuadratic_right_unitary_invariant
    (δ : ℝ) (X U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * U.conjTranspose = 1) :
    tomitaQuadratic δ (X * U) = tomitaQuadratic δ X := by
  rw [tomitaQuadratic_eq_observable_mul_conjTranspose,
    tomitaQuadratic_eq_observable_mul_conjTranspose,
    Matrix.conjTranspose_mul]
  calc
    (X * U) * (U.conjTranspose * X.conjTranspose) =
        X * (U * U.conjTranspose) * X.conjTranspose := by
          noncomm_ring
    _ = X * X.conjTranspose := by rw [hU]; simp

/-- Right-unitary gauge invariance also preserves the quadratic trace. -/
theorem tomitaQuadratic_trace_right_unitary_invariant
    (δ : ℝ) (X U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * U.conjTranspose = 1) :
    Matrix.trace (tomitaQuadratic δ (X * U)) =
      Matrix.trace (tomitaQuadratic δ X) := by
  rw [tomitaQuadratic_right_unitary_invariant δ X U hU]

theorem tomitaQuadratic_trace_right_unitary_ne_zero
    (δ : ℝ) (X U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * U.conjTranspose = 1)
    (hTraceX : Matrix.trace (tomitaQuadratic δ X) ≠ 0) :
    Matrix.trace (tomitaQuadratic δ (X * U)) ≠ 0 := by
  rw [tomitaQuadratic_trace_right_unitary_invariant δ X U hU]
  exact hTraceX

/-- Left multiplication transports the quadratic readout by unitary conjugation. -/
theorem tomitaQuadratic_left_unitary_covariant
    (δ : ℝ) (X U : Matrix (Fin 2) (Fin 2) ℂ) :
    tomitaQuadratic δ (U * X) =
      U * tomitaQuadratic δ X * U.conjTranspose := by
  rw [tomitaQuadratic_eq_observable_mul_conjTranspose,
    tomitaQuadratic_eq_observable_mul_conjTranspose,
    Matrix.conjTranspose_mul]
  noncomm_ring

/-- A left-unitary conjugation preserves the trace of the quadratic readout. -/
theorem tomitaQuadratic_trace_left_unitary_invariant
    (δ : ℝ) (X U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U.conjTranspose * U = 1) :
    Matrix.trace (tomitaQuadratic δ (U * X)) =
      Matrix.trace (tomitaQuadratic δ X) := by
  rw [tomitaQuadratic_left_unitary_covariant]
  calc
    Matrix.trace (U * tomitaQuadratic δ X * U.conjTranspose) =
        Matrix.trace (U.conjTranspose * (U * tomitaQuadratic δ X)) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (tomitaQuadratic δ X) := by
      rw [← mul_assoc, hU, one_mul]

noncomputable def normalizedTomitaQuadratic
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hTrace : Matrix.trace (tomitaQuadratic δ X) ≠ 0) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix.trace (tomitaQuadratic δ X))⁻¹ • tomitaQuadratic δ X

/-- Normalized readouts transform by unitary conjugation on the left. -/
theorem normalizedTomitaQuadratic_left_unitary_covariant
    (δ : ℝ) (X U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U.conjTranspose * U = 1)
    (hTraceX : Matrix.trace (tomitaQuadratic δ X) ≠ 0)
    (hTraceU : Matrix.trace (tomitaQuadratic δ (U * X)) ≠ 0) :
    normalizedTomitaQuadratic δ (U * X) hTraceU =
      U * normalizedTomitaQuadratic δ X hTraceX * U.conjTranspose := by
  have hTrace : Matrix.trace (tomitaQuadratic δ (U * X)) =
      Matrix.trace (tomitaQuadratic δ X) :=
    tomitaQuadratic_trace_left_unitary_invariant δ X U hU
  unfold normalizedTomitaQuadratic
  rw [hTrace, tomitaQuadratic_left_unitary_covariant]
  simp [smul_mul_assoc, mul_smul_comm, mul_assoc]

/-- The normalized density readout is invariant under the right-unitary gauge. -/
theorem normalizedTomitaQuadratic_right_unitary_invariant
    (δ : ℝ) (X U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * U.conjTranspose = 1)
    (hTraceX : Matrix.trace (tomitaQuadratic δ X) ≠ 0)
    (hTraceU : Matrix.trace (tomitaQuadratic δ (X * U)) ≠ 0) :
    normalizedTomitaQuadratic δ (X * U) hTraceU =
      normalizedTomitaQuadratic δ X hTraceX := by
  have hQuad : tomitaQuadratic δ (X * U) = tomitaQuadratic δ X :=
    tomitaQuadratic_right_unitary_invariant δ X U hU
  unfold normalizedTomitaQuadratic
  rw [hQuad]

theorem normalizedTomitaQuadratic_right_unitary_invariant_of_trace_ne_zero
    (δ : ℝ) (X U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * U.conjTranspose = 1)
    (hTraceX : Matrix.trace (tomitaQuadratic δ X) ≠ 0) :
    normalizedTomitaQuadratic δ (X * U)
        (tomitaQuadratic_trace_right_unitary_ne_zero δ X U hU hTraceX) =
      normalizedTomitaQuadratic δ X hTraceX := by
  exact normalizedTomitaQuadratic_right_unitary_invariant δ X U hU
    hTraceX (tomitaQuadratic_trace_right_unitary_ne_zero δ X U hU hTraceX)

theorem tomitaQuadratic_isHermitian
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (tomitaQuadratic δ X).IsHermitian :=
  by
    rw [tomitaQuadratic_eq_observable_mul_conjTranspose]
    exact Matrix.isHermitian_mul_conjTranspose_self X

noncomputable def tomitaQuadraticRealTrace
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (Matrix.trace (tomitaQuadratic δ X)).re

theorem tomitaQuadraticRealTrace_eq_frobenius
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    tomitaQuadraticRealTrace δ X = ∑ i, ∑ j, Complex.normSq (X i j) := by
  simp [tomitaQuadraticRealTrace, tomitaQuadratic_eq_observable_mul_conjTranspose,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]

theorem tomitaQuadraticRealTrace_pos_of_ne_zero
    (δ : ℝ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ≠ 0) :
    0 < tomitaQuadraticRealTrace δ X := by
  rw [tomitaQuadraticRealTrace_eq_frobenius]
  apply Finset.sum_pos'
  · intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact Complex.normSq_nonneg _
  · obtain ⟨i, j, hij⟩ : ∃ i j, X i j ≠ 0 := by
      by_contra h
      apply hX
      funext i j
      by_contra hzero
      exact h ⟨i, j, hzero⟩
    exact ⟨i, Finset.mem_univ _,
      Finset.sum_pos' (fun j hj => Complex.normSq_nonneg _)
        ⟨j, Finset.mem_univ _, Complex.normSq_pos.mpr hij⟩⟩

/-- The quadratic trace vanishes exactly for the zero factor. -/
theorem tomitaQuadratic_trace_eq_zero_iff
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (tomitaQuadratic δ X) = 0 ↔ X = 0 := by
  constructor
  · intro hTrace
    by_contra hX
    have hpos := tomitaQuadraticRealTrace_pos_of_ne_zero δ hX
    have hreal : tomitaQuadraticRealTrace δ X = 0 := by
      simp [tomitaQuadraticRealTrace, hTrace]
    linarith
  · intro hX
    subst hX
    simp [tomitaQuadratic]

/-- Nonzero factors therefore provide their own normalization proof. -/
theorem tomitaQuadratic_trace_ne_zero_of_ne_zero
    (δ : ℝ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ≠ 0) :
    Matrix.trace (tomitaQuadratic δ X) ≠ 0 := by
  intro hTrace
  exact hX ((tomitaQuadratic_trace_eq_zero_iff δ X).mp hTrace)

theorem normalizedTomitaQuadratic_trace
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hTrace : Matrix.trace (tomitaQuadratic δ X) ≠ 0) :
    Matrix.trace (normalizedTomitaQuadratic δ X hTrace) = 1 := by
  unfold normalizedTomitaQuadratic
  rw [Matrix.trace_smul]
  rw [smul_eq_mul, inv_mul_cancel₀ hTrace]

theorem normalizedTomitaQuadratic_isHermitian_of_trace_ne_zero
    (δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ)
  (hTrace : Matrix.trace (tomitaQuadratic δ X) ≠ 0) :
    (normalizedTomitaQuadratic δ X hTrace).IsHermitian := by
  have hQ : (tomitaQuadratic δ X).IsHermitian := tomitaQuadratic_isHermitian δ X
  have htr : star (Matrix.trace (tomitaQuadratic δ X)) =
      Matrix.trace (tomitaQuadratic δ X) := by
    rw [← Matrix.trace_conjTranspose, hQ.eq]
  have hinv : star (Matrix.trace (tomitaQuadratic δ X))⁻¹ =
      (Matrix.trace (tomitaQuadratic δ X))⁻¹ := by
    rw [star_inv₀, htr]
  unfold normalizedTomitaQuadratic Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul]
  rw [hinv, hQ.eq]

end InfoGeometry.OperatorAlgebra
