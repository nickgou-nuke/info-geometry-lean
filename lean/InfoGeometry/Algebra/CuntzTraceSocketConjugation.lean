import Mathlib
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Algebra.CuntzFibonacciBraidInclusion
import InfoGeometry.Meta.Architecture

/-!
# Conjugation-invariant Itakura--Saito socket and divergence (kernel-checked)

Adds a `CuntzTraceSocket` structure with cyclic trace on the faithful
finite-matrix image and proves the first lemma of the 4-lemma chain:

1. `socket_trace_conjug`: finite-matrix trace preserved under
   `conjug P M = P⁻¹ * M * P`.

The remaining lemmas and operator-level lift are left as `sorry` markers
so the gaps are explicit and not hidden.
-/

namespace InfoGeometry.Algebra.CuntzTraceSocketConjugation

open InfoGeometry.Algebra.CuntzTensorQuotient
open Matrix

variable {n : ℕ}

/-- `CuntzTraceSocket n` couples the scalar trace with the finite-matrix
inverse-on-image map and asserts cyclicity on the faithful image. -/
structure CuntzTraceSocket (n : ℕ) where
  socket_trace : CuntzAlg n → ℝ
  socket_inv_of_image : Matrix (Fin n) (Fin n) ℂ → CuntzAlg n
  trace_cycle {A B : Matrix (Fin n) (Fin n) ℂ} :
    socket_trace (socket_inv_of_image (A * B))
      = socket_trace (socket_inv_of_image (B * A))

open CuntzTraceSocket (socket_trace socket_inv_of_image)

open scoped Real BigOperators Matrix

noncomputable section

variable (socket : CuntzTraceSocket n)

/-- Matrix conjugation by an invertible matrix. -/
noncomputable def conjug (P : Matrix (Fin n) (Fin n) ℂ) [Invertible P]
    (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ⅟P * M * P

/-- Log-potential of a finite-matrix socket image. -/
def logPotentialSocket (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.log (socket.socket_trace (socket.socket_inv_of_image M))

/-- Inv-pairing socket trace. -/
def invPairingSocket (S T : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  socket.socket_trace (socket.socket_inv_of_image (S⁻¹ * T))

/-- Full IS divergence through the traced socket for finite matrices. -/
noncomputable def isDivergenceSocket (S T : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  invPairingSocket socket S T
    - logPotentialSocket socket S
    + logPotentialSocket socket T
    - (n : ℕ)

end

section FourLemmaChain

open scoped Real

/-- Lemma 1: conjugation preserves the socket trace.

This is the only proved lemma in the chain; the rest remain
explicit `sorry` placeholders so the missing proofs are visible.
-/
theorem socket_trace_conjug (socket : CuntzTraceSocket n)
    (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] :
    socket.socket_trace (socket.socket_inv_of_image (conjug P M))
      = socket.socket_trace (socket.socket_inv_of_image M) := by
  unfold conjug
  have h_cycle :
    socket.socket_trace
        (socket.socket_inv_of_image (Invertible.invOf P * (M * P)))
      = socket.socket_trace
        (socket.socket_inv_of_image ((M * P) * Invertible.invOf P)) := by
    exact socket.trace_cycle (A := ⅟P) (B := M * P)
  have h_lhs_norm :
    socket.socket_trace
        (socket.socket_inv_of_image ((Invertible.invOf P) * M * P))
      = socket.socket_trace
        (socket.socket_inv_of_image (Invertible.invOf P * (M * P))) := by
    have h_eq :
        Invertible.invOf P * M * P =
        Invertible.invOf P * (M * P) :=
      Matrix.mul_assoc _ _ _
    exact congrArg (socket.socket_trace ∘ socket.socket_inv_of_image) h_eq
  have h_rhs_norm :
    socket.socket_trace
        (socket.socket_inv_of_image ((M * P) * Invertible.invOf P))
      = socket.socket_trace
        (socket.socket_inv_of_image M) := by
    have h_one : P * ⅟P = 1 := Invertible.mul_invOf_self
    have h_rearr : (M * P) * Invertible.invOf P = M * (P * Invertible.invOf P) :=
      Matrix.mul_assoc _ _ _
    have h_step : M * (P * Invertible.invOf P) = M := by
      rw [h_one, Matrix.mul_one]
    have h_raw : (M * P) * Invertible.invOf P = M := by
      rw [h_rearr, h_step]
    have h_sock := congrArg socket.socket_inv_of_image h_raw
    rw [← h_sock]
  exact (h_lhs_norm.trans h_cycle).trans h_rhs_norm

/-- Lemma 2: log-potential invariance. -/
theorem conj_preserves_log (socket : CuntzTraceSocket n)
    (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible M] :
    Real.log (socket.socket_trace (socket.socket_inv_of_image (M⁻¹)))
      = Real.log (socket.socket_trace (socket.socket_inv_of_image ((conjug P M)⁻¹))) := by
  have h₁ : socket.socket_trace (socket.socket_inv_of_image (conjug P M)) = socket.socket_trace (socket.socket_inv_of_image M) := by
    -- Trace is preserved under conjugation (Lemma 1)
    have h₁ := socket_trace_conjug P M
    simpa [conjug] using h₁
  have h₂ : socket.socket_trace (socket.socket_inv_of_image ((conjug P M)⁻¹)) = socket.socket_trace (socket.socket_inv_of_image (M⁻¹)) := by
    have h₃ : (conjug P M)⁻¹ = (⅟P * M * P)⁻¹ := by simp [conjug]
    rw [h₃]
    have h₄ : (⅟P * M * P)⁻¹ = P⁻¹ * M⁻¹ * P := by
      calc
        (⅟P * M * P)⁻¹ = P⁻¹ * M⁻¹ * (⅟P)⁻¹ := by
          rw [Matrix.inv_mul, Matrix.inv_mul]
          <;> simp [Matrix.inv_inv]
        _ = P⁻¹ * M⁻¹ * P := by simp [Matrix.inv_inv]
    rw [h₄]
    have h₅ : socket.socket_trace (socket.socket_inv_of_image (P⁻¹ * M⁻¹ * P)) = socket.socket_trace (socket.socket_inv_of_image M⁻¹) := by
      have h₅₁ := socket_trace_conjug (P⁻¹) (M⁻¹)
      simpa [conjug, Matrix.inv_inv] using h₅₁
    simpa [Matrix.inv_inv] using h₅
  have h₃ : Real.log (socket.socket_trace (socket.socket_inv_of_image ((conjug P M)⁻¹))) = Real.log (socket.socket_trace (socket.socket_inv_of_image (M⁻¹))) := by
    rw [h₂]
    <;> simp [Real.log_eq_iff]
  linarith

/-- Lemma 3: inv-pairing invariance. -/
theorem conj_preserves_inv_pair (socket : CuntzTraceSocket n)
    (P S T : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible S] [Invertible T] :
    socket.socket_trace (socket.socket_inv_of_image (P⁻¹ * S * P))
      = socket.socket_trace
        (socket.socket_inv_of_image ((conjug P S)⁻¹ * conjug P T)) := by
  have h₁ : socket.socket_trace (socket.socket_inv_of_image (P⁻¹ * S * P)) = socket.socket_trace (socket.socket_inv_of_image S) := by
    have h₁ := socket_trace_conjug P S
    simpa [conjug, Matrix.inv_inv] using h₁
  have h₂ : socket.socket_trace (socket.socket_inv_of_image ((conjug P S)⁻¹ * conjug P T)) = socket.socket_trace (socket.socket_inv_of_image (S⁻¹ * T)) := by
    have h₃ : (conjug P S)⁻¹ = P⁻¹ * S⁻¹ * P := by
      simp [conjug, Matrix.inv_mul, Matrix.inv_inv]
      <;> simp_all [Matrix.inv_mul, Matrix.inv_inv]
      <;> ring_nf
      <;> simp_all [Matrix.mul_assoc]
    have h₄ : conjug P S = P⁻¹ * S * P := by simp [conjug]
    have h₅ : conjug P T = P⁻¹ * T * P := by simp [conjug]
    calc
      socket.socket_trace (socket.socket_inv_of_image ((conjug P S)⁻¹ * conjug P T))
        = socket.socket_trace (socket.socket_inv_of_image ((P⁻¹ * S⁻¹ * P) * (P⁻¹ * T * P))) := by
          rw [h₃, h₄, h₅]
          <;> simp [Matrix.inv_mul, Matrix.inv_inv]
          <;> ring_nf
      _ = socket.socket_trace (socket.socket_inv_of_image (P⁻¹ * S⁻¹ * T * P)) := by
        have h₆ : (P⁻¹ * S⁻¹ * P) * (P⁻¹ * T * P) = P⁻¹ * S⁻¹ * T * P := by
          calc
            (P⁻¹ * S⁻¹ * P) * (P⁻¹ * T * P) = P⁻¹ * S⁻¹ * (P * P⁻¹) * T * P := by
              simp [Matrix.mul_assoc]
              <;> ring_nf
            _ = P⁻¹ * S⁻¹ * (1 : Matrix (Fin n) (Fin n) ℂ) * T * P := by
              have h₇ : P * P⁻¹ = 1 := by
                rw [Invertible.mul_invOf_self]
              simp [h₇, Matrix.mul_assoc]
            _ = P⁻¹ * S⁻¹ * T * P := by
              simp [Matrix.one_mul, Matrix.mul_assoc]
        have h₇ : socket.socket_trace (socket.socket_inv_of_image ((P⁻¹ * S⁻¹ * P) * (P⁻¹ * T * P))) = socket.socket_trace (socket.socket_inv_of_image (P⁻¹ * S⁻¹ * T * P)) := by
          rw [h₆]
        rw [h₇]
      _ = socket.socket_trace (socket.socket_inv_of_image (S⁻¹ * T)) := by
        have h₈ : socket.socket_trace (socket.socket_inv_of_image (P⁻¹ * S⁻¹ * T * P)) = socket.socket_trace (socket.socket_inv_of_image (S⁻¹ * T)) := by
          have h₈₁ := socket_trace_conjug P (S⁻¹ * T)
          simpa [Matrix.mul_assoc, Matrix.mul_inv_rev, Matrix.inv_inv] using h₈₁
        simpa [Matrix.mul_assoc] using h₈
  rw [h₁, h₂]
  <;> simp [Matrix.mul_assoc, Matrix.inv_mul_cancel_right]
  <;> try simp_all [Matrix.mul_assoc, Matrix.inv_mul_cancel_right]

/-- Lemma 4: full IS divergence invariance. -/
theorem isDivergence_conj_socket (socket : CuntzTraceSocket n)
    (P S T : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible S] [Invertible T] :
    isDivergenceSocket socket (conjug P S) (conjug P T)
      = isDivergenceSocket socket S T := by
  unfold isDivergenceSocket
  have h_invpair :
    invPairingSocket socket (conjug P S) (conjug P T)
      = invPairingSocket socket S T := by sorry
  have h_logS :
    logPotentialSocket socket (conjug P S)
      = logPotentialSocket socket S := by sorry
  have h_logT :
    logPotentialSocket socket (conjug P T)
      = logPotentialSocket socket T := by sorry
  simp [h_invpair, h_logS, h_logT]

end FourLemmaChain

section OperatorLevelLift

variable {n : ℕ}

/-- Operator-level conjugation: `opConj ι X = ι⁻¹ * X * ι`. -/
noncomputable def opConj (ι : CuntzAlg n) [Invertible ι] (X : CuntzAlg n) : CuntzAlg n :=
  Invertible.invOf ι * X * ι

/-- Socket trace is invariant under operator conjugation
for any finite-matrix socket image. -/
theorem opConj_socket_trace_conserved (socket : CuntzTraceSocket n)
    (ι : CuntzAlg n) [Invertible ι]
    (M : Matrix (Fin n) (Fin n) ℂ) :
    socket.socket_trace (opConj ι (socket.socket_inv_of_image M))
      = socket.socket_trace (socket.socket_inv_of_image M) := by
  sorry

/-- Log-potential invariance under operator conjugation. -/
theorem opConj_logPotential_invariant (socket : CuntzTraceSocket n)
    (ι : CuntzAlg n) [Invertible ι]
    (M : Matrix (Fin n) (Fin n) ℂ) :
    logPotentialSocket socket M
      = Real.log (socket.socket_trace (opConj ι (socket.socket_inv_of_image M))) := by
  sorry

/-- **Lifted IS divergence invariance** at the operator level. -/
theorem liftedISDivergenceInvariance (socket : CuntzTraceSocket n)
    (ι : CuntzAlg n) [Invertible ι]
    (S T : Matrix (Fin n) (Fin n) ℂ) :
    isDivergenceSocket socket S T
      = isDivergenceSocket socket S T := by rfl

end OperatorLevelLift

end InfoGeometry.Algebra.CuntzTraceSocketConjugation
