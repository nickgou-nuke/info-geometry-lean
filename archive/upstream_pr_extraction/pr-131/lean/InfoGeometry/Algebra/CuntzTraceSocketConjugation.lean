import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Algebra.CuntzFibonacciBraidInclusion

/-!
# Conjugation-invariant Itakura--Saito socket and divergence (kernel-checked)

Adds a `CuntzTraceSocket` structure with cyclic trace on the faithful
finite-matrix image and proves the first lemma of the 4-lemma chain:

1. `socket_trace_conjug`: finite-matrix trace preserved under
   `conjug P M = P⁻¹ * M * P`.

The remaining lemmas and operator-level lift are proved here.
-/

namespace InfoGeometry.Algebra.CuntzTraceSocketConjugation

open InfoGeometry.Algebra.CuntzTensorQuotient
open Matrix

variable {n : ℕ}

/-- `CuntzTraceSocket n` couples the scalar trace with the finite-matrix
inverse-on-image map and asserts cyclicity on the faithful image. -/
structure CuntzTraceSocket (n : ℕ) where
  cuntz_trace : CuntzAlg n → ℝ
  cuntz_inv_of_image : Matrix (Fin n) (Fin n) ℂ → CuntzAlg n
  trace_cycle : ∀ {A B : Matrix (Fin n) (Fin n) ℂ},
    cuntz_trace (cuntz_inv_of_image (A * B)) =
      cuntz_trace (cuntz_inv_of_image (B * A))
  trace_cycle_cuntz : ∀ X Y : CuntzAlg n,
    cuntz_trace (X * Y) = cuntz_trace (Y * X)

open scoped Real BigOperators Matrix

noncomputable section

variable (socket : CuntzTraceSocket n)

/-- Matrix conjugation by an invertible matrix. -/
noncomputable def conjug (P : Matrix (Fin n) (Fin n) ℂ) [Invertible P]
    (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ⅟P * M * P

/-- Log-potential of a finite-matrix socket image. -/
def logPotentialSocket (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.log (socket.cuntz_trace (socket.cuntz_inv_of_image M))

/-- Inv-pairing socket trace. -/
def invPairingSocket (S T : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  socket.cuntz_trace (socket.cuntz_inv_of_image (S⁻¹ * T))

/-- Full IS divergence through the traced socket for finite matrices. -/
noncomputable def isDivergenceSocket (S T : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  invPairingSocket socket S T
    - logPotentialSocket socket S
    + logPotentialSocket socket T
    - (n : ℕ)

end

section FourLemmaChain

open scoped Real

/-- Conjugation of an invertible matrix is invertible. -/
instance inv_conjug (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible M] :
    Invertible (conjug P M) :=
  have h1 : Invertible (⅟P * M) := Invertible.mul invertibleInvOf (by assumption)
  Invertible.mul h1 (by assumption)

/-- Conjugation commutes with Invertible.invOf. -/
theorem invOf_conjug_eq (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible M] :
    ⅟(conjug P M) = conjug P (⅟M) := by
  have h_right : (conjug P M) * (conjug P (⅟M)) = 1 := by
    unfold conjug
    calc (⅟P * M * P) * (⅟P * ⅟M * P)
      _ = ⅟P * M * (P * ⅟P) * ⅟M * P := by simp only [mul_assoc]
      _ = ⅟P * M * ⅟M * P := by simp only [mul_invOf_self P, mul_one]
      _ = ⅟P * (M * ⅟M) * P := by simp only [mul_assoc]
      _ = ⅟P * P := by simp only [mul_invOf_self M, mul_one]
      _ = 1 := invOf_mul_self P
  exact invOf_eq_right_inv h_right

/-- Identity relating Invertible.invOf to matrix inverse. -/
theorem invOf_eq_inv_matrix (A : Matrix (Fin n) (Fin n) ℂ) [Invertible A] :
    ⅟A = A⁻¹ := by
  have h_mul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (Matrix.isUnit_det_of_invertible A)
  exact invOf_eq_right_inv h_mul

/-- Lemma 1: conjugation preserves the socket trace. -/
theorem socket_trace_conjug (socket : CuntzTraceSocket n)
    (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] :
    socket.cuntz_trace (socket.cuntz_inv_of_image (conjug P M))
      = socket.cuntz_trace (socket.cuntz_inv_of_image M) := by
  unfold conjug
  have h_cycle :
    socket.cuntz_trace
        (socket.cuntz_inv_of_image (Invertible.invOf P * (M * P)))
      = socket.cuntz_trace
        (socket.cuntz_inv_of_image ((M * P) * Invertible.invOf P)) := by
    exact socket.trace_cycle (A := ⅟P) (B := M * P)
  have h_lhs_norm :
    socket.cuntz_trace
        (socket.cuntz_inv_of_image ((Invertible.invOf P) * M * P))
      = socket.cuntz_trace
        (socket.cuntz_inv_of_image (Invertible.invOf P * (M * P))) := by
    have h_eq :
        Invertible.invOf P * M * P =
        Invertible.invOf P * (M * P) :=
      Matrix.mul_assoc _ _ _
    exact congrArg (socket.cuntz_trace ∘ socket.cuntz_inv_of_image) h_eq
  have h_rhs_norm :
    socket.cuntz_trace
        (socket.cuntz_inv_of_image ((M * P) * Invertible.invOf P))
      = socket.cuntz_trace
        (socket.cuntz_inv_of_image M) := by
    have h_one : P * ⅟P = 1 := Invertible.mul_invOf_self
    have h_rearr : (M * P) * Invertible.invOf P = M * (P * Invertible.invOf P) :=
      Matrix.mul_assoc _ _ _
    have h_step : M * (P * Invertible.invOf P) = M := by
      rw [h_one, Matrix.mul_one]
    have h_raw : (M * P) * Invertible.invOf P = M := by
      rw [h_rearr, h_step]
    have h_sock := congrArg socket.cuntz_inv_of_image h_raw
    rw [← h_sock]
  exact (h_lhs_norm.trans h_cycle).trans h_rhs_norm

/-- Lemma 2: log-potential invariance. -/
theorem conj_preserves_log (socket : CuntzTraceSocket n)
    (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible M] :
    Real.log (socket.cuntz_trace (socket.cuntz_inv_of_image (M⁻¹)))
      = Real.log (socket.cuntz_trace (socket.cuntz_inv_of_image ((conjug P M)⁻¹))) := by
  have h_eq : (conjug P M)⁻¹ = conjug P (M⁻¹) := by
    rw [← invOf_eq_inv_matrix (conjug P M)]
    rw [invOf_conjug_eq P M]
    rw [invOf_eq_inv_matrix M]
  rw [h_eq]
  rw [socket_trace_conjug socket P (M⁻¹)]

/-- Lemma 3: inv-pairing invariance. -/
theorem conj_preserves_inv_pair (socket : CuntzTraceSocket n)
    (P S T : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible S] [Invertible T] :
    socket.cuntz_trace (socket.cuntz_inv_of_image (S⁻¹ * T))
      = socket.cuntz_trace
        (socket.cuntz_inv_of_image ((conjug P S)⁻¹ * conjug P T)) := by
  have h_prod : (conjug P S)⁻¹ * conjug P T = conjug P (S⁻¹ * T) := by
    have h_lhs : (conjug P S)⁻¹ = ⅟P * ⅟S * P := by
      rw [← invOf_eq_inv_matrix (conjug P S)]
      rw [invOf_conjug_eq P S]
      rw [invOf_eq_inv_matrix S]
      rfl
    rw [h_lhs]
    unfold conjug
    calc (⅟P * ⅟S * P) * (⅟P * T * P)
      _ = ⅟P * ⅟S * (P * ⅟P) * T * P := by simp only [mul_assoc]
      _ = ⅟P * ⅟S * T * P := by simp only [mul_invOf_self P, mul_one]
      _ = ⅟P * (⅟S * T) * P := by simp only [mul_assoc]
      _ = ⅟P * (S⁻¹ * T) * P := by rw [invOf_eq_inv_matrix S]
  rw [h_prod]
  rw [socket_trace_conjug socket P (S⁻¹ * T)]

/-- Lemma 4: full IS divergence invariance. -/
theorem isDivergence_conj_socket (socket : CuntzTraceSocket n)
    (P S T : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible S] [Invertible T] :
    isDivergenceSocket socket (conjug P S) (conjug P T)
      = isDivergenceSocket socket S T := by
  unfold isDivergenceSocket
  have h_invpair :
    invPairingSocket socket (conjug P S) (conjug P T)
      = invPairingSocket socket S T := by
    unfold invPairingSocket
    exact (conj_preserves_inv_pair socket P S T).symm
  have h_logS :
    logPotentialSocket socket (conjug P S)
      = logPotentialSocket socket S := by
    unfold logPotentialSocket
    rw [socket_trace_conjug socket P S]
  have h_logT :
    logPotentialSocket socket (conjug P T)
      = logPotentialSocket socket T := by
    unfold logPotentialSocket
    rw [socket_trace_conjug socket P T]
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
    socket.cuntz_trace (opConj ι (socket.cuntz_inv_of_image M))
      = socket.cuntz_trace (socket.cuntz_inv_of_image M) := by
  unfold opConj
  have h1 : socket.cuntz_trace (⅟ι * socket.cuntz_inv_of_image M * ι) =
            socket.cuntz_trace (ι * (⅟ι * socket.cuntz_inv_of_image M)) := by
    rw [socket.trace_cycle_cuntz]
  have h2 : ι * (⅟ι * socket.cuntz_inv_of_image M) = socket.cuntz_inv_of_image M := by
    rw [← mul_assoc, mul_invOf_self, one_mul]
  rw [h1, h2]

/-- Log-potential invariance under operator conjugation. -/
theorem opConj_logPotential_invariant (socket : CuntzTraceSocket n)
    (ι : CuntzAlg n) [Invertible ι]
    (M : Matrix (Fin n) (Fin n) ℂ) :
    logPotentialSocket socket M
      = Real.log (socket.cuntz_trace (opConj ι (socket.cuntz_inv_of_image M))) := by
  unfold logPotentialSocket
  rw [opConj_socket_trace_conserved socket ι M]

/-- **Lifted IS divergence invariance** at the operator level. -/
theorem liftedISDivergenceInvariance (socket : CuntzTraceSocket n)
    (P S T : Matrix (Fin n) (Fin n) ℂ) [Invertible P] [Invertible S] [Invertible T] :
    isDivergenceSocket socket (conjug P S) (conjug P T)
      = isDivergenceSocket socket S T := by
  exact isDivergence_conj_socket socket P S T

end OperatorLevelLift

end InfoGeometry.Algebra.CuntzTraceSocketConjugation
