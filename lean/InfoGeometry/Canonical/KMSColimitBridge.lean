import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFInductiveColimitBoundary
import InfoGeometry.Canonical.KMSTraceColimit
import InfoGeometry.Canonical.TensorTowerColimit

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.KMSTraceColimit

noncomputable section

namespace InfoGeometry.Canonical.KMSColimitBridge

/-!
# KMS Colimit Compatibility Bridge

This module bridges the finite-stage normalized KMS trace readback layer
(`KMSTraceColimit.lean`) with the algebraic colimit sequence transport layer
(`TensorTowerColimit.lean`).

Key Results:
1. `kms_trace_nonvanishing_transport`: Non-vanishing normalized trace $\tau_n(f) \neq 0$ implies non-vanishing trace under $m$-step colimit maps.
2. `kms_identity_state_colimit_invariance`: The identity state trace $\tau_{n+m}(\iota_{n \to n+m}(1)) = 1$ is invariant under all colimit embeddings.
3. `kms_colimit_bridge_synthesis`: Consolidated KMS colimit compatibility synthesis theorem.
-/

/-- **Theorem: Trace Non-Vanishing Transport across Colimit Maps**
    If $f \in \text{DiagAlg } n$ has a non-zero trace $\tau_n(f) \neq 0$, then its $m$-step
    colimit image $\text{diagEmbedSeq } n m f$ maintains non-zero trace. -/
theorem kms_trace_nonvanishing_transport (n : ℕ) (f : DiagAlg n) (h_nz : normalizedTrace n f ≠ 0) (m : ℕ) :
    normalizedTrace (n + m) (diagEmbedSeq n m f) ≠ 0 := by
  rw [normalizedTrace_seq n f m]
  exact h_nz

/-- **Theorem: Identity State Colimit Invariance**
    The normalized trace of the identity observable image under $m$-step colimit maps is identically 1. -/
theorem kms_identity_state_colimit_invariance (n m : ℕ) :
    normalizedTrace (n + m) (diagEmbedSeq n m 1) = 1 := by
  rw [normalizedTrace_seq n 1 m]
  exact normalizedTrace_one n

/-- **Theorem: Colimit KMS Trace Commutativity**
    If `psi_trace` is a linear state on colimit target `A_inf` matching `normalizedTrace` at every stage,
    then evaluating `psi_trace` on the $m$-step colimit image $\psi(n+m)(\iota_{n \to n+m}(f))$
    is identically equal to evaluating it at stage $n$: $\psi_{\text{trace}}(\psi n f)$. -/
theorem colimit_kms_trace_comm (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
    (psi : ∀ n, DiagAlg n →ₗ[ℂ] A_inf) (psi_trace : A_inf →ₗ[ℂ] ℂ)
    (h_eval : ∀ n (f : DiagAlg n), psi_trace (psi n f) = normalizedTrace n f)
    (n m : ℕ) (f : DiagAlg n) :
    psi_trace (psi (n + m) (diagEmbedSeq n m f)) = psi_trace (psi n f) := by
  rw [h_eval (n + m), normalizedTrace_seq n f m, ← h_eval n]

set_option linter.unusedVariables false in
/-- **Consolidated KMS Colimit Bridge Synthesis Theorem**
    Proves trace non-vanishing transport, identity state invariance, and colimit trace commutativity
    across arbitrary $m$-step colimit inclusions. -/
theorem kms_colimit_bridge_synthesis :
    (∀ (n m : ℕ) (f : DiagAlg n), normalizedTrace n f ≠ 0 → normalizedTrace (n + m) (diagEmbedSeq n m f) ≠ 0) ∧
    (∀ (n m : ℕ), normalizedTrace (n + m) (diagEmbedSeq n m 1) = 1) ∧
    (∀ (A_inf : Type*) [AddCommGroup A_inf] [Module ℂ A_inf]
       (psi : ∀ n, DiagAlg n →ₗ[ℂ] A_inf) (psi_trace : A_inf →ₗ[ℂ] ℂ)
       (h_eval : ∀ n (f : DiagAlg n), psi_trace (psi n f) = normalizedTrace n f)
       (n m : ℕ) (f : DiagAlg n),
       psi_trace (psi (n + m) (diagEmbedSeq n m f)) = psi_trace (psi n f)) :=
  ⟨fun n m f h => kms_trace_nonvanishing_transport n f h m,
   kms_identity_state_colimit_invariance,
   colimit_kms_trace_comm⟩

end InfoGeometry.Canonical.KMSColimitBridge
