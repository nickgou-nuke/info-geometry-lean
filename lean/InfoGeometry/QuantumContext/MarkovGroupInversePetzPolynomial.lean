/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin
import InfoGeometry.QuantumContext.PetzDataProcessingMonotonicity

/-!
# Algebraic Petz-polynomial readout for a matrix group inverse

For a matrix group inverse pair `(L, G)`, the regular idempotent `L * G`
satisfies the ring identities required by the Petz reconstruction polynomial.
This is only an algebraic substitution into that polynomial: it does not assert
that `L` is a density matrix or that `L * G` is a symmetric causal projector.

## BUCKET 1 — Algebraic support laws
`groupInverse_regularSupport_laws` proves idempotence and commutation for the
support `L * G` under the explicit group-inverse equations.

## BUCKET 2 — Conditional polynomial reconstruction
`groupInverse_petzPolynomial_reconstructs` applies the algebraic reconstruction
identity under those same group-inverse hypotheses.

## BUCKET 3 — Open analytic and channel claims
Positivity, trace normalization, complete positivity, and channel recovery are
not established by this matrix-ring substitution.
-/

namespace InfoGeometry.QuantumContext

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-- The regular support `L * G` of a group-inverse pair is an idempotent that
commutes with both members of the pair. These are the support-algebra laws
used when substituting a group inverse into the Petz reconstruction polynomial.
-/
theorem groupInverse_regularSupport_laws {n : ℕ}
    (L G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse L G) :
    (L * G) * (L * G) = L * G ∧
    L * (L * G) = (L * G) * L ∧
    G * (L * G) = (L * G) * G := by
  rcases hG with ⟨hLGL, hGLG, hcomm⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      (L * G) * (L * G) = (L * G * L) * G := by noncomm_ring
      _ = L * G := by rw [hLGL]
  · calc
      L * (L * G) = L * (G * L) := by rw [hcomm]
      _ = (L * G) * L := by noncomm_ring
  · calc
      G * (L * G) = (G * L) * G := by noncomm_ring
      _ = (L * G) * G := by rw [hcomm.symm]

/-- Substituting a group inverse pair into the Petz recovery polynomial
reconstructs the compression of `L` by its regular idempotent. The theorem is
an algebraic polynomial identity and makes no positivity or channel claim. -/
theorem groupInverse_petzPolynomial_reconstructs {n : ℕ}
    (L G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse L G) :
    petzRecoveryMap (L * G) L G (causalChannel (L * G) L) =
      (L * G) * L * (L * G) := by
  rcases groupInverse_regularSupport_laws L G hG with ⟨hP, hComm, hInvComm⟩
  have hInvRev : G * L = L * G := hG.2.2.symm
  exact petz_reconstructs_reference_state (L * G) L G
    hP rfl hInvRev hComm hInvComm

theorem markovLaplacian_petzPolynomial_reconstructs {n : ℕ}
    (P G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    petzRecoveryMap ((1 - P) * G) (1 - P) G
      (causalChannel ((1 - P) * G) (1 - P)) =
        ((1 - P) * G) * (1 - P) * ((1 - P) * G) := by
  exact groupInverse_petzPolynomial_reconstructs (1 - P) G hG

end InfoGeometry.QuantumContext
