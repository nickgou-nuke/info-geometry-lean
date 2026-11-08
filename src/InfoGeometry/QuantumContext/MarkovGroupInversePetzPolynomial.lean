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
-/

namespace InfoGeometry.QuantumContext

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

/-- Substituting a group inverse pair into the Petz recovery polynomial
reconstructs the compression of `L` by its regular idempotent. The theorem is
an algebraic polynomial identity and makes no positivity or channel claim. -/
theorem groupInverse_petzPolynomial_reconstructs {n : ℕ}
    (L G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse L G) :
    petzRecoveryMap (L * G) L G (causalChannel (L * G) L) =
      (L * G) * L * (L * G) := by
  have hP : (L * G) * (L * G) = L * G := by
    calc
      (L * G) * (L * G) = (L * G * L) * G := by noncomm_ring
      _ = L * G := by rw [hG.1]
  have hInv : L * G = L * G := rfl
  have hInvRev : G * L = L * G := hG.2.2.symm
  have hComm : L * (L * G) = (L * G) * L := by
    calc
      L * (L * G) = L * (G * L) := by rw [hG.2.2]
      _ = (L * G) * L := by noncomm_ring
  have hInvComm : G * (L * G) = (L * G) * G := by
    calc
      G * (L * G) = G * L * G := by noncomm_ring
      _ = L * G * G := by rw [← hG.2.2]
      _ = (L * G) * G := by noncomm_ring
  exact petz_reconstructs_reference_state (L * G) L G
    hP hInv hInvRev hComm hInvComm

/-- Markov-Laplacian specialization: when `G` is a group inverse of `1 - P`,
the same algebraic Petz-polynomial reconstruction holds for the regular
idempotent `(1 - P) * G`. No stochastic or positivity interpretation is
asserted by this identity alone. -/
theorem markovLaplacian_petzPolynomial_reconstructs {n : ℕ}
    (P G : Matrix (Fin n) (Fin n) ℝ)
    (hG : IsGroupInverse (1 - P) G) :
    petzRecoveryMap ((1 - P) * G) (1 - P) G
      (causalChannel ((1 - P) * G) (1 - P)) =
        ((1 - P) * G) * (1 - P) * ((1 - P) * G) := by
  exact groupInverse_petzPolynomial_reconstructs (1 - P) G hG

end InfoGeometry.QuantumContext
