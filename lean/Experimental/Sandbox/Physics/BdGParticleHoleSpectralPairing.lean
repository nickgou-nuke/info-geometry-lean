import InfoGeometry.Canonical.PhysicalBdGPairingBridgeAntiLinear

/-!
# Finite-dimensional spectral pairing from anti-linear BdG symmetry

This file reuses the canonical conjugate-linear Nambu sheet swap.  Its main
theorem states the spectral consequence of particle-hole covariance for a
momentum-indexed family: an eigenvector at momentum `k` and eigenvalue `z` is
sent to an eigenvector at the reversed momentum and eigenvalue `-conj z`.

The theorem is conditional on the actual anti-linear covariance identity and
an involutive one-particle conjugation.  The matrix-level statement records
the concrete map `v ↦ U · conj(v)`.  It makes no claim
that this structure identifies BdG systems with relativistic spacetime,
Krein CPT, or Majorana braiding.
-/

noncomputable section

namespace InfoGeometry.Experimental.BdGParticleHoleSpectralPairing

open ContinuousLinearMap
open InfoGeometry.Canonical.PhysicalBdGPairingBridgeAntiLinear

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "EndH" => H →L[ℂ] H
local notation "AntiEndH" => H →L⋆[ℂ] H
local notation "NambuH" => H × H
local notation "EndNambu" => NambuH →L[ℂ] NambuH

/-! ## Explicit finite-matrix particle-hole map -/

/-- The anti-linear map `v ↦ U · conj(v)` on a finite complex coordinate space. -/
def matrixParticleHole {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : Fin n → ℂ :=
  U.mulVec (fun i => star (v i))

/-- The explicit matrix particle-hole map is conjugate-linear. -/
theorem matrixParticleHole_smul {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (v : Fin n → ℂ) :
    matrixParticleHole U (z • v) = star z • matrixParticleHole U v := by
  ext i
  simp [matrixParticleHole, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_left_comm]

/--
If `U · conj` is an involution, it transports eigenvectors across a
momentum-reversing particle-hole covariance relation.  The eigenvalue is
`-conj(z)`; for real `z`, this is the familiar `-z` pairing.
-/
theorem matrix_eigenvector_pairing {n : ℕ} {κ : Type*}
    (U : Matrix (Fin n) (Fin n) ℂ)
    (Hamiltonian : κ → Matrix (Fin n) (Fin n) ℂ)
    (momentumReversal : κ → κ) (k : κ)
    (hC2 : ∀ v : Fin n → ℂ,
      matrixParticleHole U (matrixParticleHole U v) = v)
    (hCovariant : ∀ v : Fin n → ℂ,
      matrixParticleHole U ((Hamiltonian k).mulVec v) =
        -((Hamiltonian (momentumReversal k)).mulVec (matrixParticleHole U v)))
    (v : Fin n → ℂ) (z : ℂ)
    (hv : (Hamiltonian k).mulVec v = z • v) (hv0 : v ≠ 0) :
    matrixParticleHole U v ≠ 0 ∧
      (Hamiltonian (momentumReversal k)).mulVec (matrixParticleHole U v) =
        (-star z) • matrixParticleHole U v := by
  have htransport :
      (Hamiltonian (momentumReversal k)).mulVec (matrixParticleHole U v) =
        (-star z) • matrixParticleHole U v := by
    have h := congrArg (matrixParticleHole U) hv
    rw [hCovariant v, matrixParticleHole_smul] at h
    have h' := congrArg Neg.neg h
    simpa [neg_smul] using h'
  refine ⟨?_, htransport⟩
  intro hzero
  have htwice := congrArg (matrixParticleHole U) hzero
  have hvzero : v = 0 := by
    rw [hC2 v] at htwice
    have hzeroMap : matrixParticleHole U 0 = 0 := by
      unfold matrixParticleHole
      simp only [Pi.zero_apply, star_zero]
      exact Matrix.mulVec_zero U
    exact htwice.trans hzeroMap
  exact hv0 hvzero

/--
Spectral pairing for an anti-linear particle-hole involution on a complex
Hilbert space.  The anti-linear Nambu map is the canonical sheet swap from
`PhysicalBdGPairingBridgeAntiLinear`; `hCovariant` is the operator
particle-hole relation, including momentum reversal in the family.  The
explicit finite-coordinate matrix version is `matrix_eigenvector_pairing`.
-/
theorem eigenvector_transport
    (C₀ : AntiEndH)
    (hC₀ : ∀ x : H, C₀ (C₀ x) = x)
    {κ : Type*} (Hamiltonian : κ → EndNambu)
    (momentumReversal : κ → κ) (k : κ)
    (hCovariant : ∀ ψ : NambuH,
      PHS_operator C₀ (Hamiltonian k ψ) =
        -(Hamiltonian (momentumReversal k) (PHS_operator C₀ ψ)))
    (ψ : NambuH) (z : ℂ)
    (hψ : Hamiltonian k ψ = z • ψ) (hψne : ψ ≠ 0) :
    PHS_operator C₀ ψ ≠ 0 ∧
      Hamiltonian (momentumReversal k) (PHS_operator C₀ ψ) =
        (-star z) • PHS_operator C₀ ψ := by
  have hmap := congrArg (PHS_operator C₀) hψ
  rw [hCovariant ψ, map_smulₛₗ] at hmap
  have htransport :
      Hamiltonian (momentumReversal k) (PHS_operator C₀ ψ) =
        (-star z) • PHS_operator C₀ ψ := by
    have hneg := congrArg Neg.neg hmap
    simpa [neg_smul] using hneg
  refine ⟨?_, htransport⟩
  intro hzero
  have hzero' := congrArg (PHS_operator C₀) hzero
  have hψzero : ψ = 0 := by
    rw [PHS_operator_sq C₀ hC₀ ψ] at hzero'
    simpa using hzero'
  exact hψne hψzero

end InfoGeometry.Experimental.BdGParticleHoleSpectralPairing

end noncomputable section
