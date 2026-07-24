/-
InfoGeometry/OperatorAlgebra/DIIISuperfluid.lean

Class DIII superfluid/BdG symmetry sockets.

This module keeps DIII as a concrete physical symmetry-class branch:

* `K` is the real Hestenes phase axis.
* `Theta` is time reversal, phase-reversing with square `-1`.
* `Xi` is particle-hole/Majorana conjugation, phase-reversing with square `+1`.
* `chi = Theta Xi` is the phase-linear chiral grading.
* `BdG` is the gapped BdG/Dirac generator.

The topological invariant is intentionally model-dependent: `Z`, `Z2`, `Z16`,
or a richer index/winding datum depending on dimension and interaction regime.
-/

import Mathlib
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DIIISuperfluid

universe uH uInv

/-! ## 1. Basic real operator notation -/

/-- Bounded real-linear endomorphisms. -/
abbrev EndR
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  H →L[ℝ] H

/-! ## 2. Algebraic DIII sign derivation -/

/--
Algebraic DIII sign datum.

This is the pure sign skeleton behind the real-linear DIII sockets.  It proves
the formal consequences of the Altland-Zirnbauer DIII signs without choosing a
particular carrier or Hamiltonian representation.
-/
structure DIIISignDatum
    (Op : Type*) [Ring Op] where
  /-- Hestenes/complex phase axis. -/
  K : Op

  /-- Time reversal. -/
  Theta : Op

  /-- Particle-hole/Majorana conjugation. -/
  Xi : Op

  /-- Phase-axis law `K² = -1`. -/
  K_sq :
    K * K = -1

  /-- Time reversal is phase-reversing. -/
  Theta_reverses_phase :
    Theta * K = -(K * Theta)

  /-- Particle-hole symmetry is phase-reversing. -/
  Xi_reverses_phase :
    Xi * K = -(K * Xi)

  /-- DIII Kramers sign: `Theta² = -1`. -/
  Theta_sq :
    Theta * Theta = -1

  /-- Majorana particle-hole sign: `Xi² = 1`. -/
  Xi_sq :
    Xi * Xi = 1

  /-- DIII anticommutation: `Theta Xi = -Xi Theta`. -/
  Theta_Xi_anticomm :
    Theta * Xi = -(Xi * Theta)

namespace DIIISignDatum

variable {Op : Type*} [Ring Op]
variable (D : DIIISignDatum Op)

/-- The DIII chiral grading is the product `Theta Xi`. -/
def chi : Op :=
  D.Theta * D.Xi

/-- Opposite orientation of the DIII anticommutation law: `Xi Theta = -Theta Xi`. -/
theorem Xi_Theta_anticomm :
    D.Xi * D.Theta = -(D.Theta * D.Xi) := by
  rw [D.Theta_Xi_anticomm]
  simp

/-- The DIII product `chi = Theta Xi` squares to one. -/
theorem chi_sq :
    D.chi * D.chi = 1 := by
  calc
    D.chi * D.chi
        = (D.Theta * D.Xi) * (D.Theta * D.Xi) := by
            rfl
    _ = D.Theta * (D.Xi * D.Theta) * D.Xi := by
            noncomm_ring
    _ = D.Theta * (-(D.Theta * D.Xi)) * D.Xi := by
            rw [D.Xi_Theta_anticomm]
    _ = -(D.Theta * (D.Theta * D.Xi)) * D.Xi := by
            rw [mul_neg]
    _ = -((D.Theta * D.Theta) * D.Xi) * D.Xi := by
            rw [mul_assoc]
    _ = -((-1 : Op) * D.Xi) * D.Xi := by
            rw [D.Theta_sq]
    _ = D.Xi * D.Xi := by
            simp
    _ = 1 := by
            rw [D.Xi_sq]

/-- The DIII chiral grading preserves the phase axis: `chi K = K chi`. -/
theorem chi_phase_linear :
    D.chi * D.K = D.K * D.chi := by
  calc
    D.chi * D.K
        = (D.Theta * D.Xi) * D.K := by
            rfl
    _ = D.Theta * (D.Xi * D.K) := by
            rw [mul_assoc]
    _ = D.Theta * (-(D.K * D.Xi)) := by
            rw [D.Xi_reverses_phase]
    _ = -(D.Theta * (D.K * D.Xi)) := by
            rw [mul_neg]
    _ = -((D.Theta * D.K) * D.Xi) := by
            rw [mul_assoc]
    _ = -((-(D.K * D.Theta)) * D.Xi) := by
            rw [D.Theta_reverses_phase]
    _ = (D.K * D.Theta) * D.Xi := by
            simp
    _ = D.K * D.chi := by
            rw [chi, mul_assoc]

/-- Particle-hole/Majorana conjugation flips the DIII chiral grading. -/
theorem Xi_flips_chi :
    D.Xi * D.chi * D.Xi = -D.chi := by
  calc
    D.Xi * D.chi * D.Xi
        = D.Xi * (D.Theta * D.Xi) * D.Xi := by
            rfl
    _ = (D.Xi * D.Theta) * (D.Xi * D.Xi) := by
            noncomm_ring
    _ = (D.Xi * D.Theta) * 1 := by
            rw [D.Xi_sq]
    _ = D.Xi * D.Theta := by
            rw [mul_one]
    _ = -(D.Theta * D.Xi) := by
            rw [D.Xi_Theta_anticomm]
    _ = -D.chi := by
            rfl

/--
Raw multiplication by time reversal on both sides preserves `chi`.

Since `Theta² = -1`, the inverse of `Theta` is `-Theta`; the usual conjugation
statement with `Theta⁻¹` is therefore the chiral-flipping statement.
-/
theorem Theta_mul_chi_mul_Theta :
    D.Theta * D.chi * D.Theta = D.chi := by
  calc
    D.Theta * D.chi * D.Theta
        = D.Theta * (D.Theta * D.Xi) * D.Theta := by
            rfl
    _ = (D.Theta * D.Theta) * (D.Xi * D.Theta) := by
            noncomm_ring
    _ = (-1 : Op) * (D.Xi * D.Theta) := by
            rw [D.Theta_sq]
    _ = -(D.Xi * D.Theta) := by
            rw [neg_one_mul]
    _ = D.Theta * D.Xi := by
            rw [D.Xi_Theta_anticomm]
            simp
    _ = D.chi := by
            rfl

/-- Time-reversal conjugation by `Theta⁻¹ = -Theta` flips the DIII chiral grading. -/
theorem Theta_conj_inv_flips_chi :
    D.Theta * D.chi * (-D.Theta) = -D.chi := by
  calc
    D.Theta * D.chi * (-D.Theta)
        = -(D.Theta * D.chi * D.Theta) := by
            rw [mul_neg]
    _ = -D.chi := by
            rw [D.Theta_mul_chi_mul_Theta]

end DIIISignDatum

/-! ## 3. Real-space DIII symmetry data -/

/--
Class DIII superfluid/BdG symmetry datum on a real doubled carrier.

`Theta` is time reversal with square `-1`.
`Xi` is particle-hole/Majorana conjugation with square `+1`.
`chi` is the chiral grading, usually the normalized product `Theta * Xi`.
-/
structure DIIISuperfluidDatum
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Hestenes phase axis. -/
  K : EndR H

  /-- BdG/Dirac generator. -/
  BdG : EndR H

  /-- Time-reversal mirror. -/
  Theta : EndR H

  /-- Particle-hole/Majorana mirror. -/
  Xi : EndR H

  /-- Chiral grading. -/
  chi : EndR H

  /-- Phase-axis law `K^2 = -1`. -/
  K_sq :
    K.comp K = -(ContinuousLinearMap.id ℝ H)

  /-- Time reversal is phase-reversing. -/
  Theta_reverses_phase :
    Theta.comp K = -(K.comp Theta)

  /-- Particle-hole symmetry is phase-reversing. -/
  Xi_reverses_phase :
    Xi.comp K = -(K.comp Xi)

  /-- DIII Kramers sign: `Theta^2 = -1`. -/
  Theta_sq :
    Theta.comp Theta = -(ContinuousLinearMap.id ℝ H)

  /-- Majorana particle-hole sign: `Xi^2 = 1`. -/
  Xi_sq :
    Xi.comp Xi = ContinuousLinearMap.id ℝ H

  /-- The two mirrors anticommute. -/
  Theta_Xi_anticomm :
    Theta.comp Xi = -(Xi.comp Theta)

  /-- The chiral grading is the product `Theta Xi`. -/
  chi_eq :
    chi = Theta.comp Xi

  /-- Chiral grading squares to one. -/
  chi_sq :
    chi.comp chi = ContinuousLinearMap.id ℝ H

  /-- The product of two phase-reversing symmetries is phase-linear. -/
  chi_phase_linear :
    chi.comp K = K.comp chi

  /-- Particle-hole symmetry: the BdG generator is odd under `Xi`. -/
  Xi_BdG :
    Xi.comp BdG = -(BdG.comp Xi)

  /-- Time-reversal symmetry in the real-space/no-momentum-reversal socket. -/
  Theta_BdG :
    Theta.comp BdG = BdG.comp Theta

  /-- Chiral symmetry: the BdG generator is odd under `chi`. -/
  chi_BdG :
    chi.comp BdG = -(BdG.comp chi)

  /-- Topological invariant socket: `Z`, `Z2`, or `Z16` depending on the model. -/
  topologicalInvariant : Type*

  /-- Chosen invariant readout for this model. -/
  invariant_readout :
    topologicalInvariant

namespace DIIISuperfluidDatum

variable
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : DIIISuperfluidDatum H)

/-- The underlying algebraic DIII sign datum of a real-space DIII model. -/
def signDatum : DIIISignDatum (EndR H) where
  K := D.K
  Theta := D.Theta
  Xi := D.Xi
  K_sq := D.K_sq
  Theta_reverses_phase := D.Theta_reverses_phase
  Xi_reverses_phase := D.Xi_reverses_phase
  Theta_sq := D.Theta_sq
  Xi_sq := D.Xi_sq
  Theta_Xi_anticomm := D.Theta_Xi_anticomm

/-- The DIII chiral grading is phase-linear. -/
theorem chi_commutes_phase :
    D.chi.comp D.K = D.K.comp D.chi :=
  D.chi_phase_linear

/-- The DIII chiral grading square is derived from the DIII sign skeleton. -/
theorem chi_sq_derived :
    D.chi.comp D.chi = ContinuousLinearMap.id ℝ H := by
  simpa [signDatum, DIIISignDatum.chi, D.chi_eq] using
    (D.signDatum.chi_sq)

/-- Phase-linearity of `chi` is derived from the two phase-reversing mirrors. -/
theorem chi_phase_linear_derived :
    D.chi.comp D.K = D.K.comp D.chi := by
  simpa [signDatum, DIIISignDatum.chi, D.chi_eq] using
    (D.signDatum.chi_phase_linear)

/-- The Majorana particle-hole mirror flips the DIII chiral grading. -/
theorem Xi_flips_chi :
    (D.Xi.comp D.chi).comp D.Xi = -D.chi := by
  simpa [signDatum, DIIISignDatum.chi, D.chi_eq] using
    (D.signDatum.Xi_flips_chi)

/-- The DIII BdG generator is chiral-odd. -/
theorem chiral_odd_BdG :
    D.chi.comp D.BdG = -(D.BdG.comp D.chi) :=
  D.chi_BdG

end DIIISuperfluidDatum

/-! ## 3. Momentum-space DIII symmetry data -/

/--
Momentum-space class DIII superfluid/BdG symmetry datum.

The map `invK` is the momentum inversion/reversal operation.
-/
structure MomentumDIIISuperfluidDatum
    (Kpt H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  /-- Momentum reversal, usually `k ↦ -k`. -/
  invK : Kpt → Kpt

  /-- Momentum reversal is involutive. -/
  invK_involutive :
    ∀ k : Kpt, invK (invK k) = k

  /-- Momentum-family BdG/Dirac generator. -/
  BdG : Kpt → EndR H

  /-- Time-reversal mirror. -/
  Theta : EndR H

  /-- Particle-hole/Majorana mirror. -/
  Xi : EndR H

  /-- Chiral grading. -/
  chi : EndR H

  /-- DIII Kramers sign: `Theta^2 = -1`. -/
  Theta_sq :
    Theta.comp Theta = -(ContinuousLinearMap.id ℝ H)

  /-- Majorana particle-hole sign: `Xi^2 = 1`. -/
  Xi_sq :
    Xi.comp Xi = ContinuousLinearMap.id ℝ H

  /-- Chiral grading squares to one. -/
  chi_sq :
    chi.comp chi = ContinuousLinearMap.id ℝ H

  /-- Time-reversal covariance across momentum reversal. -/
  time_reversal :
    ∀ k : Kpt, Theta.comp (BdG k) = (BdG (invK k)).comp Theta

  /-- Particle-hole covariance across momentum reversal. -/
  particle_hole :
    ∀ k : Kpt, Xi.comp (BdG k) = -((BdG (invK k)).comp Xi)

  /-- Chiral oddness at fixed momentum. -/
  chiral :
    ∀ k : Kpt, chi.comp (BdG k) = -((BdG k).comp chi)

  /-- Topological invariant socket for this momentum-space model. -/
  topologicalInvariant : Type*

  /-- Chosen invariant readout for this model. -/
  invariant_readout :
    topologicalInvariant

namespace MomentumDIIISuperfluidDatum

variable
    {Kpt H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : MomentumDIIISuperfluidDatum Kpt H)

/-- Momentum reversal is an involution. -/
theorem invK_invK
    (k : Kpt) :
    D.invK (D.invK k) = k :=
  D.invK_involutive k

/-- Re-export the chiral oddness law. -/
theorem chiral_odd
    (k : Kpt) :
    D.chi.comp (D.BdG k) = -((D.BdG k).comp D.chi) :=
  D.chiral k

end MomentumDIIISuperfluidDatum

/-! ## 4. Owner theorem -/

/--
Read out the DIII symmetry laws from a supplied model datum.

The theorem is still model-gated: the concrete BdG carrier, symmetry
operators, and topological invariant must be supplied by a model.  What it
proves is not mere inhabitation; it exposes the kernel-checked sign,
phase-reversal, chiral, and BdG covariance laws carried by that datum.
-/
theorem dIIISuperfluidOwnerTarget :
  ∀ (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H],
    ∀ D : DIIISuperfluidDatum.{uH, uInv} H,
      D.K.comp D.K = -(ContinuousLinearMap.id ℝ H) ∧
      D.Theta.comp D.K = -(D.K.comp D.Theta) ∧
      D.Xi.comp D.K = -(D.K.comp D.Xi) ∧
      D.Theta.comp D.Theta = -(ContinuousLinearMap.id ℝ H) ∧
      D.Xi.comp D.Xi = ContinuousLinearMap.id ℝ H ∧
      D.Theta.comp D.Xi = -(D.Xi.comp D.Theta) ∧
      D.chi = D.Theta.comp D.Xi ∧
      D.chi.comp D.chi = ContinuousLinearMap.id ℝ H ∧
      D.chi.comp D.K = D.K.comp D.chi ∧
      D.Xi.comp D.BdG = -(D.BdG.comp D.Xi) ∧
      D.Theta.comp D.BdG = D.BdG.comp D.Theta ∧
      D.chi.comp D.BdG = -(D.BdG.comp D.chi) := by
  intro H _ _ D
  exact ⟨D.K_sq, D.Theta_reverses_phase, D.Xi_reverses_phase,
    D.Theta_sq, D.Xi_sq, D.Theta_Xi_anticomm, D.chi_eq, D.chi_sq,
    D.chi_phase_linear, D.Xi_BdG, D.Theta_BdG, D.chi_BdG⟩

/-- A supplied DIII datum exposes the chiral and BdG laws used downstream. -/
theorem dIIISuperfluidDatum_packet
    {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (D : DIIISuperfluidDatum.{uH, uInv} H) :
    D.chi.comp D.chi = ContinuousLinearMap.id ℝ H ∧
      D.chi.comp D.K = D.K.comp D.chi ∧
      D.chi.comp D.BdG = -(D.BdG.comp D.chi) := by
  exact ⟨D.chi_sq, D.chi_phase_linear, D.chi_BdG⟩

end InfoGeometry.OperatorAlgebra.DIIISuperfluid
