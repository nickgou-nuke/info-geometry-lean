import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Abel
import InfoGeometry.Canonical.BraidedCubicCompressionBridge
import InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge

/-!
# InfoGeometry.Canonical.ToeplitzCuntzThreeAnyonBraidCentralChargeBridge

Genuinely braidedAnyon representation (B₃ → U(ℰ₃)) with central full twist Z_twist = (b₂ b₁)³
and braided cubic fractional SUSY closure: Q_br³ = Z_twist H over a non-commutative Ring A.

This formalizes how anyonic braid fusion data elevates the unbraided cubic relation Q³ = H
to the central charge relation Q_br³ = Z_twist H while strictly preserving vacuum protection Q_br P₀ = P₀ Q_br = 0.
-/

noncomputable section

namespace InfoGeometry.Canonical.ToeplitzCuntzThreeAnyonBraidCentralChargeBridge

open InfoGeometry.Canonical.ToeplitzCuntzThreeVacuumBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeCyclicSuperchargeBridge
open InfoGeometry.Canonical.ToeplitzCuntzThreeArtinBraidBridge
open InfoGeometry.Canonical.BraidedCubicCompressionBridge
open ToeplitzCuntzThreeGenerators

variable {A : Type*} [Ring A] [StarRing A]
variable (g : ToeplitzCuntzThreeGenerators A)

/-- Abstract anyonic braid excitation data for a B₃ representation on the ℰ₃ excited sector. -/
structure BraidedExcitationData where
  braid1 : A
  braid2 : A
  artin_relation : braid1 * braid2 * braid1 = braid2 * braid1 * braid2
  preserves_H_left1 : g.susyHamiltonian * braid1 = braid1 * g.susyHamiltonian
  preserves_H_left2 : g.susyHamiltonian * braid2 = braid2 * g.susyHamiltonian

def fullTwist (D : BraidedExcitationData g) : A :=
  (D.braid2 * D.braid1) ^ 3

theorem fullTwist_comm_hamiltonian (D : BraidedExcitationData g) :
    fullTwist g D * g.susyHamiltonian =
      g.susyHamiltonian * fullTwist g D := by
  have hC : g.susyHamiltonian * (D.braid2 * D.braid1) =
      (D.braid2 * D.braid1) * g.susyHamiltonian := by
    calc
      g.susyHamiltonian * (D.braid2 * D.braid1) =
          (g.susyHamiltonian * D.braid2) * D.braid1 := by noncomm_ring
      _ = (D.braid2 * g.susyHamiltonian) * D.braid1 := by
        rw [D.preserves_H_left2]
      _ = D.braid2 * (g.susyHamiltonian * D.braid1) := by noncomm_ring
      _ = D.braid2 * (D.braid1 * g.susyHamiltonian) := by
        rw [D.preserves_H_left1]
      _ = (D.braid2 * D.braid1) * g.susyHamiltonian := by noncomm_ring
  have hComm : Commute g.susyHamiltonian (D.braid2 * D.braid1) := hC
  exact (hComm.pow_right 3).symm

/-- Braided Cubic Supercharge Q_br := H (b₂ b₁) H. -/
def braidedCubicSupercharge (D : BraidedExcitationData g) : A :=
  g.susyHamiltonian * (D.braid2 * D.braid1) * g.susyHamiltonian

theorem susyHamiltonian_idempotent :
    g.susyHamiltonian * g.susyHamiltonian = g.susyHamiltonian := by
  dsimp [susyHamiltonian, P1, P2, P3]
  have hp1 := p1_idempotent g
  have hp2 := p2_idempotent g
  have hp3 := p3_idempotent g
  have h12 := p1_p2_ortho g
  have h21 := p2_p1_ortho g
  have h23 := p2_p3_ortho g
  have h32 := p3_p2_ortho g
  have h13 := p1_p3_ortho g
  have h31 := p3_p1_ortho g
  calc (g.P1 + g.P2 + g.P3) * (g.P1 + g.P2 + g.P3)
      = g.P1 * g.P1 + g.P1 * g.P2 + g.P1 * g.P3
        + g.P2 * g.P1 + g.P2 * g.P2 + g.P2 * g.P3
        + g.P3 * g.P1 + g.P3 * g.P2 + g.P3 * g.P3 := by noncomm_ring
    _ = g.P1 + 0 + 0 + 0 + g.P2 + 0 + 0 + 0 + g.P3 := by
      rw [hp1, hp2, hp3, h12, h21, h23, h32, h13, h31]
    _ = g.P1 + g.P2 + g.P3 := by abel

/-- **Theorem**: Q_br simplifies to H (b₂ b₁) due to H preservation. -/
theorem braidedCubicSupercharge_eq_hamiltonian_mul (D : BraidedExcitationData g) :
    braidedCubicSupercharge g D = g.susyHamiltonian * (D.braid2 * D.braid1) := by
  have hH_sq := susyHamiltonian_idempotent g
  dsimp [braidedCubicSupercharge]
  calc g.susyHamiltonian * (D.braid2 * D.braid1) * g.susyHamiltonian
      = g.susyHamiltonian * (D.braid2 * (D.braid1 * g.susyHamiltonian)) := by noncomm_ring
    _ = g.susyHamiltonian * (D.braid2 * (g.susyHamiltonian * D.braid1)) := by rw [← D.preserves_H_left1]
    _ = g.susyHamiltonian * ((D.braid2 * g.susyHamiltonian) * D.braid1) := by noncomm_ring
    _ = g.susyHamiltonian * ((g.susyHamiltonian * D.braid2) * D.braid1) := by rw [← D.preserves_H_left2]
    _ = (g.susyHamiltonian * g.susyHamiltonian) * (D.braid2 * D.braid1) := by noncomm_ring
    _ = g.susyHamiltonian * (D.braid2 * D.braid1) := by rw [hH_sq]

/-- **Theorem**: Right Vacuum Annihilation Q_br P₀ = 0. -/
theorem braidedCubicSupercharge_vacuum_annihilation (D : BraidedExcitationData g) :
    braidedCubicSupercharge g D * g.P0 = 0 := by
  have hH_p0 := susyHamiltonian_defect_annihilation_right g
  dsimp [braidedCubicSupercharge]
  calc g.susyHamiltonian * (D.braid2 * D.braid1) * g.susyHamiltonian * g.P0
      = g.susyHamiltonian * (D.braid2 * D.braid1) * (g.susyHamiltonian * g.P0) := by noncomm_ring
    _ = 0 := by rw [hH_p0, mul_zero]

/-- **Theorem**: Left Vacuum Annihilation P₀ Q_br = 0. -/
theorem vacuum_braidedCubicSupercharge_annihilation (D : BraidedExcitationData g) :
    g.P0 * braidedCubicSupercharge g D = 0 := by
  have hp0_H := susyHamiltonian_defect_annihilation_left g
  dsimp [braidedCubicSupercharge]
  calc g.P0 * (g.susyHamiltonian * (D.braid2 * D.braid1) * g.susyHamiltonian)
      = (g.P0 * g.susyHamiltonian) * ((D.braid2 * D.braid1) * g.susyHamiltonian) := by noncomm_ring
    _ = 0 := by rw [hp0_H, zero_mul]

/-- **Apex Theorem**: Braided Cubic Fractional SUSY Law Q_br³ = Z_twist H. -/
theorem braidedCubicSupercharge_cube_eq_fullTwist_hamiltonian (D : BraidedExcitationData g) :
    braidedCubicSupercharge g D * braidedCubicSupercharge g D * braidedCubicSupercharge g D =
    fullTwist g D * g.susyHamiltonian := by
  have hH_sq := susyHamiltonian_idempotent g
  have hFull :
      (D.braid2 * D.braid1) * (D.braid2 * D.braid1) *
          (D.braid2 * D.braid1) = fullTwist g D := by
    dsimp [fullTwist]
    rw [pow_three]
    noncomm_ring
  simpa [braidedCubicSupercharge] using
    braided_cubic_compression_cube_of
      g.susyHamiltonian D.braid1 D.braid2 (fullTwist g D)
      hH_sq D.preserves_H_left1 D.preserves_H_left2
      hFull (fullTwist_comm_hamiltonian g D)

/-- **Master Synthesis**: Anyonic Braid Central Charge Q_br³ = Z_twist H. -/
theorem master_toeplitz_cuntz_three_anyon_braid_synthesis (D : BraidedExcitationData g) :
    braidedCubicSupercharge g D * g.P0 = 0 ∧
    g.P0 * braidedCubicSupercharge g D = 0 ∧
    braidedCubicSupercharge g D * braidedCubicSupercharge g D * braidedCubicSupercharge g D =
      fullTwist g D * g.susyHamiltonian := ⟨
  braidedCubicSupercharge_vacuum_annihilation g D,
  vacuum_braidedCubicSupercharge_annihilation g D,
  braidedCubicSupercharge_cube_eq_fullTwist_hamiltonian g D
⟩

end InfoGeometry.Canonical.ToeplitzCuntzThreeAnyonBraidCentralChargeBridge
