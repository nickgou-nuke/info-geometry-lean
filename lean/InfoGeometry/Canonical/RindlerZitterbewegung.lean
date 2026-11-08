import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorChirality
import InfoGeometry.Canonical.CantorDiracPropagation

/-!
# Algebraic Majorana identities in a Rindler-oriented model

This module records two finite algebraic identities for the repository's
Majorana and chirality operators. It does not construct a braid-group action,
derive a time-evolution law, or establish anyonic statistics at a horizon.

We define:
1. **A chirality commutator identity:**
   The velocity operator is the commutator of the Hamiltonian (Dirac operator) and the chirality operator:
   `VelocityOp = DiracOp * ChiralityOp - ChiralityOp * DiracOp`.
   We prove `zitterbewegung_oscillation`, the algebraic consequence of the stated
   anticommutation relation. This identity alone does not establish oscillatory
   dynamics.
2. **A normalized Majorana-product square:**
   The operator `BraidingOp ψ_L ψ_R = c • (1 + ψ_L * ψ_R)` (where `c² = 1/2`)
   squares exactly to `ψ_L * ψ_R` for two anticommuting involutions:
   `BraidingOp * BraidingOp = ψ_L * ψ_R`.
   This is an algebraic identity only; a braid representation and its exchange
   statistics require additional structure not defined here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RindlerZitterbewegung

open InfoGeometry.Canonical.OmegaBoundaryRepresentation
open InfoGeometry.Canonical.CantorChirality
open InfoGeometry.Canonical.CantorDiracPropagation

/-- The Velocity Operator on the Rindler Horizon. -/
def VelocityOp (D Γ : CantorOp) : CantorOp :=
  D * Γ - Γ * D

/-- The commutator of anticommuting `D` and `Γ` equals `2 D Γ`.
    This algebraic identity alone makes no claim about time evolution. -/
theorem zitterbewegung_oscillation :
    VelocityOp DiracOp ChiralityOp = (2 : ℂ) • (DiracOp * ChiralityOp) := by
  dsimp [VelocityOp]
  have h_anticomm := DiracOp_anticommute_ChiralityOp
  have h_comm : ChiralityOp * DiracOp + DiracOp * ChiralityOp = 0 := by
    rw [add_comm]
    exact h_anticomm
  have h_neg : ChiralityOp * DiracOp = - (DiracOp * ChiralityOp) := by
    exact add_eq_zero_iff_eq_neg.mp h_comm
  rw [h_neg]
  simp only [sub_neg_eq_add, two_smul]

/-- The Anyonic Braiding Operator at the Null Space. -/
def BraidingOp (c : ℂ) (ψ_L ψ_R : CantorOp) : CantorOp :=
  c • (1 + ψ_L * ψ_R)

/-- Under the displayed involution and anticommutation hypotheses, the square
    of this normalized Majorana-product operator is `ψ_L * ψ_R`. This identity
    by itself does not assert a topological phase or anyonic statistics. -/
theorem majorana_anyon_exchange (ψ_L ψ_R : CantorOp)
    (hL_sq : ψ_L * ψ_L = 1)
    (hR_sq : ψ_R * ψ_R = 1)
    (h_anticomm : ψ_L * ψ_R + ψ_R * ψ_L = 0)
    (c : ℂ) (hc : c^2 = 1 / 2) :
    (BraidingOp c ψ_L ψ_R) * (BraidingOp c ψ_L ψ_R) = ψ_L * ψ_R := by
  dsimp [BraidingOp]
  have hX : (ψ_L * ψ_R) * (ψ_L * ψ_R) = -1 := by
    have h_comm : ψ_R * ψ_L + ψ_L * ψ_R = 0 := by
      rw [add_comm] at h_anticomm
      exact h_anticomm
    have h_neg : ψ_R * ψ_L = - (ψ_L * ψ_R) := by
      exact add_eq_zero_iff_eq_neg.mp h_comm
    calc
      (ψ_L * ψ_R) * (ψ_L * ψ_R) = ψ_L * (ψ_R * ψ_L) * ψ_R := by simp [mul_assoc]
      _ = ψ_L * (- (ψ_L * ψ_R)) * ψ_R := by rw [h_neg]
      _ = - (ψ_L * (ψ_L * (ψ_R * ψ_R))) := by
        rw [mul_neg ψ_L (ψ_L * ψ_R), neg_mul (ψ_L * (ψ_L * ψ_R)) ψ_R]
        simp [mul_assoc]
      _ = - (ψ_L * ψ_L * (ψ_R * ψ_R)) := by
        rw [mul_assoc ψ_L ψ_L]
      _ = - (1 * 1) := by rw [hL_sq, hR_sq]
      _ = -1 := by simp
  have h_smul : (c • (1 + ψ_L * ψ_R)) * (c • (1 + ψ_L * ψ_R)) = (c * c) • ((1 + ψ_L * ψ_R) * (1 + ψ_L * ψ_R)) := by
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  have h_hc : c * c = 1 / 2 := by
    rw [← pow_two c]
    exact hc
  rw [h_smul, h_hc]
  have h_sq : (1 + ψ_L * ψ_R) * (1 + ψ_L * ψ_R) = (2 : ℂ) • (ψ_L * ψ_R) := by
    calc
      (1 + ψ_L * ψ_R) * (1 + ψ_L * ψ_R) = 1 + (ψ_L * ψ_R) + (ψ_L * ψ_R) + (ψ_L * ψ_R) * (ψ_L * ψ_R) := by
        simp only [add_mul, mul_add, one_mul, mul_one, add_assoc]
      _ = 1 + ((ψ_L * ψ_R) + (ψ_L * ψ_R)) + (ψ_L * ψ_R) * (ψ_L * ψ_R) := by
        rw [add_assoc 1 (ψ_L * ψ_R) (ψ_L * ψ_R)]
      _ = 1 + (2 : ℂ) • (ψ_L * ψ_R) + -1 := by
        have h_two : (ψ_L * ψ_R) + (ψ_L * ψ_R) = (2 : ℂ) • (ψ_L * ψ_R) := by
          simp only [two_smul]
        rw [h_two, hX]
      _ = (2 : ℂ) • (ψ_L * ψ_R) := by
        rw [add_assoc, add_comm ((2 : ℂ) • (ψ_L * ψ_R)) (-1), ← add_assoc, add_neg_cancel, zero_add]
  rw [h_sq]
  rw [smul_smul]
  have h_mul : (1 / 2 : ℂ) * 2 = 1 := by ring
  rw [h_mul, one_smul]

end InfoGeometry.Canonical.RindlerZitterbewegung

end noncomputable section
