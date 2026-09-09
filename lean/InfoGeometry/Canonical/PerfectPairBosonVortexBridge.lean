import InfoGeometry.Canonical.FinitePerfectMatching
import InfoGeometry.Canonical.CausalVortexCooperPairing
import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Projective.KleinQuadricMonodromy
import Mathlib.Tactic

/-! # Perfect-pair occupation and vortex bridge

This is the theorem-safe mathematical translation of pair/condensate language:
perfect matchings give composite modes, occupations give a finite symmetric
carrier, and a charge-two phase has integer winding.  No CCR, spectral gap, or
dynamical condensation claim is made.
-/

noncomputable section

namespace InfoGeometry.Canonical.PerfectPairBosonVortexBridge

open InfoGeometry.Canonical.FinitePerfectMatching
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

variable {m : ℕ}

abbrev PairMode (M : PerfectMatching m) :=
  {i : Fin (2 * m) // i ∈ M.leftEndpoints}

abbrev PairOccupation (M : PerfectMatching m) := PairMode M → ℕ

theorem pairMode_card (M : PerfectMatching m) : Fintype.card (PairMode M) = m := by
  calc
    Fintype.card (PairMode M) = M.leftEndpoints.card := by
      simpa [PairMode] using (Fintype.card_coe M.leftEndpoints)
    _ = m := M.leftEndpoints_card

def vacuumOccupation (M : PerfectMatching m) : PairOccupation M := fun _ => 0

def purePairCondensate (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) :
    PairOccupation M := fun j => if j = mode then N else 0

@[simp] theorem purePairCondensate_at_mode
    (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) :
    purePairCondensate M mode N mode = N := by simp [purePairCondensate]

@[simp] theorem purePairCondensate_off_mode
    (M : PerfectMatching m) (mode j : PairMode M) (N : ℕ) (h : j ≠ mode) :
    purePairCondensate M mode N j = 0 := by simp [purePairCondensate, h]

def totalPairOccupation (M : PerfectMatching m) (n : PairOccupation M) : ℕ := ∑ j, n j

@[simp] theorem totalPairOccupation_vacuum (M : PerfectMatching m) :
    totalPairOccupation M (vacuumOccupation M) = 0 := by
  simp [totalPairOccupation, vacuumOccupation]

@[simp] theorem totalPairOccupation_pure
    (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) :
    totalPairOccupation M (purePairCondensate M mode N) = N := by
  classical
  simp [totalPairOccupation, purePairCondensate]

def constituentPhase (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

def pairPhase (θ : ℝ) : ℂ := Complex.exp (Complex.I * ((2 * θ : ℝ) : ℂ))

theorem pairPhase_eq_constituentPhase_sq (θ : ℝ) :
    pairPhase θ = constituentPhase θ ^ 2 := by
  rw [pairPhase, constituentPhase, pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem norm_constituentPhase (θ : ℝ) : ‖constituentPhase θ‖ = 1 := by
  simpa [constituentPhase, mul_comm] using Complex.norm_exp_ofReal_mul_I θ

@[simp] theorem norm_pairPhase (θ : ℝ) : ‖pairPhase θ‖ = 1 := by
  rw [pairPhase_eq_constituentPhase_sq, norm_pow, norm_constituentPhase, one_pow]

theorem cooperPairPhaseRotation_constituentGauge
    {n : ℕ} (M : CausalVortex.NullBoundaryMajoranas n) (θ : ℝ) :
    CausalVortex.cooperPairPhaseRotation M (2 * θ) =
      pairPhase θ • CausalVortex.cooperPairCondensate M := by rfl

theorem cooperPairPhaseRotation_eq_constituentPhase_sq
    {n : ℕ} (M : CausalVortex.NullBoundaryMajoranas n) (θ : ℝ) :
    CausalVortex.cooperPairPhaseRotation M (2 * θ) =
      constituentPhase θ ^ 2 • CausalVortex.cooperPairCondensate M := by
  rw [cooperPairPhaseRotation_constituentGauge M θ, pairPhase_eq_constituentPhase_sq]

def pairVortexAngle (n : ℤ) : ℝ := Real.pi * n

theorem pairPhase_vortex_winding (n : ℤ) : pairPhase (pairVortexAngle n) = 1 := by
  rw [pairPhase, pairVortexAngle]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1 <;>
    push_cast <;> ring_nf

theorem cooperPairPhaseRotation_vortex
    {n : ℕ} (M : CausalVortex.NullBoundaryMajoranas n) (k : ℤ) :
    CausalVortex.cooperPairPhaseRotation M (2 * pairVortexAngle k) =
      CausalVortex.cooperPairCondensate M := by
  rw [cooperPairPhaseRotation_constituentGauge, pairPhase_vortex_winding]
  simp

theorem pairVortex_eq_deRhamHolonomy
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    pairPhase (pairVortexAngle n) =
      Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)) := by
  rw [pairPhase_vortex_winding]
  symm
  exact wilsonPhase_of_winding R hR n

theorem bipolar_pairing_residue_balance :
    residuePair = ((1 : ℂ), (-1 : ℂ)) ∧ residuePair.1 + residuePair.2 = 0 := by
  exact ⟨rfl, residuePair_sum_zero⟩

theorem perfect_pair_boson_vortex_packet
    (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) (n : ℤ) :
    Fintype.card (PairMode M) = m ∧
      totalPairOccupation M (purePairCondensate M mode N) = N ∧
      pairPhase (pairVortexAngle n) = constituentPhase (pairVortexAngle n) ^ 2 ∧
      pairPhase (pairVortexAngle n) = 1 ∧ residuePair.1 + residuePair.2 = 0 := by
  exact ⟨pairMode_card M, totalPairOccupation_pure M mode N,
    pairPhase_eq_constituentPhase_sq _, pairPhase_vortex_winding n,
    residuePair_sum_zero⟩

end InfoGeometry.Canonical.PerfectPairBosonVortexBridge
