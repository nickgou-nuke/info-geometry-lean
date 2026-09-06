import InfoGeometry.Canonical.FinitePerfectMatching
import InfoGeometry.Canonical.CausalVortexCooperPairing
import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Projective.KleinQuadricMonodromy
import Mathlib.Analysis.SpecialFunctions.Complex.Exponential
import Mathlib.Tactic

/-!
# Perfect-pair bosonic occupation and vortex bridge

This file gives a theorem-safe mathematical interpretation of the informal
"superconducting" language attached to the bipolar source/sink construction.

The formal hierarchy is:

1. a perfect matching partitions `2m` elementary labels into `m` pair modes;
2. a bosonic state of these composites is represented by occupation numbers on
   the pair modes, so ordering of identical composites is absent by construction;
3. a pure condensate is the occupation vector with all `N` composites in one
   pair mode;
4. a composite made from two equally charged constituents carries the square of
   the constituent `U(1)` phase;
5. the existing finite Cooper-pair operator therefore sees twice the constituent
   gauge angle;
6. integer vortex winding gives trivial closed-loop composite phase;
7. the bipolar logarithmic differential supplies the balanced two-pole
   `( +1, -1 )` residue datum.

This does **not** claim that arbitrary fermion bilinears satisfy canonical CCR,
that a microscopic BCS Hamiltonian has a gap, or that Bose condensation occurs
dynamically. Those require additional operator, spectral, and thermodynamic
hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.PerfectPairBosonVortexBridge

open InfoGeometry.Canonical.FinitePerfectMatching
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy

variable {m : ℕ}

/-- One composite mode for each unordered matched pair. The smaller endpoint
is used as the canonical representative, so every pair occurs exactly once. -/
abbrev PairMode (M : PerfectMatching m) :=
  {i : Fin (2 * m) // i ∈ M.leftEndpoints}

/-- A bosonic occupation-number configuration of the matched composite modes. -/
abbrev PairOccupation (M : PerfectMatching m) := PairMode M → ℕ

/-- The number of distinct composite pair modes is exactly `m`. -/
theorem pairMode_card (M : PerfectMatching m) : Fintype.card (PairMode M) = m := by
  calc
    Fintype.card (PairMode M) = M.leftEndpoints.card := by
      simpa [PairMode] using (Fintype.card_coe M.leftEndpoints)
    _ = m := M.leftEndpoints_card

/-- Vacuum occupation of the composite modes. -/
def vacuumOccupation (M : PerfectMatching m) : PairOccupation M := fun _ => 0

/-- Put exactly `N` matched composites into one selected mode. This is the
finite occupation-number analogue of a pure one-mode condensate. -/
def purePairCondensate (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) :
    PairOccupation M :=
  fun j => if j = mode then N else 0

@[simp] theorem purePairCondensate_at_mode
    (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) :
    purePairCondensate M mode N mode = N := by
  simp [purePairCondensate]

@[simp] theorem purePairCondensate_off_mode
    (M : PerfectMatching m) (mode j : PairMode M) (N : ℕ) (h : j ≠ mode) :
    purePairCondensate M mode N j = 0 := by
  simp [purePairCondensate, h]

/-- Total number of composite pairs in an occupation configuration. -/
def totalPairOccupation (M : PerfectMatching m) (n : PairOccupation M) : ℕ :=
  ∑ j, n j

@[simp] theorem totalPairOccupation_vacuum (M : PerfectMatching m) :
    totalPairOccupation M (vacuumOccupation M) = 0 := by
  simp [totalPairOccupation, vacuumOccupation]

@[simp] theorem totalPairOccupation_pure
    (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) :
    totalPairOccupation M (purePairCondensate M mode N) = N := by
  classical
  simp [totalPairOccupation, purePairCondensate]

/-- Elementary `U(1)` phase. -/
def constituentPhase (θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (θ : ℂ))

/-- A two-constituent composite transforms with twice the phase angle. -/
def pairPhase (θ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((2 * θ : ℝ) : ℂ))

/-- The composite phase is exactly the square of the constituent phase. -/
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

/-- Adapter to the existing finite Cooper-pair owner: if `θ` is the constituent
gauge angle, the composite order parameter is rotated by `2θ`. -/
theorem cooperPairPhaseRotation_constituentGauge
    {n : ℕ} (M : CausalVortex.NullBoundaryMajoranas n) (θ : ℝ) :
    CausalVortex.cooperPairPhaseRotation M (2 * θ) =
      pairPhase θ • CausalVortex.cooperPairCondensate M := by
  rfl

/-- Equivalently, the existing Cooper-pair rotation carries the square of the
constituent phase. -/
theorem cooperPairPhaseRotation_eq_constituentPhase_sq
    {n : ℕ} (M : CausalVortex.NullBoundaryMajoranas n) (θ : ℝ) :
    CausalVortex.cooperPairPhaseRotation M (2 * θ) =
      constituentPhase θ ^ 2 • CausalVortex.cooperPairCondensate M := by
  rw [cooperPairPhaseRotation_constituentGauge M θ,
    pairPhase_eq_constituentPhase_sq]

/-- Dimensionless integer vortex angle for a charge-two composite. A half-turn
`π n` of the constituent phase becomes a full `2π n` turn of the pair phase. -/
def pairVortexAngle (n : ℤ) : ℝ := Real.pi * n

/-- Integer pair-vortex winding closes with trivial `U(1)` holonomy. -/
theorem pairPhase_vortex_winding (n : ℤ) :
    pairPhase (pairVortexAngle n) = 1 := by
  rw [pairPhase, pairVortexAngle]
  have harg :
      Complex.I * (((2 : ℝ) * (Real.pi * (n : ℝ))) : ℂ) =
        (n : ℂ) * (2 * Real.pi * Complex.I : ℂ) := by
    push_cast
    ring
  rw [harg]
  simpa using Complex.exp_int_mul_two_pi_mul_I n

/-- The existing Cooper-pair operator is single-valued after an integer pair
vortex winding in the constituent gauge angle. -/
theorem cooperPairPhaseRotation_vortex
    {n : ℕ} (M : CausalVortex.NullBoundaryMajoranas n) (k : ℤ) :
    CausalVortex.cooperPairPhaseRotation M (2 * pairVortexAngle k) =
      CausalVortex.cooperPairCondensate M := by
  rw [cooperPairPhaseRotation_constituentGauge, pairPhase_vortex_winding]
  simp

/-- The same integer winding is the exponential of the repository's canonical
`2πi` logarithmic period. -/
theorem pairVortex_eq_deRhamHolonomy
    (R : ℝ) (hR : 0 < R) (n : ℤ) :
    pairPhase (pairVortexAngle n) =
      Complex.exp ((n : ℂ) * (∮ z in C((0 : ℂ), R), poleForm z)) := by
  rw [pairPhase_vortex_winding]
  symm
  exact wilsonPhase_of_winding R hR n

/-- The bipolar logarithmic differential carries the balanced pair of residues
that underlies the source/sink vocabulary. -/
theorem bipolar_pairing_residue_balance :
    residuePair = ((1 : ℂ), (-1 : ℂ)) ∧
      residuePair.1 + residuePair.2 = 0 := by
  exact ⟨rfl, residuePair_sum_zero⟩

/-- Compact theorem packet: perfect pairing gives exactly `m` composite modes,
a pure occupation state contains exactly `N` composites, the pair phase is the
square of the constituent phase, integer vortex winding is closed, and the
underlying logarithmic two-pole residues balance. -/
theorem perfect_pair_boson_vortex_packet
    (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) (n : ℤ) :
    Fintype.card (PairMode M) = m ∧
      totalPairOccupation M (purePairCondensate M mode N) = N ∧
      pairPhase (pairVortexAngle n) = constituentPhase (pairVortexAngle n) ^ 2 ∧
      pairPhase (pairVortexAngle n) = 1 ∧
      residuePair.1 + residuePair.2 = 0 := by
  exact ⟨pairMode_card M,
    totalPairOccupation_pure M mode N,
    pairPhase_eq_constituentPhase_sq _,
    pairPhase_vortex_winding n,
    residuePair_sum_zero⟩

end InfoGeometry.Canonical.PerfectPairBosonVortexBridge
