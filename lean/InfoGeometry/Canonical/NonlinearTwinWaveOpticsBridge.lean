import Mathlib.Tactic

import InfoGeometry.Canonical.ManakovZornSolitonLaxBridge
import InfoGeometry.Canonical.KreinParaKahlerTwinWaveBridge
import InfoGeometry.Physics.ChiralZitterbewegungBridge
import InfoGeometry.External.Auto.VacuumJonesKleinBirefringence
import InfoGeometry.Attention.PhaseConjugateLaserCavity
import InfoGeometry.Physics.CPTGlobalPinKleinDescent
import InfoGeometry.Canonical.Cl11BipartitePolynomialSpectralAction

/-!
# Nonlinear twin-wave optics synthesis bridge

This module collects theorem-safe finite identities already present in the
repository and adds only the missing interoperability layer.

Closed here:
* symmetric two-sheet nonlinear density energy;
* exact XPM term g_cross n_plus n_minus and sheet-swap invariance;
* forward/backward frequency difference omega - (-omega) = 2 omega;
* connection to the existing two-level Zitterbewegung 2*Delta gap identity;
* existing Jones birefringence readout;
* existing phase-conjugate aberration cancellation;
* existing Klein/CPT two-cycle readouts;
* an explicit hypothesis-bearing comparison between the polynomial spectral
  mixed trace term and an XPM energy.

No theorem identifies Schwinger--Keldysh doubling with Clifford doubling,
identifies the spectral mixed trace term with physical XPM without a supplied
comparison hypothesis, derives refractive indices from Nieh--Yan torsion, or
identifies a Kerr crosscap with a physical phase-conjugate mirror.
-/

noncomputable section

namespace InfoGeometry.Canonical.NonlinearTwinWaveOpticsBridge

open InfoGeometry.Canonical.ManakovZornSolitonLax
open InfoGeometry.Canonical.KreinParaKahlerTwinWaveBridge
open InfoGeometry.Physics.Zitterbewegung
open VacuumJonesKleinBirefringence
open InfoGeometry.PhaseConjugateLaserCavity
open InfoGeometry.Physics.CPTGlobalPinKleinDescent
open InfoGeometry.Canonical.Cl11BipartitePolynomialSpectralAction

/-! ## 1. Two-sheet nonlinear density energy -/

/-- Finite two-sheet density datum. -/
structure TwinDensity where
  nPlus : ℝ
  nMinus : ℝ

/-- Exchange of the two density sheets. -/
def sheetSwap (s : TwinDensity) : TwinDensity where
  nPlus := s.nMinus
  nMinus := s.nPlus

@[simp] theorem sheetSwap_involutive (s : TwinDensity) :
    sheetSwap (sheetSwap s) = s := by
  cases s
  rfl

/-- Cross-phase interaction term. -/
def crossPhaseEnergy (gCross : ℝ) (s : TwinDensity) : ℝ :=
  gCross * s.nPlus * s.nMinus

/-- Symmetric self/cross nonlinear density energy. -/
def coupledDensityEnergy
    (gSelf gCross : ℝ) (s : TwinDensity) : ℝ :=
  (gSelf / 2) * (s.nPlus ^ 2 + s.nMinus ^ 2) +
    crossPhaseEnergy gCross s

/-- XPM is invariant under exchanging the two sheets. -/
theorem crossPhaseEnergy_sheetSwap
    (gCross : ℝ) (s : TwinDensity) :
    crossPhaseEnergy gCross (sheetSwap s) =
      crossPhaseEnergy gCross s := by
  cases s
  simp [crossPhaseEnergy, sheetSwap]
  ring

/-- The symmetric nonlinear energy is invariant under sheet exchange. -/
theorem coupledDensityEnergy_sheetSwap
    (gSelf gCross : ℝ) (s : TwinDensity) :
    coupledDensityEnergy gSelf gCross (sheetSwap s) =
      coupledDensityEnergy gSelf gCross s := by
  cases s
  simp [coupledDensityEnergy, crossPhaseEnergy, sheetSwap]
  ring

/-- When self and cross couplings are both two, the density polynomial is
exactly the repository's Manakov Kerr square up to the displayed normalization. -/
theorem coupledDensityEnergy_eq_manakov
    (s : TwinDensity) :
    coupledDensityEnergy 2 2 s =
      manakovKerrEnergy s.nPlus s.nMinus := by
  unfold coupledDensityEnergy crossPhaseEnergy manakovKerrEnergy
  ring

/-! ## 2. Forward/backward frequency difference -/

/-- A forward frequency +omega and a backward frequency -omega differ by
exactly 2 omega. -/
theorem forward_backward_frequency_difference (omega : ℝ) :
    omega - (-omega) = 2 * omega := by
  ring

/-- The same factor two is the algebraic gap of the existing two-level
chiral/Zitterbewegung Hamiltonian when Delta = omega. -/
theorem frequency_difference_eq_zitter_gap
    (E0 omega : ℝ) :
    omega - (-omega) =
      (E0 + omega) - (E0 - omega) := by
  have hgap := universal_zitterbewegung_mass_gap E0 omega
  dsimp at hgap
  rw [forward_backward_frequency_difference, hgap]

/-! ## 3. Existing optical readouts -/

/-- Existing Jones-tensor birefringence readout. -/
theorem jones_birefringence_readout
    (eps11 eps22 gamma : ℝ) :
    ((vacuumJonesTensor eps11 eps22 gamma 0 0) -
      (vacuumJonesTensor eps11 eps22 gamma 1 1)) =
      (birefringenceDelta eps11 eps22 : ℂ) :=
  vacuumJonesTensor_birefringence eps11 eps22 gamma

/-- Existing exact finite phase-conjugation cancellation theorem. -/
theorem phaseConjugate_aberration_cancellation
    (c s : ℝ) (hunit : c ^ 2 + s ^ 2 = 1) :
    matMul2 pcmMat
      (matMul2 (rotMat c s)
        (matMul2 pcmMat (rotMat c s))) =
      matId2 :=
  pcm_aberration_cancellation c s hunit

/-- Existing matrix-level Klein two-cycle holonomy. -/
theorem klein_two_cycle_readout :
    InfoGeometry.Topology.BraidMatrix *
        InfoGeometry.Topology.TwistedBraidMatrix = 1 :=
  classical_klein_two_cycle_holonomy

/-- Existing Pin-kernel two-cycle readout. -/
theorem pin_two_cycle_readout :
    InfoGeometry.Clifford.Clifford55.pinTwistedOrthogonalAction
        InfoGeometry.Clifford.Clifford55.negOnePin = 1 :=
  pin_central_two_cycle_is_trivial

/-! ## 4. Explicit comparison boundary to the spectral cross term -/

/-- Scalar mixed term from the finite polynomial spectral action. -/
def spectralMixedTerm
    (c2 : ℝ) (DeltaL : StageOne) (DeltaR : Atom) : ℝ :=
  2 * c2 * (Matrix.trace DeltaL * Matrix.trace DeltaR)

/-- The spectral mixed term is an XPM energy only after an explicit
identification of the sheet densities/coupling with the trace readouts. -/
theorem spectralMixedTerm_eq_crossPhaseEnergy_of_readout
    (c2 gCross : ℝ)
    (DeltaL : StageOne) (DeltaR : Atom)
    (s : TwinDensity)
    (hread :
      gCross * s.nPlus * s.nMinus =
        2 * c2 * (Matrix.trace DeltaL * Matrix.trace DeltaR)) :
    crossPhaseEnergy gCross s =
      spectralMixedTerm c2 DeltaL DeltaR := by
  exact hread

/-- Equivalent comparison using separate density/readout hypotheses. -/
theorem spectralMixedTerm_eq_crossPhaseEnergy_of_factorized_readout
    (c2 gCross : ℝ)
    (DeltaL : StageOne) (DeltaR : Atom)
    (s : TwinDensity)
    (hPlus : s.nPlus = Matrix.trace DeltaL)
    (hMinus : s.nMinus = Matrix.trace DeltaR)
    (hCoupling : gCross = 2 * c2) :
    crossPhaseEnergy gCross s =
      spectralMixedTerm c2 DeltaL DeltaR := by
  rw [hPlus, hMinus, hCoupling]
  unfold crossPhaseEnergy spectralMixedTerm
  ring

/-! ## 5. Compact theorem-safe synthesis -/

theorem nonlinear_twin_wave_packet
    (gSelf gCross omega : ℝ)
    (s : TwinDensity) :
    crossPhaseEnergy gCross (sheetSwap s) =
        crossPhaseEnergy gCross s ∧
      coupledDensityEnergy gSelf gCross (sheetSwap s) =
        coupledDensityEnergy gSelf gCross s ∧
      omega - (-omega) = 2 * omega :=
  ⟨crossPhaseEnergy_sheetSwap gCross s,
    coupledDensityEnergy_sheetSwap gSelf gCross s,
    forward_backward_frequency_difference omega⟩

end InfoGeometry.Canonical.NonlinearTwinWaveOpticsBridge
