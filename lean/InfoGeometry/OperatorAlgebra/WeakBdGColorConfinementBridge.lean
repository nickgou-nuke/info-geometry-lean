import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.ColeFuryIdeals
import InfoGeometry.OperatorAlgebra.ColorConfinementBRSTBridge
import InfoGeometry.OperatorAlgebra.SplitOctonionStandardModel
import InfoGeometry.Canonical.CanonicalZornModularAAVBridge
import InfoGeometry.Canonical.AAVWeakMeasurementKleinSeamBridge
import InfoGeometry.Canonical.IwasawaMaurerCartanBdGBridge
import InfoGeometry.Canonical.IwasawaCuntzKleinWeakBridge

noncomputable section

namespace InfoGeometry.OperatorAlgebra.WeakBdGColorConfinement

open Matrix
open InfoGeometry.OperatorAlgebra.ColeFury
open InfoGeometry.OperatorAlgebra.SplitOctonions.StandardModel
open InfoGeometry.Canonical.ZornModularAAV
open InfoGeometry.Canonical.AAVWeakMeasurementKleinSeam
open InfoGeometry.Canonical.IwasawaMaurerCartanBdG
open InfoGeometry.Canonical.IwasawaCuntzKleinWeak

abbrev Spin32Vec := Fin 32 → ℤ
abbrev Spin32End := Module.End ℤ Spin32Vec

/-!
## Step 1: Linear Endomorphism Formulation of the Horizon BRST Algebra
-/

def horizonQ : Spin32End := Matrix.toLin' horizonUp
def horizonK : Spin32End := Matrix.toLin' horizonDown
def quarkProj : Spin32End := Matrix.toLin' upperLeft
def leptonProj : Spin32End := Matrix.toLin' lowerRight
def colorGradingEnd : Spin32End := Matrix.toLin' g0Core

theorem horizonQ_nilpotent : horizonQ.comp horizonQ = 0 := by
  dsimp [horizonQ]
  rw [← toLin'_mul, horizonUp_nilpotent, map_zero toLin']

theorem horizonK_nilpotent : horizonK.comp horizonK = 0 := by
  dsimp [horizonK]
  rw [← toLin'_mul, horizonDown_nilpotent, map_zero toLin']

theorem horizon_anticomm_end : horizonQ.comp horizonK + horizonK.comp horizonQ = LinearMap.id := by
  dsimp [horizonQ, horizonK]
  rw [← toLin'_mul, ← toLin'_mul, ← map_add toLin', horizon_anticomm_identity, toLin'_one]

theorem quarkProj_eq_QK : quarkProj = horizonQ.comp horizonK := by
  dsimp [quarkProj, horizonQ, horizonK]
  rw [← toLin'_mul, horizonUp_horizonDown]

theorem leptonProj_eq_KQ : leptonProj = horizonK.comp horizonQ := by
  dsimp [leptonProj, horizonQ, horizonK]
  rw [← toLin'_mul, horizonDown_horizonUp]

theorem colorGrading_eq_commutator : colorGradingEnd = horizonK.comp horizonQ - horizonQ.comp horizonK := by
  dsimp [colorGradingEnd, horizonQ, horizonK]
  rw [← toLin'_mul, ← toLin'_mul, ← map_sub toLin']
  rfl

/-!
## Step 2: Boundary Zero-Mode State & Kugo-Ojima Exactness
-/

structure ModularHorizonBoundaryState where
  psi : Spin32Vec
  h_boundary_zero_mode : horizonQ psi = 0

theorem horizon_kugo_ojima_exactness (S : ModularHorizonBoundaryState) :
    S.psi = horizonQ (horizonK S.psi) := by
  have h_id := LinearMap.congr_fun horizon_anticomm_end S.psi
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    S.h_boundary_zero_mode, map_zero, add_zero] at h_id
  exact h_id.symm

theorem horizon_quark_projection_brst_exact (S : ModularHorizonBoundaryState) :
    quarkProj S.psi = horizonQ (horizonK S.psi) := by
  rw [quarkProj_eq_QK]
  rfl

theorem horizon_lepton_projection_vanishes (S : ModularHorizonBoundaryState) :
    leptonProj S.psi = 0 := by
  rw [leptonProj_eq_KQ]
  change horizonK (horizonQ S.psi) = 0
  rw [S.h_boundary_zero_mode, map_zero]

theorem horizon_color_grading_brst_exact (S : ModularHorizonBoundaryState) :
    colorGradingEnd S.psi = - horizonQ (horizonK S.psi) := by
  rw [colorGrading_eq_commutator]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, S.h_boundary_zero_mode, map_zero, zero_sub]

/-!
## Step 3: Synthesis Packet Linking BdG Horizon Vanishing to BRST Confinement
-/

structure WeakBdGConfinementSynthesis where
  divergence_condition : ∀ num t M : ℝ, t > 0 → M > 0 → t < num / M →
    aharonovWeakValue num t > M
  mass_gap_pos : ∀ xi num t : ℝ, num ≠ 0 → t ≠ 0 →
    bdgEnergySq xi (aharonovWeakValue num t) > xi * xi
  krein_seam_vanishes : ∀ p : SpacetimePoint, isKleinSeam p →
    kreinDiracPairing (postState p.t) preState = 0
  brst_exactness : ∀ S : ModularHorizonBoundaryState,
    quarkProj S.psi = horizonQ (horizonK S.psi)
  lepton_vanishes : ∀ S : ModularHorizonBoundaryState,
    leptonProj S.psi = 0
  color_grading_exact : ∀ S : ModularHorizonBoundaryState,
    colorGradingEnd S.psi = - horizonQ (horizonK S.psi)
  kugo_ojima_identity : ∀ S : ModularHorizonBoundaryState,
    S.psi = horizonQ (horizonK S.psi)

def makeWeakBdGConfinementSynthesis : WeakBdGConfinementSynthesis where
  divergence_condition := fun num t M ht hM hbound => by
    dsimp [aharonovWeakValue]
    rw [gt_iff_lt]
    have h1 : M * t < num := by
      calc M * t < M * (num / M) := (mul_lt_mul_iff_of_pos_left hM).mpr hbound
        _ = num := mul_div_cancel₀ num (ne_of_gt hM)
    exact (lt_div_iff₀ ht).mpr h1
  mass_gap_pos := weak_induced_mass_gap_positive
  krein_seam_vanishes := seam_implies_krein_orthogonality
  brst_exactness := horizon_quark_projection_brst_exact
  lepton_vanishes := horizon_lepton_projection_vanishes
  color_grading_exact := horizon_color_grading_brst_exact
  kugo_ojima_identity := horizon_kugo_ojima_exactness

theorem weak_bdg_confinement_synthesis_certified :
    makeWeakBdGConfinementSynthesis.lepton_vanishes = horizon_lepton_projection_vanishes :=
  rfl

end InfoGeometry.OperatorAlgebra.WeakBdGColorConfinement
