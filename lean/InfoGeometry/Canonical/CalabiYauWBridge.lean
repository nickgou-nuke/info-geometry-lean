/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CalabiYauMetricRicci
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PerelmanWCore

namespace InfoGeometry.Canonical.CalabiYauBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.PerelmanW
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.SpectralInference

section WBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Constructive Calabi-Yau spectral closure state:
constant Monge-Ampere density together with vanishing spinorial scalar curvature.
-/
def MongeAmpereSpinorialClosure
    (IST : InfoSpectralTriple E) : Prop :=
  HasConstantMongeAmpereDensity IST.H ∧ spinorialScalarCurvature IST = 0

/-- Constructive spectral Calabi-Yau state (non-bridge form). -/
def CalabiYauSpinorialState (IST : InfoSpectralTriple E) : Prop :=
  spinorialScalarCurvature IST = 0

omit [FiniteDimensional ℝ E] in
/-- Constructor for the spinorial closure state. -/
private theorem mongeAmpereSpinorialClosure_mk
    (IST : InfoSpectralTriple E)
    (hConst : HasConstantMongeAmpereDensity IST.H)
    (hSpin0 : CalabiYauSpinorialState IST) :
    MongeAmpereSpinorialClosure IST := by
  exact ⟨hConst, hSpin0⟩

omit [FiniteDimensional ℝ E] in
/-- Extract spinorial vanishing from the constructive spinorial closure state. -/
private theorem spinorialScalarCurvature_eq_zero_of_mongeAmpereSpinorialClosure
    (IST : InfoSpectralTriple E)
    (hCY : MongeAmpereSpinorialClosure IST) :
    CalabiYauSpinorialState IST :=
  hCY.2

omit [FiniteDimensional ℝ E] in
/--
Connection to the `W`-flow layer:
under normalized spinorial tracking, the explicit spinorial vanishing
portion of the closure makes `W` constant.
-/
private theorem W_constant_of_spinorialClosureState
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = scalarRicciWDissipation flow s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hCY : MongeAmpereSpinorialClosure IST) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  have hBeta : ∀ t : ℝ, scalarRicciBetaFunction (E := E) flow t = 0 := by
    intro t
    rw [normalizedKaehlerRicci_beta_eq_neg_spinorial
      (E := E) flow IST t hNorm hTrack, hCY.2]
    ring
  exact w_constant_of_zero_scalarRicci_beta
    (flow := flow) (W := W) hDiff hW hBeta

omit [FiniteDimensional ℝ E] in
/--
Constructive `W`-constancy closure from an explicit zero-spinorial witness
(non-bridge form).
-/
private theorem W_constant_of_spinorialState
    (flow : ScalarRicciFlow E) (IST : InfoSpectralTriple E)
    (W : ℝ → ℝ)
    (hDiff : Differentiable ℝ W)
    (hW : ∀ s : ℝ, deriv W s = scalarRicciWDissipation flow s)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := E) flow)
    (hTrack : ∀ t : ℝ, flow t = spinorialScalarCurvature IST)
    (hSpin0 : CalabiYauSpinorialState IST) :
    ∃ c : ℝ, ∀ s : ℝ, W s = c := by
  have hBeta : ∀ t : ℝ, scalarRicciBetaFunction (E := E) flow t = 0 := by
    intro t
    rw [normalizedKaehlerRicci_beta_eq_neg_spinorial
      (E := E) flow IST t hNorm hTrack, hSpin0]
    ring
  exact w_constant_of_zero_scalarRicci_beta
    (flow := flow) (W := W) hDiff hW hBeta

end WBridge

end InfoGeometry.Canonical.CalabiYauBridge
