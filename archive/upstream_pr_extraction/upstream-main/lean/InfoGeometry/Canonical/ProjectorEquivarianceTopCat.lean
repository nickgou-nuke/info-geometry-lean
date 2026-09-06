import InfoGeometry.Canonical.ProjectorEquivariance
import Mathlib.Topology.Category.TopCat.Basic

/-!
# TopCat readout of the projector/phase-flip packet

The projector owner supplies bounded continuous-linear maps and exact
phase-flip identities.  This file exposes them as `TopCat` endomorphisms on
the doubled carrier and transports the identities pointwise.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.ProjectorEquivarianceTopCat

open CategoryTheory
open InfoGeometry.Krein
open InfoGeometry.Canonical.ProjectorEquivariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "H₂" => DoubledSpace E

local notation "EndH" => H₂ →L[ℝ] H₂

theorem continuous_phaseFlow_operator :
    Continuous (phaseFlow (E := E) : ℝ → EndH) := by
  unfold phaseFlow
  exact (Real.continuous_cos.smul continuous_const).add
    (Real.continuous_sin.smul continuous_const)

theorem continuous_chiralBoost_operator :
    Continuous (chiralBoost (E := E) : ℝ → EndH) := by
  unfold chiralBoost
  exact (Real.continuous_cosh.smul continuous_const).add
    (Real.continuous_sinh.smul continuous_const)

def phaseFlowAction (p : ℝ × H₂) : H₂ :=
  phaseFlow (E := E) p.1 p.2

def chiralBoostAction (p : ℝ × H₂) : H₂ :=
  chiralBoost (E := E) p.1 p.2

theorem continuous_phaseFlowAction :
    Continuous (phaseFlowAction (E := E)) := by
  unfold phaseFlowAction phaseFlow
  exact
    ((Real.continuous_cos.comp continuous_fst).smul continuous_snd).add
      ((Real.continuous_sin.comp continuous_fst).smul
        ((HestenesI (E := E)).continuous.comp continuous_snd))

theorem continuous_chiralBoostAction :
    Continuous (chiralBoostAction (E := E)) := by
  unfold chiralBoostAction chiralBoost
  exact
    ((Real.continuous_cosh.comp continuous_fst).smul continuous_snd).add
      ((Real.continuous_sinh.comp continuous_fst).smul
        ((spectral_epsilon (E := E)).continuous.comp continuous_snd))

def continuousLinearMapTopCatHom (T : H₂ →L[ℝ] H₂) :
    TopCat.of H₂ ⟶ TopCat.of H₂ :=
  TopCat.ofHom
    { toFun := T
      continuous_toFun := T.continuous }

def plusProjectorTopCatHom : TopCat.of H₂ ⟶ TopCat.of H₂ :=
  continuousLinearMapTopCatHom (plusProjector (E := E))

def minusProjectorTopCatHom : TopCat.of H₂ ⟶ TopCat.of H₂ :=
  continuousLinearMapTopCatHom (minusProjector (E := E))

def plusProjectorAfterPhaseFlipTopCatHom :
    TopCat.of H₂ ⟶ TopCat.of H₂ :=
  continuousLinearMapTopCatHom (plusProjectorAfterPhaseFlip (E := E))

def minusProjectorAfterPhaseFlipTopCatHom :
    TopCat.of H₂ ⟶ TopCat.of H₂ :=
  continuousLinearMapTopCatHom (minusProjectorAfterPhaseFlip (E := E))

def modularSignTopCatHom : TopCat.of H₂ ⟶ TopCat.of H₂ :=
  continuousLinearMapTopCatHom (modularSign (E := E))

def spectralEpsilonTopCatHom : TopCat.of H₂ ⟶ TopCat.of H₂ :=
  continuousLinearMapTopCatHom (spectral_epsilon (E := E))

theorem projectorResolution_topCat (v : H₂) :
    plusProjectorTopCatHom (E := E) v +
        minusProjectorTopCatHom (E := E) v = v := by
  change spectralPlusProj (E := E) v + spectralMinusProj (E := E) v = v
  exact congrArg (fun T => T v) (spectralProj_sum (E := E))

theorem phaseFlip_plusProjector_topCat (v : H₂) :
    plusProjectorAfterPhaseFlipTopCatHom (E := E) v =
      minusProjectorTopCatHom (E := E) v := by
  simpa [plusProjectorAfterPhaseFlipTopCatHom, minusProjectorTopCatHom,
    continuousLinearMapTopCatHom] using
    congrArg (fun T => T v)
      (plusProjectorAfterPhaseFlip_eq_minusProjector (E := E))

theorem phaseFlip_minusProjector_topCat (v : H₂) :
    minusProjectorAfterPhaseFlipTopCatHom (E := E) v =
      plusProjectorTopCatHom (E := E) v := by
  simpa [minusProjectorAfterPhaseFlipTopCatHom, plusProjectorTopCatHom,
    continuousLinearMapTopCatHom] using
    congrArg (fun T => T v)
      (minusProjectorAfterPhaseFlip_eq_plusProjector (E := E))

theorem modularSign_topCat_eq_spectralEpsilon :
    modularSignTopCatHom (E := E) = spectralEpsilonTopCatHom (E := E) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  simpa [modularSignTopCatHom, spectralEpsilonTopCatHom,
    continuousLinearMapTopCatHom] using
    congrArg (fun T => T v) (modularSign_eq_spectral_epsilon (E := E))

end InfoGeometry.Canonical.ProjectorEquivarianceTopCat
