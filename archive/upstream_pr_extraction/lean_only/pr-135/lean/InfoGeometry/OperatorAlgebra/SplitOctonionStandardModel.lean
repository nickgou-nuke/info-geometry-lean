import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication
import InfoGeometry.OperatorAlgebra.ColeFuryIdeals

/-!
# Standard Model Particle Embedding (Split Octonion Basis)

This file defines the mapping from the 8-dimensional split-octonion basis
to the Standard Model particle quantum numbers, representing the first generation.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonions.StandardModel

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.ColeFury

/-- 
Standard Model Particle Sector Classification. 
Represents the structural projection of the 8D non-associative algebra
onto physical quantum numbers.
-/
inductive SMParticleSector
  | HiggsNeutral
  | LeptonDoublet
  | ColorTriplet
  | AntiColorTriplet
  deriving DecidableEq, Repr

/-- 
Mapping from the 8-dimensional Split Octonion basis to the Standard Model sectors.
- The diagonal unit `1 = ePlus + eMinus` maps structurally to the Higgs/neutral scalar sector.
- `ePlus` and `eMinus` form the lepton doublet projections.
- The `up_i` basis elements form the quark color triplets.
- The `down_i` basis elements form the anti-quark anti-color triplets.
-/
def basisToParticleSector : Basis8 → SMParticleSector
  | Basis8.ePlus => SMParticleSector.LeptonDoublet
  | Basis8.eMinus => SMParticleSector.LeptonDoublet
  | Basis8.up0 => SMParticleSector.ColorTriplet
  | Basis8.up1 => SMParticleSector.ColorTriplet
  | Basis8.up2 => SMParticleSector.ColorTriplet
  | Basis8.down0 => SMParticleSector.AntiColorTriplet
  | Basis8.down1 => SMParticleSector.AntiColorTriplet
  | Basis8.down2 => SMParticleSector.AntiColorTriplet

/-! ## Chiral/Gauge Structure Extensions -/

/-- 
The SU(3) color grading operator derived from the commutator of the horizon nilpotents. 
Matches `g0 = [horizonDown, horizonUp]`.
-/
abbrev colorGradingCore : Spin32Matrix := g0Core

/-- 
Quark confinement projection. 
The product `horizonUp * horizonDown` algebraically projects to `upperLeft`.
-/
theorem quark_confinement_projection : horizonUp * horizonDown = upperLeft :=
  horizonUp_horizonDown

/-- 
Lepton projection. 
The product `horizonDown * horizonUp` algebraically projects to `lowerRight`.
-/
theorem lepton_projection : horizonDown * horizonUp = lowerRight :=
  horizonDown_horizonUp

end InfoGeometry.OperatorAlgebra.SplitOctonions.StandardModel
