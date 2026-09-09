/-
InfoGeometry/Automorphic/AutomorphicKreinBridge.lean

Bridge between Automorphic Siegel surgery and Krein Doubled Geometry.

The automorphic boundary is the real doubled carrier H₂.  The geometric
readout owned here is the continuous linear Siegel operator itself.  A
separate Dirac/Hestenes identification requires an equality of operators and
is not asserted by this bridge.
-/

import InfoGeometry.Automorphic.SiegelResonance
import InfoGeometry.Quantum.HestenesKahler
import InfoGeometry.Krein.DoubledSpace

noncomputable section

namespace InfoGeometry.Automorphic.KreinBridge

open InfoGeometry.Automorphic.SiegelResonance
open InfoGeometry.Quantum
open InfoGeometry.Krein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/--
The Automorphic-Krein Bridge.
Identifies the abstract Siegel Boundary with the real doubled carrier H₂.
-/
structure AutomorphicKreinBridge
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Bulk : Type*) [AddCommGroup Bulk] [Module ℝ Bulk] where
  /-- The automorphic surgery witness. -/
  surgery : SiegelEisensteinWitness Bulk (DoubledSpace E)

namespace AutomorphicKreinBridge

variable {Bulk : Type*} [AddCommGroup Bulk] [Module ℝ Bulk]
variable (W : AutomorphicKreinBridge E Bulk)

/-- The genuine operator-valued geometric boundary readout owned by the
automorphic surgery witness. -/
def geometricReadout : Bulk →ₗ[ℝ] DoubledSpace E :=
  W.surgery.siegel

@[simp]
theorem geometricReadout_eq_siegel :
    W.geometricReadout = W.surgery.siegel :=
  rfl

/--
A state in the bulk is P-cuspidal if it vanishes under the Siegel-Krein
boundary operator.
-/
def IsPCuspidal (f : Bulk) : Prop :=
  W.geometricReadout f = 0

/--
Theorem: The Cuspidal Projector ℜ_P yields PCuspidal states.
This is the geometric isolation of the internal resonance core.
-/
theorem cuspidalProjector_yields_PCuspidal (f : Bulk) :
    W.IsPCuspidal (W.surgery.cuspidalProjector f) := by
  exact W.surgery.siegel_cuspidalProjector_apply f

/-- Native kernel characterization through the owner Siegel operator. -/
theorem PCuspidal_iff_siegel_zero (f : Bulk) :
    W.IsPCuspidal f ↔ W.surgery.siegel f = 0 :=
  Iff.rfl

/--
Compatibility name for the geometric-readout kernel characterization.
No Dirac or Hestenes monogenic identification is asserted here.
-/
theorem PCuspidal_iff_monogenic_readout (f : Bulk) :
    W.IsPCuspidal f ↔ W.surgery.siegel f = 0 :=
  W.PCuspidal_iff_siegel_zero f

end AutomorphicKreinBridge

end InfoGeometry.Automorphic.KreinBridge
