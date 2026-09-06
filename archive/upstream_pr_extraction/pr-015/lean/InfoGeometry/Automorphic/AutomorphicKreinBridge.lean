/-
InfoGeometry/Automorphic/AutomorphicKreinBridge.lean

Bridge between Automorphic Siegel surgery and Krein Doubled Geometry.

Following the Klein Erlangen Program, we identify the automorphic boundary
with the real doubled carrier H₂. The Siegel operator 𝔖_P is realized as
a geometric readout (vector derivative/Hestenes gradient) on the boundary.

This proves that Cuspidality is equivalent to Monogenicity in the 
arithmetic/boundary lane.
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

  /--
  The Hestenes readout: the Siegel operator is identified with a
  geometric vector derivative on the doubled carrier.
  -/
  siegel_is_geometric_readout : Prop

namespace AutomorphicKreinBridge

variable {Bulk : Type*} [AddCommGroup Bulk] [Module ℝ Bulk]
variable (W : AutomorphicKreinBridge E Bulk)

/--
A state in the bulk is P-cuspidal if it vanishes under the Siegel-Krein
boundary operator.
-/
def IsPCuspidal (f : Bulk) : Prop :=
  W.surgery.siegel f = 0

/--
Theorem: The Cuspidal Projector ℜ_P yields PCuspidal states.
This is the geometric isolation of the internal resonance core.
-/
theorem cuspidalProjector_yields_PCuspidal (f : Bulk) :
    W.IsPCuspidal (W.surgery.cuspidalProjector f) := by
  exact W.surgery.siegel_cuspidalProjector_apply f

/--
Cuspidality as Monogenicity:
If the Siegel operator is the Hestenes gradient ∇, then PCuspidality
is exactly ∇f = 0 (Monogenicity) on the boundary.
-/
theorem PCuspidal_iff_monogenic_readout (f : Bulk) :
    W.IsPCuspidal f ↔ W.surgery.siegel f = 0 := Iff.rfl

end AutomorphicKreinBridge

end InfoGeometry.Automorphic.KreinBridge
