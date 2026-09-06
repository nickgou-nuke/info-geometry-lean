import InfoGeometry.Clifford.Cl11Quaternion
import InfoGeometry.Canonical.HestenesRealStructures
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Clifford

open InfoGeometry.Krein
open InfoGeometry.Canonical.HestenesRealStructures

/-!
# Biquaternion Representation in the Spire

This module formalizes Biquaternions as the $K$-complexification of the 
split-quaternion core. 

Under the Pauli Mandate, we avoid the scalar complex `i` and instead use 
the operatorial phase axis $K = J ∘ ε$.
-/

/-- 
Biquaternions represented as purely real operators on the doubled Krein space.
A biquaternion $X$ is realized as a $K$-linear operator:
$X = \begin{pmatrix} A & -B \\ B & A \end{pmatrix}$
where $A$ and $B$ are real split-quaternions.
-/
@[rep_depth operator]
structure Biquaternion (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  op : DoubledSpace E →L[ℝ] DoubledSpace E
  is_k_linear : InfoGeometry.Canonical.BogoliubovTransport.IsPhaseLinear (E := E) op
  is_biquaternionic : 
    ∃ (A B : DoubledSpace E →L[ℝ] DoubledSpace E),
      op = A + (InfoGeometry.Krein.clockAxis (E := E)).comp B

namespace Biquaternion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- 
Geometric Rotation part: The block-diagonal component of the biquaternion.
-/
@[rep_depth operator]
noncomputable def rotationPart (q : InfoGeometry.Clifford.Biquaternion E) : EndH :=
  InfoGeometry.Canonical.BogoliubovTransport.phaseLinearPart (E := E) q.op

/-- 
Geometric Boost part: The out-of-diagonal component (scaled by K).
-/
@[rep_depth operator]
noncomputable def boostPart (q : InfoGeometry.Clifford.Biquaternion E) : EndH :=
  (InfoGeometry.Krein.clockAxis (E := E)).comp
    (InfoGeometry.Canonical.BogoliubovTransport.phaseAntilinearPart (E := E) q.op)

/-- 
Lorentz transformation sector: Biquaternions acting as rotors.
For a rotor $R$, we have $R R^* = 1$ in the Krein metric.
-/
def IsRotor (q : InfoGeometry.Clifford.Biquaternion E) : Prop :=
  q.op.comp (KreinSpace.kreinAdjoint (H := H₂) q.op) = ContinuousLinearMap.id ℝ H₂

end Biquaternion

end InfoGeometry.Clifford
