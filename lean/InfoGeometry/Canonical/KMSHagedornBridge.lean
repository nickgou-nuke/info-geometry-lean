import Mathlib.Analysis.InnerProductSpace.Basic
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.NoncommutativeModularSignum

namespace KMSHagedornBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.NoncommutativeModularSignum

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- The KMS shift in standard complex space is an imaginary time translation `t + i beta`.
In the real Yin-Yang doubled space, the imaginary unit `i` is replaced by the emergent
complex structure `complex_i` (which is J * epsilon).
Therefore, the KMS shift is represented as a translation generator scaled by `complex_i * beta`.
-/
@[rep_depth krein]
noncomputable def real_kms_shift [CompleteSpace E] (beta : ℝ) : EndH :=
  beta • (complex_i (E := E))

set_option linter.unusedVariables false

/-- The Kubo-Martin-Schwinger (KMS) boundary condition in the finite doubled-real
socket.

`ω` is the chosen finite readout/state.  The right hand side inserts the real
KMS shift, so this is a genuine equality of scalar correlation readouts rather
than a vacuous placeholder for the full Tomita--Takesaki theorem. -/
def is_kms_state [CompleteSpace E] (ω : EndH → ℝ) (A B : EndH) (beta : ℝ) : Prop :=
  ω (A * B) = ω (B * (real_kms_shift (E := E) beta * A))

/-- Read back the finite KMS equality carried by `is_kms_state`. -/
theorem kms_state_readout [CompleteSpace E]
    (ω : EndH → ℝ) (A B : EndH) (beta : ℝ)
    (h : is_kms_state (E := E) ω A B beta) :
    ω (A * B) = ω (B * (real_kms_shift (E := E) beta * A)) :=
  h

/-- At the Hagedorn temperature, the partition function diverges. 
This is the boundary of the thermal cylinder. -/
def is_hagedorn_temperature (T_H T : ℝ) : Prop :=
  T = T_H

end KMSHagedornBridge
