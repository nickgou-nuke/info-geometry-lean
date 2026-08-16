import Mathlib.Tactic
import InfoGeometry.Recovered.SplitQuaternionMatricesRecovered

/-!
# Twistor Plücker bridge — algebraic core

This recovered file no longer installs unproved Bost-Connes/amplituhedron
identifications.  It keeps only the elementary split-quaternion matrix interval
calculation and records the Hestenes--Krein/categorical colimit bridge as a
statement shape.
-/

namespace InfoGeometry.Recovered.TwistorAmplituhedronPluckerBridge

open Matrix
open InfoGeometry.SplitQuaternion

/-- Embed a real thermal readout on the time axis. -/
noncomputable def thermalSpacetimeEmbedding (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  spacetimeMatrix r 0 0 0

/-- Difference matrix between two scalar thermal readouts. -/
noncomputable def thermalPluckerMatrix (r s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  thermalSpacetimeEmbedding s - thermalSpacetimeEmbedding r

/-- The determinant of a pure time-axis difference is the square of the scalar
difference. -/
theorem thermalPluckerDeterminant_eq_sq (r s : ℝ) :
    (thermalPluckerMatrix r s).det = (s - r) ^ 2 := by
  dsimp [thermalPluckerMatrix, thermalSpacetimeEmbedding]
  have hdiff : spacetimeMatrix s 0 0 0 - spacetimeMatrix r 0 0 0 =
      spacetimeMatrix (s - r) 0 0 0 := by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [spacetimeMatrix, splitOne, splitI, splitJ, splitK]
  rw [hdiff, det_spacetimeMatrix]
  ring

/-- Statement shape for any later colimit/amplituhedron interpretation of the
same determinant calculation. -/
def nicaAmplituhedronVolume_from_twistorDeterminants_statement : Prop :=
  ∀ readout01 readout23 volume : ℝ,
    volume = Real.sqrt ((readout01) ^ 2) * Real.sqrt ((readout23) ^ 2)

/-- The unrestricted volume-identification statement is inconsistent: the
unconstrained volume parameter cannot equal the prescribed value for all
inputs.  This keeps the later colimit/amplituhedron bridge theorem-honest. -/
theorem nicaAmplituhedronVolume_statement_false :
    ¬ nicaAmplituhedronVolume_from_twistorDeterminants_statement := by
  intro h
  have hbad := h 1 1 0
  norm_num at hbad

end InfoGeometry.Recovered.TwistorAmplituhedronPluckerBridge
