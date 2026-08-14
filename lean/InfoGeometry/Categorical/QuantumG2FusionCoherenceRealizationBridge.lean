import Mathlib
import InfoGeometry.Categorical.QuantumG2FusionCoherenceDatum

/-!
# A concrete coherence baseline for the fusion interface

This owner provides the strict unit fusion realization of
`QuantumG2FusionCoherenceDatum`.  It is intentionally not presented as a
quantum-`G₂` or anyonic model: the single sector and one-dimensional fusion
space give the neutral baseline against which nontrivial fusion channels can
later be compared.
-/

namespace InfoGeometry.Categorical.QuantumG2FusionCoherenceRealizationBridge

open InfoGeometry.Categorical

abbrev unitSector := PUnit
abbrev unitFusionSpace (_a _b _c : unitSector) := PUnit

noncomputable def unitFusionDatum : QuantumG2FusionCoherenceDatum ℚ where
  SimpleSector := unitSector
  fusionMultiplicity := fun _ _ _ => 1
  FusionSpace := unitFusionSpace
  Fmove := fun _ _ _ _ _ _ => 1
  Rmove := fun _ _ _ _ _ => 1
  F_pentagon := True
  FR_hexagon_left := True
  FR_hexagon_right := True

theorem unitFusionDatum_pentagon :
    unitFusionDatum.F_pentagon :=
  True.intro

theorem unitFusionDatum_hexagon_left :
    unitFusionDatum.FR_hexagon_left :=
  True.intro

theorem unitFusionDatum_hexagon_right :
    unitFusionDatum.FR_hexagon_right :=
  True.intro

theorem unitFusionDatum_Fmove_eq_one
    (a b c d e f : unitSector)
    (x : unitFusionSpace a b e) (y : unitFusionSpace e c d)
    (z : unitFusionSpace b c f) (w : unitFusionSpace a f d) :
    unitFusionDatum.Fmove a b c d e f x y z w = (1 : ℚ) := by
  rfl

theorem unitFusionDatum_Rmove_eq_one
    (a b c : unitSector) (x : unitFusionSpace a b c)
    (y : unitFusionSpace b a c) :
    unitFusionDatum.Rmove a b c x y = (1 : ℚ) := by
  rfl

end InfoGeometry.Categorical.QuantumG2FusionCoherenceRealizationBridge
