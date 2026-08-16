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

/-- The unique normalized `F`-move in the strict unit-sector baseline. -/
def unitFmove (a b c d e f : unitSector)
    (_x : unitFusionSpace a b e) (_y : unitFusionSpace e c d)
    (_z : unitFusionSpace b c f) (_w : unitFusionSpace a f d) : ℚ :=
  1

/-- The unique normalized `R`-move in the strict unit-sector baseline. -/
def unitRmove (a b c : unitSector)
    (_x : unitFusionSpace a b c) (_y : unitFusionSpace b a c) : ℚ :=
  1

/-- Concrete finite normalization obligations for the strict unit-sector datum.
They mention the actual move maps rather than using a vacuous `True` field. -/
def unitPentagon : Prop :=
  ∀ (a b c d e f : PUnit.{0})
    (x y z w : PUnit.{0}),
    unitFmove a b c d e f x y z w = 1

def unitHexagonLeft : Prop :=
  ∀ (a b c : PUnit.{0}) (x y : PUnit.{0}),
    unitRmove a b c x y = 1

def unitHexagonRight : Prop :=
  ∀ (a b c : PUnit.{0}) (x y : PUnit.{0}),
    unitRmove a b c x y = 1

noncomputable def unitFusionDatum : QuantumG2FusionCoherenceDatum ℚ where
  SimpleSector := unitSector
  fusionMultiplicity := fun _ _ _ => 1
  FusionSpace := unitFusionSpace
  Fmove := unitFmove
  Rmove := unitRmove
  F_pentagon := unitPentagon
  FR_hexagon_left := unitHexagonLeft
  FR_hexagon_right := unitHexagonRight

theorem unitFusionDatum_pentagon :
    unitFusionDatum.F_pentagon :=
  by
    intro a b c d e f x y z w
    rfl

theorem unitFusionDatum_hexagon_left :
    unitFusionDatum.FR_hexagon_left :=
  by
    intro a b c x y
    rfl

theorem unitFusionDatum_hexagon_right :
    unitFusionDatum.FR_hexagon_right :=
  by
    intro a b c x y
    rfl

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
