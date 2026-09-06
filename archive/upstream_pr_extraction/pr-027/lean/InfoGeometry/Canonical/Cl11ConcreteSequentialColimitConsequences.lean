import InfoGeometry.Canonical.Cl11SequentialColimitSystemBridge
import InfoGeometry.Clifford.Cl11InfiniteCarrier

set_option autoImplicit false

/-!
# Concrete consequences for the `Cl(1,1)` sequential colimit system

This file connects the generic sequential-colimit interface to the concrete
Hestenes phase representative already present in the finite tower.  It proves
only algebraic carrier statements: the phase element has square `-1`, and its
finite advances have the same image in the direct-limit carrier.  No analytic
completion or factor classification is introduced.
-/

namespace InfoGeometry.Canonical.Cl11ConcreteSequentialColimitConsequences

noncomputable section

open InfoGeometry.Canonical.Cl11SequentialColimitSystemBridge
open InfoGeometry.Clifford.Cl11InfiniteCarrier
open InfoGeometry.Clifford.Cl11TensorTowerLimit

abbrev Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

/-! The concrete image of the first-stage Hestenes phase representative. -/
def phaseAxisImage : Limit :=
  ofStage 1 phaseAxisStage

theorem phaseAxisImage_eq_globalPhaseAxis :
    phaseAxisImage = globalPhaseAxis := by
  rfl

/-! The phase representative remains a square-minus-one element in the carrier. -/
theorem phaseAxisImage_sq :
    phaseAxisImage * phaseAxisImage = -(1 : Limit) := by
  rw [phaseAxisImage]
  calc
    ofStage 1 phaseAxisStage * ofStage 1 phaseAxisStage
        = ofStage 1 (phaseAxisStage * phaseAxisStage) := by
            rw [map_mul]
    _ = ofStage 1 (-(1 : InfoGeometry.Clifford.Cl11InfiniteCarrier.Stage 1)) := by
          rw [phaseAxisStage_sq]
    _ = -(1 : Limit) := by simp

/-! Every finite advance of the phase axis has the same carrier image. -/
theorem phaseAxisImage_finiteAdvance (k : ℕ) :
    ofStage (1 + k)
        (finiteAdvance 1 k phaseAxisStage) = phaseAxisImage := by
  change intoCarrier (1 + k) (finiteAdvance 1 k phaseAxisStage) =
    intoCarrier 1 phaseAxisStage
  exact intoCarrier_finiteAdvance 1 k phaseAxisStage

/-! The concrete phase element induces the usual inner derivation law. -/
theorem phaseAxisImage_commutator_derivation (X Y : Limit) :
    (phaseAxisImage * (X * Y) - (X * Y) * phaseAxisImage) =
      (phaseAxisImage * X - X * phaseAxisImage) * Y +
        X * (phaseAxisImage * Y - Y * phaseAxisImage) := by
  exact ringCommutator_isDerivation phaseAxisImage X Y

end

end InfoGeometry.Canonical.Cl11ConcreteSequentialColimitConsequences
