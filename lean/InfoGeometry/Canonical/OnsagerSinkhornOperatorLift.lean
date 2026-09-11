import InfoGeometry.Canonical.OnsagerReciprocity
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.OnsagerSinkhornOperatorLift

Operatorial lift of the Sinkhorn relative-volume defect lane to the maintained
Onsager response line in the canonical trunk.

This file introduces no new dynamics. It only packages:

- absolute Onsager response readout from `responseCoefficient`,
- reciprocal swap symmetry on that readout,
- a bridge from Sinkhorn RN-barrier trajectory bounds to one-step monotone
  Onsager-response bounds.
-/

namespace InfoGeometry.Canonical.OnsagerSinkhornOperatorLift

open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Absolute operatorial Onsager response readout on a fixed perturbation pair. -/
@[rep_depth transport]
noncomputable def onsagerResponseAbs
    (P : PotentialDatum (E := E)) (X Y A : EndH) : ℝ :=
  |responseCoefficient (E := E) P X Y A|

@[rep_depth transport]
theorem onsagerResponseAbs_nonneg
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    0 ≤ onsagerResponseAbs (E := E) P X Y A := by
  unfold onsagerResponseAbs
  exact abs_nonneg _

/-- Onsager reciprocity keeps the absolute response invariant under channel swap. -/
@[rep_depth transport]
theorem onsagerResponseAbs_swap
    (P : PotentialDatum (E := E)) (X Y A : EndH) :
    onsagerResponseAbs (E := E) P X Y A
      =
    onsagerResponseAbs (E := E) P Y X A := by
  unfold onsagerResponseAbs
  simp [responseCoefficient_swap (E := E) P X Y A]

/--
Bridge data: an abstract barrier trajectory controls one-step Onsager response
in the operator lane.
-/
@[rep_depth transport]
structure SinkhornOnsagerResponseBridge where
  barrier : Nat → ℝ
  barrier_monotone :
    ∀ k : Nat, barrier (k + 1) ≤ barrier k
  P : PotentialDatum (E := E)
  channelX : EndH
  channelY : EndH
  stateOperator : Nat → EndH
  next_le_barrierNext :
    ∀ k : Nat,
      onsagerResponseAbs (E := E) P channelX channelY (stateOperator (k + 1))
        ≤ barrier (k + 1)
  barrier_le_now :
    ∀ k : Nat,
      barrier k
        ≤ onsagerResponseAbs (E := E) P channelX channelY (stateOperator k)

/--
Sinkhorn RN-barrier monotonicity forces one-step monotone decay of the absolute
operatorial Onsager response.
-/
@[rep_depth transport]
theorem onsagerResponseAbs_next_le_now
    (B : SinkhornOnsagerResponseBridge (E := E))
    (k : Nat) :
    onsagerResponseAbs (E := E) B.P B.channelX B.channelY (B.stateOperator (k + 1))
      ≤
    onsagerResponseAbs (E := E) B.P B.channelX B.channelY (B.stateOperator k) := by
  exact le_trans (B.next_le_barrierNext k)
    (le_trans (B.barrier_monotone k) (B.barrier_le_now k))

/--
The same one-step monotone response bound expressed on the swapped Onsager
channel pair.
-/
@[rep_depth transport]
theorem onsagerResponseAbs_next_le_now_swap
    (B : SinkhornOnsagerResponseBridge (E := E))
    (k : Nat) :
    onsagerResponseAbs (E := E) B.P B.channelY B.channelX (B.stateOperator (k + 1))
      ≤
    onsagerResponseAbs (E := E) B.P B.channelY B.channelX (B.stateOperator k) := by
  calc
    onsagerResponseAbs (E := E) B.P B.channelY B.channelX (B.stateOperator (k + 1))
        =
      onsagerResponseAbs (E := E) B.P B.channelX B.channelY (B.stateOperator (k + 1)) := by
          symm
          exact onsagerResponseAbs_swap (E := E) B.P B.channelX B.channelY (B.stateOperator (k + 1))
    _ ≤
      onsagerResponseAbs (E := E) B.P B.channelX B.channelY (B.stateOperator k) :=
        onsagerResponseAbs_next_le_now B k
    _ =
      onsagerResponseAbs (E := E) B.P B.channelY B.channelX (B.stateOperator k) :=
        onsagerResponseAbs_swap (E := E) B.P B.channelX B.channelY (B.stateOperator k)

end Core

end InfoGeometry.Canonical.OnsagerSinkhornOperatorLift
