import InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger
import InfoGeometry.Canonical.WeylGWVolumeBridge
import InfoGeometry.Canonical.BKMDriftMetric
import InfoGeometry.Canonical.WeylNormalizedCARCCRBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.WeylFiveGradeBalanceBridge

Canonical socket for five-grade Weyl balance.

The repository already owns a five-graded algebra/accounting lane in
`OperatorAlgebra.FiveGradedInformationLedger`.  This file does not redefine that
owner surface and does not assert Virasoro, Kac-Moody, Sugawara, or global
anomaly-cancellation theorems.

It records the common algebraic bookkeeping behind the already-installed
normalization gates:

```text
  +2 intensity × -2 gauge  -> 0 physical readout,
  +1 creator   × -1 gauge  -> 0 canonical ladder bracket,
  -1/+1 bracket            -> grade zero in a five-grading.
```

Central-charge or Tomita mirror cancellation is kept as an external predicate.
-/

namespace InfoGeometry.Canonical.WeylFiveGradeBalanceBridge

open InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger

/-! ## 1. Pure finite Weyl-grade bookkeeping -/

/-- The five Weyl grades used by the projective normalization sockets. -/
@[rep_depth operator]
inductive WeylFiveGrade where
  | negTwo
  | negOne
  | zero
  | posOne
  | posTwo
deriving DecidableEq, Repr

namespace WeylFiveGrade

/-- Integer weight attached to a five-grade label. -/
@[rep_depth operator]
def weight : WeylFiveGrade → ℤ
  | negTwo => -2
  | negOne => -1
  | zero => 0
  | posOne => 1
  | posTwo => 2

/-- Two labels are balanced exactly when their integer weights sum to zero. -/
@[rep_depth operator]
def Balanced (a b : WeylFiveGrade) : Prop :=
  a.weight + b.weight = 0

@[rep_depth operator]
theorem posTwo_negTwo_balanced :
    Balanced posTwo negTwo := by
  rfl

@[rep_depth operator]
theorem negTwo_posTwo_balanced :
    Balanced negTwo posTwo := by
  rfl

@[rep_depth operator]
theorem posOne_negOne_balanced :
    Balanced posOne negOne := by
  rfl

@[rep_depth operator]
theorem negOne_posOne_balanced :
    Balanced negOne posOne := by
  rfl

@[rep_depth operator]
theorem zero_zero_balanced :
    Balanced zero zero := by
  rfl

end WeylFiveGrade

/-! ## 2. Readout carrier for five-grade assignment -/

/--
Carrier assigning Weyl five-grades to arbitrary objects.

This is data only.  The statement that an object's grade matches a concrete
operator, current, or gauge realization belongs to the relevant owner module.
-/
@[rep_depth operator]
structure WeylFiveGradeAssignment
    (Obj : Type*) where
  grade : Obj → WeylFiveGrade

namespace WeylFiveGradeAssignment

variable {Obj : Type*}
variable (A : WeylFiveGradeAssignment Obj)

@[rep_depth operator]
theorem grade_apply (x : Obj) :
    A.grade x = A.grade x := rfl

/-- External balance readback for two assigned objects. -/
@[rep_depth operator]
def BalancedPair (x y : Obj) : Prop :=
  WeylFiveGrade.Balanced (A.grade x) (A.grade y)

end WeylFiveGradeAssignment

/-! ## 3. Fusion with the existing five-graded algebra owner -/

/--
Canonical socket connecting the finite Weyl-grade bookkeeping to an existing
five-grading on a Lie algebra.
-/
@[rep_depth operator]
structure FiveGradedWeylBalanceFusion
    (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] where
  grading : FiveGrading L

namespace FiveGradedWeylBalanceFusion

variable {L : Type*} [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L]
variable (F : FiveGradedWeylBalanceFusion L)

/-- Existing owner theorem: `g₋₁` with `g₊₁` brackets into `g₀`. -/
@[rep_depth operator]
theorem negOne_posOne_mem_zero
    {X Y : L}
    (hX : X ∈ F.grading.gNegOne)
    (hY : Y ∈ F.grading.gPosOne) :
    ⁅X, Y⁆ ∈ F.grading.gZero :=
  F.grading.negOne_posOne_mem_zero hX hY

/-- Existing owner field: `g₋₂` with `g₊₂` brackets into `g₀`. -/
@[rep_depth operator]
theorem negTwo_posTwo_mem_zero
    {X Y : L}
    (hX : X ∈ F.grading.gNegTwo)
    (hY : Y ∈ F.grading.gPosTwo) :
    ⁅X, Y⁆ ∈ F.grading.gZero :=
  F.grading.bracket_negTwo_posTwo X Y hX hY

/-- Existing owner theorem: same positive grade-one brackets land in `g₊₂`. -/
@[rep_depth operator]
theorem posOne_posOne_mem_posTwo
    {X Y : L}
    (hX : X ∈ F.grading.gPosOne)
    (hY : Y ∈ F.grading.gPosOne) :
    ⁅X, Y⁆ ∈ F.grading.gPosTwo :=
  F.grading.posOne_posOne_mem_posTwo hX hY

/-- Existing owner theorem: same negative grade-one brackets land in `g₋₂`. -/
@[rep_depth operator]
theorem negOne_negOne_mem_negTwo
    {X Y : L}
    (hX : X ∈ F.grading.gNegOne)
    (hY : Y ∈ F.grading.gNegOne) :
    ⁅X, Y⁆ ∈ F.grading.gNegTwo :=
  F.grading.negOne_negOne_mem_negTwo hX hY

end FiveGradedWeylBalanceFusion

/-! ## 4. Central/Tomita balance as an external predicate -/

/--
Carrier for source/sink central-charge or anomaly readouts.

No cancellation law is bundled here.
-/
@[rep_depth operator]
structure TomitaCentralBalanceCarrier
    (State Charge : Type*) where
  sourceCharge : State → Charge
  sinkCharge : State → Charge
  totalCharge : State → Charge

/-- External predicate: total charge is source plus sink. -/
@[rep_depth operator]
def TotalChargeSplits
    {State Charge : Type*} [Add Charge]
    (C : TomitaCentralBalanceCarrier State Charge) : Prop :=
  ∀ s : State, C.totalCharge s = C.sourceCharge s + C.sinkCharge s

/-- External predicate: source and sink charges cancel. -/
@[rep_depth operator]
def SourceSinkChargesCancel
    {State Charge : Type*} [AddMonoid Charge]
    (C : TomitaCentralBalanceCarrier State Charge) : Prop :=
  ∀ s : State, C.sourceCharge s + C.sinkCharge s = 0

namespace TomitaCentralBalanceCarrier

variable {State Charge : Type*}
variable (C : TomitaCentralBalanceCarrier State Charge)

@[rep_depth operator]
theorem sourceCharge_apply (s : State) :
    C.sourceCharge s = C.sourceCharge s := rfl

@[rep_depth operator]
theorem sinkCharge_apply (s : State) :
    C.sinkCharge s = C.sinkCharge s := rfl

@[rep_depth operator]
theorem totalCharge_apply (s : State) :
    C.totalCharge s = C.totalCharge s := rfl

variable [AddMonoid Charge]

/--
If the total charge splits as source plus sink and source/sink cancel, the
total readout is zero.
-/
@[rep_depth operator]
theorem totalCharge_eq_zero
    (hSplit : TotalChargeSplits C)
    (hCancel : SourceSinkChargesCancel C)
    (s : State) :
    C.totalCharge s = 0 := by
  rw [hSplit s, hCancel s]

end TomitaCentralBalanceCarrier

end InfoGeometry.Canonical.WeylFiveGradeBalanceBridge
