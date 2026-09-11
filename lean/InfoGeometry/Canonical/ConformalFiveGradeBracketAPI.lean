import InfoGeometry.Canonical.ConformalFiveGradeClosurePacket
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.WeylWeightBalance

/-!
# InfoGeometry.Canonical.ConformalFiveGradeBracketAPI

Importable canonical API for the five-grade bracket compatibility layer.

This file owns the bracket bookkeeping directly:

* the grade-to-Weyl-grade map;
* the bracket packet;
* the balanced-sector and grade-zero readout theorems.

It is declaration-bearing and importable.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConformalFiveGradeBracketAPI

open InfoGeometry.Canonical.ConformalFiveGradeClosurePacket
open InfoGeometry.Canonical.ConformalFiveGradeCurrentPacket
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.OperatorAlgebra.WeylWeightBalance

/-- Canonical map from conformal grades to the five Weyl grades. -/
def toWeylGrade : ConformalGrade → FiveGrade
  | ConformalGrade.negTwo => FiveGrade.m2
  | ConformalGrade.negOne => FiveGrade.m1
  | ConformalGrade.zero => FiveGrade.zero
  | ConformalGrade.posOne => FiveGrade.p1
  | ConformalGrade.posTwo => FiveGrade.p2

@[simp] theorem toWeylGrade_negTwo :
    toWeylGrade ConformalGrade.negTwo = FiveGrade.m2 := rfl

@[simp] theorem toWeylGrade_negOne :
    toWeylGrade ConformalGrade.negOne = FiveGrade.m1 := rfl

@[simp] theorem toWeylGrade_zero :
    toWeylGrade ConformalGrade.zero = FiveGrade.zero := rfl

@[simp] theorem toWeylGrade_posOne :
    toWeylGrade ConformalGrade.posOne = FiveGrade.p1 := rfl

@[simp] theorem toWeylGrade_posTwo :
    toWeylGrade ConformalGrade.posTwo = FiveGrade.p2 := rfl

/--
Direct canonical bracket packet for the five-grade conformal engine.

The packet does not manufacture a new Lie bracket from the inversion layer.
It records a bracket readout on the same owner surface and keeps the grade
bookkeeping explicit.
-/
structure FiveGradeBracketPacket
    (L : Type*) (ι : Type*) (R : Type*)
    [Fintype ι] [DecidableEq ι] [Ring R] where
  closure : FiveGradeBoundaryCurrentPacket L ι R
  gradeCarrier : WeylGradedCarrier L
  gradeCompat : ∀ x : L,
    gradeCarrier.gradeOf x = toWeylGrade (closure.inversion.grade x)
  bracket : L → L → L
  bracket_additive :
    IsAdditiveWeightForBracket gradeCarrier gradeCarrier bracket

namespace FiveGradeBracketPacket

variable {L ι R : Type*}
variable [Fintype ι] [DecidableEq ι] [Ring R]

/-- The source sector has weight `+2`. -/
theorem source_weight
    (P : FiveGradeBracketPacket L ι R)
    {x : L}
    (hx : x ∈ P.closure.sourceSet) :
    FiveGrade.weight (P.gradeCarrier.gradeOf x) = 2 := by
  have hxgrade :
      P.closure.inversion.grade x = ConformalGrade.posTwo := by
    simpa [FiveGradeBoundaryCurrentPacket.sourceSet] using hx
  rw [P.gradeCompat x, hxgrade]
  simp [toWeylGrade, FiveGrade.weight]

/-- The sink sector has weight `-2`. -/
theorem sink_weight
    (P : FiveGradeBracketPacket L ι R)
    {x : L}
    (hx : x ∈ P.closure.sinkSet) :
    FiveGrade.weight (P.gradeCarrier.gradeOf x) = -2 := by
  have hxgrade :
      P.closure.inversion.grade x = ConformalGrade.negTwo := by
    simpa [FiveGradeBoundaryCurrentPacket.sinkSet] using hx
  rw [P.gradeCompat x, hxgrade]
  simp [toWeylGrade, FiveGrade.weight]

/-- The incoming boundary sector has weight `-1`. -/
theorem incoming_weight
    (P : FiveGradeBracketPacket L ι R)
    {x : L}
    (hx : x ∈ P.closure.inversion.incomingSet) :
    FiveGrade.weight (P.gradeCarrier.gradeOf x) = -1 := by
  have hxgrade :
      P.closure.inversion.grade x = ConformalGrade.negOne := by
    simpa [FiveGradedConformalInversion.incomingSet] using hx
  rw [P.gradeCompat x, hxgrade]
  simp [toWeylGrade, FiveGrade.weight]

/-- The outgoing boundary sector has weight `+1`. -/
theorem outgoing_weight
    (P : FiveGradeBracketPacket L ι R)
    {x : L}
    (hx : x ∈ P.closure.inversion.outgoingSet) :
    FiveGrade.weight (P.gradeCarrier.gradeOf x) = 1 := by
  have hxgrade :
      P.closure.inversion.grade x = ConformalGrade.posOne := by
    simpa [FiveGradedConformalInversion.outgoingSet] using hx
  rw [P.gradeCompat x, hxgrade]
  simp [toWeylGrade, FiveGrade.weight]

/-- The modular center has weight `0`. -/
theorem center_weight
    (P : FiveGradeBracketPacket L ι R)
    {x : L}
    (hx : x ∈ P.closure.centerSet) :
    FiveGrade.weight (P.gradeCarrier.gradeOf x) = 0 := by
  have hxgrade :
      P.closure.inversion.grade x = ConformalGrade.zero := by
    simpa [FiveGradeBoundaryCurrentPacket.centerSet] using hx
  rw [P.gradeCompat x, hxgrade]
  simp [toWeylGrade, FiveGrade.weight]

/-- Source and sink are weight-balanced. -/
theorem source_sink_balanced
    (P : FiveGradeBracketPacket L ι R)
    {x y : L}
    (hx : x ∈ P.closure.sourceSet)
    (hy : y ∈ P.closure.sinkSet) :
    IsWeylBalanced P.gradeCarrier x y := by
  unfold IsWeylBalanced
  rw [P.source_weight hx, P.sink_weight hy]
  decide

/-- Incoming and outgoing are weight-balanced. -/
theorem incoming_outgoing_balanced
    (P : FiveGradeBracketPacket L ι R)
    {x y : L}
    (hx : x ∈ P.closure.inversion.incomingSet)
    (hy : y ∈ P.closure.inversion.outgoingSet) :
    IsWeylBalanced P.gradeCarrier x y := by
  unfold IsWeylBalanced
  rw [P.incoming_weight hx, P.outgoing_weight hy]
  decide

/-- The center is balanced with itself. -/
theorem center_center_balanced
    (P : FiveGradeBracketPacket L ι R)
    {x y : L}
    (hx : x ∈ P.closure.centerSet)
    (hy : y ∈ P.closure.centerSet) :
    IsWeylBalanced P.gradeCarrier x y := by
  unfold IsWeylBalanced
  rw [P.center_weight hx, P.center_weight hy]
  decide

/--
Balanced source/sink inputs bracket to the grade-zero sector of the bracket
readout.
-/
theorem source_sink_bracket_grade_zero
    (P : FiveGradeBracketPacket L ι R)
    {x y : L}
    (hx : x ∈ P.closure.sourceSet)
    (hy : y ∈ P.closure.sinkSet) :
    IsPhysicalGradeZero P.gradeCarrier (P.bracket x y) :=
  bracket_is_physical_of_balanced P.gradeCarrier P.gradeCarrier P.bracket
    P.bracket_additive (P.source_sink_balanced hx hy)

/--
Balanced incoming/outgoing inputs bracket to the grade-zero sector of the
bracket readout.
-/
theorem incoming_outgoing_bracket_grade_zero
    (P : FiveGradeBracketPacket L ι R)
    {x y : L}
    (hx : x ∈ P.closure.inversion.incomingSet)
    (hy : y ∈ P.closure.inversion.outgoingSet) :
    IsPhysicalGradeZero P.gradeCarrier (P.bracket x y) :=
  bracket_is_physical_of_balanced P.gradeCarrier P.gradeCarrier P.bracket
    P.bracket_additive (P.incoming_outgoing_balanced hx hy)

/--
Balanced center/center inputs bracket to the grade-zero sector of the bracket
readout.
-/
theorem center_center_bracket_grade_zero
    (P : FiveGradeBracketPacket L ι R)
    {x y : L}
    (hx : x ∈ P.closure.centerSet)
    (hy : y ∈ P.closure.centerSet) :
    IsPhysicalGradeZero P.gradeCarrier (P.bracket x y) :=
  bracket_is_physical_of_balanced P.gradeCarrier P.gradeCarrier P.bracket
    P.bracket_additive (P.center_center_balanced hx hy)

/-- A bracket packet obtained directly from a closure packet and bracket data. -/
def ofClosurePacket
    (P : FiveGradeBoundaryCurrentPacket L ι R)
    (gradeCarrier : WeylGradedCarrier L)
    (gradeCompat : ∀ x : L,
      gradeCarrier.gradeOf x = toWeylGrade (P.inversion.grade x))
    (bracket : L → L → L)
    (bracket_additive :
      IsAdditiveWeightForBracket gradeCarrier gradeCarrier bracket) :
    FiveGradeBracketPacket L ι R where
  closure := P
  gradeCarrier := gradeCarrier
  gradeCompat := gradeCompat
  bracket := bracket
  bracket_additive := bracket_additive

end FiveGradeBracketPacket

end InfoGeometry.Canonical.ConformalFiveGradeBracketAPI
