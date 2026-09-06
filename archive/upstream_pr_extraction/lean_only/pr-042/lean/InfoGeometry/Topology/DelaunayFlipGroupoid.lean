import InfoGeometry.Topology.DelaunayPureBraidInvariant
import InfoGeometry.Physics.WeightGrading55
import InfoGeometry.Algebra.Cl11Fermions
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Canonical.FiveGradedMobiusWittenGlobality

/-!
# Delaunay flip groupoid boundary with explicit compensation obligations

This file adds a topology-side owner for the extra data that a raw Delaunay
pure-braid matrix audit does not carry:

* a chosen flip word / quotient object;
* a witnessed Delaunay move equivalence between source and target words;
* a separate finite chiral-compensation packet;

The proved content here is intentionally minimal:

* `DelaunayFlipMorphism` transports the existing move property;
* `matrix_of_morphism_well_defined` is exactly the already-proved Rohozhkin
  matrix invariance under `DelaunayEquiv`;
* the compensation field carries concrete Cl(1,1) relations.

Boundary: this file does not prove any global Witten index theorem, any Möbius
trace cancellation theorem, or any five-graded closure theorem.
-/

namespace InfoGeometry.Topology.Delaunay

open InfoGeometry.Physics
open Cl11Fermions
open InfoGeometry.Physics.WeightGrading55.JordanMatrix10D
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Canonical.Globality

/-- An object in the Delaunay flip groupoid boundary is a witnessed flip word. -/
abbrev DelaunayFlipObject (n : ℕ) := DelaunayFlipWord n

namespace DelaunayFlipObject

abbrev word {n : ℕ} (X : DelaunayFlipObject n) : DelaunayFlipWord n := X

end DelaunayFlipObject

/--
Finite local compensation data carried alongside a Delaunay object.

This is the smallest explicit bridge to the five-graded/chiral side currently
available in repo: a Jordan-state refined orbit tag together with a concrete
Cl(1,1) nilpotent/anticommuting pair.
-/
structure LocalCompensationBoundary where
  ePlus : CliffordAlgebra q11
  eMinus : CliffordAlgebra q11
  ePlus_sq : ePlus * ePlus = 0
  eMinus_sq : eMinus * eMinus = 0
  anticommutator : ePlus * eMinus + eMinus * ePlus = 1

/--
Finite compensation data carried alongside a Delaunay object.

This is the smallest explicit bridge to the five-graded/chiral side currently
available in repo: a Jordan-state refined orbit tag together with the concrete
local Cl(1,1) compensation packet.
-/
structure DelaunayCompensationBoundary where
  state : OrbitClassification55.JordanMatrix10D
  refinedOrbit : WeightGrading55.JordanMatrix10D.RefinedOrbitType state
  localCompensation : LocalCompensationBoundary
  /-- Genuine five-grade inversion acting on the Delaunay compensation carrier. -/
  fiveGradeInversion :
    FiveGradedConformalInversion OrbitClassification55.JordanMatrix10D
  /-- Genuine recursive grade-two compensation ledger. -/
  gradeTwoLedger :
    GradeTwoInformationLedger OrbitClassification55.JordanMatrix10D PUnit

/-- A morphism is a witnessed Delaunay word equivalence with local compensation. -/
structure DelaunayFlipMorphism (n : ℕ) where
  source : DelaunayFlipObject n
  target : DelaunayFlipObject n
  moveWitness : DelaunayEquiv source.word target.word
  compensation : DelaunayCompensationBoundary

/-- The matrix attached to a groupoid object is the existing Rohozhkin matrix. -/
def objectMatrix {n : ℕ} (X : DelaunayFlipObject n) :
    Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ :=
  rohozhkinMatrix X.word

/-- The matrix transported by a morphism is read from its source object. -/
def matrixOfMorphism {n : ℕ} (f : DelaunayFlipMorphism n) :
    Matrix (Fin (rohozhkinDim n)) (Fin (rohozhkinDim n)) ℚ :=
  objectMatrix f.source

/--
Existing Delaunay move invariance shows that the source and target matrices of a
morphism agree.  The local compensation data are orthogonal to this existing
matrix invariance theorem.
-/
theorem matrix_of_morphism_well_defined {n : ℕ} (f : DelaunayFlipMorphism n) :
    objectMatrix f.source = objectMatrix f.target := by
  exact rohozhkin_invariant_under_equiv f.moveWitness

/-- Delaunay compensation exchanges the two extreme five-grade sectors. -/
theorem compensation_source_iff_sink
    (C : DelaunayCompensationBoundary)
    (x : OrbitClassification55.JordanMatrix10D) :
    x ∈ C.fiveGradeInversion.sourceSet ↔
      C.fiveGradeInversion.theta x ∈ C.fiveGradeInversion.sinkSet :=
  C.fiveGradeInversion.mem_source_iff_mem_sink x

/-- Delaunay compensation exchanges incoming and outgoing grade-one sectors. -/
theorem compensation_incoming_iff_outgoing
    (C : DelaunayCompensationBoundary)
    (x : OrbitClassification55.JordanMatrix10D) :
    x ∈ C.fiveGradeInversion.incomingSet ↔
      C.fiveGradeInversion.theta x ∈ C.fiveGradeInversion.outgoingSet :=
  C.fiveGradeInversion.mem_incoming_iff_mem_outgoing x

/-- The Delaunay grade-two ledger obeys its recursive compensation law. -/
theorem compensation_recursive_gradeTwo
    (C : DelaunayCompensationBoundary)
    (step : ℝ) (n : ℕ) :
    C.gradeTwoLedger.visible C.state -
        C.gradeTwoLedger.visible
          (stateAt C.gradeTwoLedger step C.state n) =
      C.gradeTwoLedger.gradeTwo
          (stateAt C.gradeTwoLedger step C.state n) -
        C.gradeTwoLedger.gradeTwo C.state :=
  recursive_visibleLoss_eq_gradeTwoGain
    C.gradeTwoLedger step C.state n

/--
Concrete replacement for the former unconstrained `fiveGradedClosure : Prop`
field.  Closure means that the chosen five-grade inversion exchanges both
opposite pairs of boundary sectors.
-/
def DelaunayFlipMorphism.fiveGradedClosure
    {n : ℕ} (f : DelaunayFlipMorphism n) : Prop :=
  ∀ x : OrbitClassification55.JordanMatrix10D,
    (x ∈ f.compensation.fiveGradeInversion.sourceSet ↔
        f.compensation.fiveGradeInversion.theta x ∈
          f.compensation.fiveGradeInversion.sinkSet) ∧
      (x ∈ f.compensation.fiveGradeInversion.incomingSet ↔
        f.compensation.fiveGradeInversion.theta x ∈
          f.compensation.fiveGradeInversion.outgoingSet)

/-- Every Delaunay flip morphism satisfies its derived five-grade closure law. -/
theorem DelaunayFlipMorphism.fiveGradedClosure_holds
    {n : ℕ} (f : DelaunayFlipMorphism n) :
    f.fiveGradedClosure := by
  intro x
  exact ⟨compensation_source_iff_sink f.compensation x,
    compensation_incoming_iff_outgoing f.compensation x⟩

/--
Concrete replacement for the former unconstrained `mobiusRecursion : Prop`
field.  The historical name now denotes the recursive grade-two compensation
identity owned by `GradeTwoInformationLedger`.
-/
def DelaunayFlipMorphism.mobiusRecursion
    {n : ℕ} (f : DelaunayFlipMorphism n) : Prop :=
  ∀ (step : ℝ) (k : ℕ),
    f.compensation.gradeTwoLedger.visible f.compensation.state -
        f.compensation.gradeTwoLedger.visible
          (stateAt f.compensation.gradeTwoLedger step
            f.compensation.state k) =
      f.compensation.gradeTwoLedger.gradeTwo
          (stateAt f.compensation.gradeTwoLedger step
            f.compensation.state k) -
        f.compensation.gradeTwoLedger.gradeTwo f.compensation.state

/-- Every Delaunay flip morphism satisfies its derived recursion law. -/
theorem DelaunayFlipMorphism.mobiusRecursion_holds
    {n : ℕ} (f : DelaunayFlipMorphism n) :
    f.mobiusRecursion := by
  intro step k
  exact compensation_recursive_gradeTwo f.compensation step k

/-- The concrete local Cl(1,1) packet can always be inserted as compensation data. -/
def defaultLocalCompensation : LocalCompensationBoundary :=
  { ePlus := b
    eMinus := bdag
    ePlus_sq := b_sq
    eMinus_sq := bdag_sq
    anticommutator := anticomm_bbdag }

end InfoGeometry.Topology.Delaunay
