import InfoGeometry.Topology.DelaunayPureBraidInvariant
import InfoGeometry.Physics.WeightGrading55
import InfoGeometry.Algebra.Cl11Fermions

/-!
# Delaunay flip groupoid boundary with explicit compensation obligations

This file adds a topology-side owner for the extra data that a raw Delaunay
pure-braid matrix audit does not carry:

* a chosen flip word / quotient object;
* a witnessed Delaunay move equivalence between source and target words;
* a separate finite chiral-compensation packet;
* explicit placeholders for five-graded closure and Möbius-recursion obligations.

The proved content here is intentionally minimal:

* `DelaunayFlipMorphism` transports the existing move witness;
* `matrix_of_morphism_well_defined` is exactly the already-proved Rohozhkin
  matrix invariance under `DelaunayEquiv`;
* the additional compensation/globality fields are explicit data, not claimed
  theorems.

Boundary: this file does not prove any global Witten index theorem, any Möbius
trace cancellation theorem, or any five-graded closure theorem.
-/

namespace InfoGeometry.Topology.Delaunay

open InfoGeometry.Physics
open Cl11Fermions
open InfoGeometry.Physics.WeightGrading55.JordanMatrix10D

/-- An object in the Delaunay flip groupoid boundary is a witnessed flip word. -/
structure DelaunayFlipObject (n : ℕ) where
  word : DelaunayFlipWord n

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

/--
A morphism is a witnessed Delaunay word equivalence together with the extra
non-topological obligations kept explicit as fields rather than hidden claims.
-/
structure DelaunayFlipMorphism (n : ℕ) where
  source : DelaunayFlipObject n
  target : DelaunayFlipObject n
  moveWitness : DelaunayEquiv source.word target.word
  compensation : DelaunayCompensationBoundary
  fiveGradedClosure : Prop
  mobiusRecursion : Prop

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
morphism agree.  The compensation/globality fields do not participate in this
proof yet; they are kept as explicit extra obligations.
-/
theorem matrix_of_morphism_well_defined {n : ℕ} (f : DelaunayFlipMorphism n) :
    objectMatrix f.source = objectMatrix f.target := by
  exact rohozhkin_invariant_under_equiv f.moveWitness

/-- The concrete local Cl(1,1) packet can always be inserted as compensation data. -/
def defaultLocalCompensation : LocalCompensationBoundary :=
  { ePlus := b
    eMinus := bdag
    ePlus_sq := b_sq
    eMinus_sq := bdag_sq
    anticommutator := anticomm_bbdag }

end InfoGeometry.Topology.Delaunay
