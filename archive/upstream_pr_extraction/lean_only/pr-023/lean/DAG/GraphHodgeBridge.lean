import DAG.GraphHodge

/-!
# DAG.GraphHodgeBridge

Canonical finite Hodge / Dirac / chiral bridge for the declaration DAG.

This module does not introduce new operators. It packages the existing finite
graph-Hodge carrier from `GraphHodge.lean` into a single coherence layer:

* `TwoComplex` is the finite discrete carrier;
* `graphDirac` is the bounded graph Dirac matrix;
* `laplacian0` and `laplacian1` are the finite Hodge Laplacians;
* `ChiralGrading` and `extendedChiralGrading` provide the grading data;
* `chiralAnticommutes` is the bounded chiral compatibility check;
* `HodgeSummary` is the readout/export packet.

The bridge is intentionally a packaging surface, not a new theorem owner.
-/

namespace DAG

/--
Canonical finite graph-Hodge operator packet.

This bundles the finite declaration two-complex together with the induced
Dirac, Laplacian, chiral, and summary readouts.
-/
structure FiniteGraphHodgePacket (α) [BEq α] [Hashable α] where
  tc : TwoComplex α
  gradingSize : Nat
  gradingMatrix : Array (Array Rat)
  dirac : Array (Array Rat)
  lap0 : Array (Array Rat)
  lap1 : Array (Array Rat)
  chiralMatrix : Array (Array Rat)
  chiralCompatible : Bool
  summary : HodgeSummary

namespace FiniteGraphHodgePacket

/--
Canonical constructor for the finite graph-Hodge packet.

The fields are populated from the owner definitions in `GraphHodge.lean`.
-/
def canonical
    {α} [BEq α] [Hashable α]
    (tc : TwoComplex α)
    (grading : ChiralGrading (tc.base.toGraph.nodes.size)) :
    FiniteGraphHodgePacket α :=
  let n := tc.base.toGraph.nodes.size
  { tc := tc
    gradingSize := n
    gradingMatrix := chiralDiagMatrix grading
    dirac := graphDirac tc
    lap0 := laplacian0 tc
    lap1 := laplacian1 tc
    chiralMatrix := extendedChiralGrading tc grading
    chiralCompatible := chiralAnticommutes tc grading
    summary := hodgeSummary tc }

end FiniteGraphHodgePacket

/--
Finite graph Hodge bridge target.

This is the canonical packaging point for the finite Hodge / Dirac / chiral
bundle in the DAG layer.
-/
def GraphHodgeBridgeTarget (α) [BEq α] [Hashable α] : Prop :=
  ∀ (tc : TwoComplex α)
    (grading : ChiralGrading (tc.base.toGraph.nodes.size)),
    ∃ B : FiniteGraphHodgePacket α,
      B.tc = tc ∧
      B.gradingSize = tc.base.toGraph.nodes.size ∧
      B.gradingMatrix = chiralDiagMatrix grading ∧
      B.dirac = graphDirac tc ∧
      B.lap0 = laplacian0 tc ∧
      B.lap1 = laplacian1 tc ∧
      B.chiralMatrix = extendedChiralGrading tc grading ∧
      B.chiralCompatible = chiralAnticommutes tc grading ∧
      B.summary = hodgeSummary tc

/-- The finite graph Hodge bridge target is closed. -/
theorem graphHodgeBridgeTarget (α) [BEq α] [Hashable α] :
    GraphHodgeBridgeTarget α := by
  intro tc grading
  refine ⟨FiniteGraphHodgePacket.canonical tc grading, ?_⟩
  simp [FiniteGraphHodgePacket.canonical]

end DAG
