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

The bridge is intended to make the operator lane explicit at one point in the
namespace, instead of repeating the same finite dictionary in each consumer.
-/

namespace DAG

/--
Canonical finite graph-Hodge operator packet.

This bundles the finite declaration two-complex together with the induced
Dirac, Laplacian, chiral, and summary readouts.
-/
structure FiniteGraphHodgePacket (α) [BEq α] [Hashable α] where
  tc : TwoComplex α
  grading : ChiralGrading (tc.base.toGraph.nodes.size)
  dirac : Array (Array Rat)
  laplacian0 : Array (Array Rat)
  laplacian1 : Array (Array Rat)
  chiral : Array (Array Rat)
  chiralAnticommutes : Bool
  summary : HodgeSummary

/--
Canonical constructor for the finite graph-Hodge packet.

This is the bridge-normalized packet: the operator and readout fields are
filled from the owner definitions in `GraphHodge.lean`.
-/
def FiniteGraphHodgePacket.canonical
    {α : Type*} [BEq α] [Hashable α]
    (tc : TwoComplex α)
    (grading : ChiralGrading (tc.base.toGraph.nodes.size)) :
    FiniteGraphHodgePacket α where
  tc := tc
  grading := grading
  dirac := graphDirac tc
  laplacian0 := laplacian0 tc
  laplacian1 := laplacian1 tc
  chiral := extendedChiralGrading tc grading
  chiralAnticommutes := chiralAnticommutes tc grading
  summary := hodgeSummary tc

namespace FiniteGraphHodgePacket

variable {α : Type*} [BEq α] [Hashable α]

/-- The bundled Dirac matrix is the graph Dirac readout. -/
theorem dirac_eq_graphDirac (B : FiniteGraphHodgePacket α) :
    B.dirac = graphDirac B.tc := by
  rfl

/-- The bundled 0-Laplacian is the graph Hodge Laplacian readout. -/
theorem laplacian0_eq_graphLaplacian0 (B : FiniteGraphHodgePacket α) :
    B.laplacian0 = laplacian0 B.tc := by
  rfl

/-- The bundled 1-Laplacian is the graph Hodge Laplacian readout. -/
theorem laplacian1_eq_graphLaplacian1 (B : FiniteGraphHodgePacket α) :
    B.laplacian1 = laplacian1 B.tc := by
  rfl

/-- The bundled chiral grading matrix is the extended grading readout. -/
theorem chiral_eq_extendedChiralGrading (B : FiniteGraphHodgePacket α) :
    B.chiral = extendedChiralGrading B.tc B.grading := by
  rfl

/-- The summary packet is the Hodge summary of the carrier. -/
theorem summary_eq_hodgeSummary (B : FiniteGraphHodgePacket α) :
    B.summary = hodgeSummary B.tc := by
  rfl

end FiniteGraphHodgePacket

/--
Finite graph Hodge bridge target.

This is the canonical coercion point for the finite Hodge / Dirac / chiral
bundle in the DAG layer.
-/
def GraphHodgeBridgeTarget (α) [BEq α] [Hashable α] : Prop :=
  ∀ (B : FiniteGraphHodgePacket α),
    B.dirac = graphDirac B.tc ∧
    B.laplacian0 = laplacian0 B.tc ∧
    B.laplacian1 = laplacian1 B.tc ∧
    B.chiral = extendedChiralGrading B.tc B.grading ∧
    B.summary = hodgeSummary B.tc

/-- The finite graph Hodge bridge target is closed by definitional equality. -/
theorem graphHodgeBridgeTarget (α) [BEq α] [Hashable α] :
    GraphHodgeBridgeTarget α := by
  intro B
  exact
    ⟨FiniteGraphHodgePacket.dirac_eq_graphDirac B,
     FiniteGraphHodgePacket.laplacian0_eq_graphLaplacian0 B,
     FiniteGraphHodgePacket.laplacian1_eq_graphLaplacian1 B,
     FiniteGraphHodgePacket.chiral_eq_extendedChiralGrading B,
     FiniteGraphHodgePacket.summary_eq_hodgeSummary B⟩

end DAG
