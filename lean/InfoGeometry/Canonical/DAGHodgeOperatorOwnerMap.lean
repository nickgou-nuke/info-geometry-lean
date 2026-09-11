import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import DAG.GraphHodge
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Canonical.DAGHodgeOperatorOwnerMap

Lean-facing owner / translator / coherence map for the DAG Hodge, chiral,
and graph-Dirac toolchain.

This module does not reimplement the DAG operators.  It records, as typed
readouts and a small owner map, that the concrete graph-operator layer is
owned by `DAG.GraphHodge`, while the physical interpretation is supplied by
the `InfoGeometry` bridge layers.

Native DAG closure:
* `DAG.coboundary0`, `DAG.coboundary1`;
* `DAG.laplacian0`, `DAG.laplacian1`;
* `DAG.graphDirac`;
* `DAG.ChiralGrading`, `DAG.extendedChiralGrading`;
* `DAG.chiralAnticommutes`;
* `DAG.hodgeSummary`.

This file is an owner map and readout layer, not an analytic theorem.  It does not
assert Type-III/KMS completion, Hilbert--Pólya, zeta continuation, or RH.
-/

noncomputable section

namespace InfoGeometry.Canonical.DAGHodgeOperatorOwnerMap

/-- The operator-like objects supplied by the DAG Hodge toolchain. -/
@[rep_depth operator]
inductive DAGHodgeOperatorKind where
  | coboundary0
  | coboundary1
  | laplacian0
  | laplacian1
  | graphDirac
  | chiralGrading
  | extendedChiralGrading
  | chiralAnticommutationCheck
  | hodgeSummary
deriving DecidableEq, Repr

/--
Status of a layer in the owner map.

`nativeDAGClosure` means the concrete operator definition is already present
in `lean/DAG`.  `canonicalBridge` means the interpretation lives in an
`InfoGeometry.Canonical` bridge.
-/
@[rep_depth operator]
inductive OperatorOwnerStatus where
  | nativeDAGClosure
  | kreinOwner
  | canonicalBridge
  | finiteExteriorOwner
  | notClaimed
deriving DecidableEq, Repr

/-- One entry of the DAG-to-InfoGeometry owner map. -/
@[rep_depth operator]
structure DAGHodgeOperatorOwner where
  kind : DAGHodgeOperatorKind
  dagDefinition : String
  dagFile : String
  interpretationOwner : String
  status : OperatorOwnerStatus
deriving Repr

/-- Concrete DAG file that owns the graph-Hodge operator definitions. -/
@[rep_depth operator]
def dagGraphHodgeFile : String :=
  "lean/DAG/GraphHodge.lean"

/-- InfoGeometry file owning doubled/Krein chirality readouts. -/
@[rep_depth operator]
def kreinChiralityOwnerFile : String :=
  "lean/InfoGeometry/Krein/Prelude.lean"

/-- Canonical bridge file for incidence/Hodge/Dirac readouts. -/
@[rep_depth operator]
def realIncidenceHomologyBridgeFile : String :=
  "lean/InfoGeometry/Canonical/RealIncidenceHomologyBridge.lean"

/-- Canonical bridge file for chiral Dirac/homology readouts. -/
@[rep_depth operator]
def chiralDiracHomologyBridgeFile : String :=
  "lean/InfoGeometry/Canonical/ChiralDiracHomologyBridge.lean"

/-- Finite exterior/Fock graph-Hodge owner. -/
@[rep_depth operator]
def finiteExteriorGraphDiracOwnerFile : String :=
  "lean/InfoGeometry/Arithmetic/PrimeExteriorGraphDirac.lean"

/-- `δ₀ = ∂₁ᵀ` owner entry. -/
@[rep_depth operator]
def coboundary0Owner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.coboundary0
    dagDefinition := "DAG.coboundary0"
    dagFile := dagGraphHodgeFile
    interpretationOwner := "DAG.GraphHodge native coboundary readout"
    status := OperatorOwnerStatus.nativeDAGClosure }

/-- `δ₁ = ∂₂ᵀ` owner entry. -/
@[rep_depth operator]
def coboundary1Owner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.coboundary1
    dagDefinition := "DAG.coboundary1"
    dagFile := dagGraphHodgeFile
    interpretationOwner := "DAG.GraphHodge native coboundary readout"
    status := OperatorOwnerStatus.nativeDAGClosure }

/-- `Δ₀ = ∂₁ᵀ∂₁` owner entry. -/
@[rep_depth operator]
def laplacian0Owner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.laplacian0
    dagDefinition := "DAG.laplacian0"
    dagFile := dagGraphHodgeFile
    interpretationOwner := "DAG.GraphHodge native 0-chain Laplacian"
    status := OperatorOwnerStatus.nativeDAGClosure }

/-- `Δ₁ = ∂₁∂₁ᵀ + ∂₂ᵀ∂₂` owner entry. -/
@[rep_depth operator]
def laplacian1Owner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.laplacian1
    dagDefinition := "DAG.laplacian1"
    dagFile := dagGraphHodgeFile
    interpretationOwner := "DAG.GraphHodge native 1-chain Hodge Laplacian"
    status := OperatorOwnerStatus.nativeDAGClosure }

/-- Graph Dirac owner entry. -/
@[rep_depth operator]
def graphDiracOwner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.graphDirac
    dagDefinition := "DAG.graphDirac"
    dagFile := dagGraphHodgeFile
    interpretationOwner := "Canonical chiral/Hodge/Dirac bridges interpret this matrix"
    status := OperatorOwnerStatus.nativeDAGClosure }

/-- Chiral grading owner entry. -/
@[rep_depth operator]
def chiralGradingOwner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.chiralGrading
    dagDefinition := "DAG.ChiralGrading"
    dagFile := dagGraphHodgeFile
    interpretationOwner := kreinChiralityOwnerFile
    status := OperatorOwnerStatus.kreinOwner }

/-- Extended chiral grading owner entry. -/
@[rep_depth operator]
def extendedChiralGradingOwner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.extendedChiralGrading
    dagDefinition := "DAG.extendedChiralGrading"
    dagFile := dagGraphHodgeFile
    interpretationOwner := chiralDiracHomologyBridgeFile
    status := OperatorOwnerStatus.canonicalBridge }

/-- Chiral anticommutation check owner entry. -/
@[rep_depth operator]
def chiralAnticommutationOwner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.chiralAnticommutationCheck
    dagDefinition := "DAG.chiralAnticommutes"
    dagFile := dagGraphHodgeFile
    interpretationOwner := "checks ΓD + DΓ = 0 at DAG matrix level"
    status := OperatorOwnerStatus.nativeDAGClosure }

/-- Hodge summary owner entry. -/
@[rep_depth operator]
def hodgeSummaryOwner : DAGHodgeOperatorOwner :=
  { kind := DAGHodgeOperatorKind.hodgeSummary
    dagDefinition := "DAG.hodgeSummary"
    dagFile := dagGraphHodgeFile
    interpretationOwner := "DAG native invariant summary; canonical files may consume readouts"
    status := OperatorOwnerStatus.nativeDAGClosure }

/-- Compact owner map. -/
@[rep_depth operator]
def dagHodgeOperatorOwnerMap : List DAGHodgeOperatorOwner :=
  [ coboundary0Owner
  , coboundary1Owner
  , laplacian0Owner
  , laplacian1Owner
  , graphDiracOwner
  , chiralGradingOwner
  , extendedChiralGradingOwner
  , chiralAnticommutationOwner
  , hodgeSummaryOwner
  ]

/-! ## Typed readouts of the DAG implementation -/

section DAGReadouts

variable {α : Type*} [BEq α] [Hashable α]

/-- Readout of the DAG coboundary `δ₀ = ∂₁ᵀ`. -/
@[rep_depth operator]
def dagCoboundary0 (tc : DAG.TwoComplex α) : Array (Array Rat) :=
  DAG.coboundary0 tc

@[rep_depth operator]
theorem dagCoboundary0_eq (tc : DAG.TwoComplex α) :
    dagCoboundary0 tc = DAG.coboundary0 tc := rfl

/-- Readout of the DAG coboundary `δ₁ = ∂₂ᵀ`. -/
@[rep_depth operator]
def dagCoboundary1 (tc : DAG.TwoComplex α) : Array (Array Rat) :=
  DAG.coboundary1 tc

@[rep_depth operator]
theorem dagCoboundary1_eq (tc : DAG.TwoComplex α) :
    dagCoboundary1 tc = DAG.coboundary1 tc := rfl

/-- Readout of the graph Laplacian on 0-chains. -/
@[rep_depth operator]
def dagLaplacian0 (tc : DAG.TwoComplex α) : Array (Array Rat) :=
  DAG.laplacian0 tc

@[rep_depth operator]
theorem dagLaplacian0_eq (tc : DAG.TwoComplex α) :
    dagLaplacian0 tc = DAG.laplacian0 tc := rfl

/-- Readout of the Hodge Laplacian on 1-chains. -/
@[rep_depth operator]
def dagLaplacian1 (tc : DAG.TwoComplex α) : Array (Array Rat) :=
  DAG.laplacian1 tc

@[rep_depth operator]
theorem dagLaplacian1_eq (tc : DAG.TwoComplex α) :
    dagLaplacian1 tc = DAG.laplacian1 tc := rfl

/-- Readout of the graph Dirac matrix on `C⁰ ⊕ C¹`. -/
@[rep_depth operator]
def dagGraphDirac (tc : DAG.TwoComplex α) : Array (Array Rat) :=
  DAG.graphDirac tc

@[rep_depth operator]
theorem dagGraphDirac_eq (tc : DAG.TwoComplex α) :
    dagGraphDirac tc = DAG.graphDirac tc := rfl

/-- Readout of the extended chiral grading matrix. -/
@[rep_depth operator]
def dagExtendedChiralGrading
    (tc : DAG.TwoComplex α)
    (γ : DAG.ChiralGrading tc.base.toGraph.nodes.size) :
    Array (Array Rat) :=
  DAG.extendedChiralGrading tc γ

@[rep_depth operator]
theorem dagExtendedChiralGrading_eq
    (tc : DAG.TwoComplex α)
    (γ : DAG.ChiralGrading tc.base.toGraph.nodes.size) :
    dagExtendedChiralGrading tc γ = DAG.extendedChiralGrading tc γ := rfl

/-- Readout of the Boolean chiral anticommutation check `ΓD + DΓ = 0`. -/
@[rep_depth operator]
def dagChiralAnticommutes
    (tc : DAG.TwoComplex α)
    (γ : DAG.ChiralGrading tc.base.toGraph.nodes.size) : Bool :=
  DAG.chiralAnticommutes tc γ

@[rep_depth operator]
theorem dagChiralAnticommutes_eq
    (tc : DAG.TwoComplex α)
    (γ : DAG.ChiralGrading tc.base.toGraph.nodes.size) :
    dagChiralAnticommutes tc γ = DAG.chiralAnticommutes tc γ := rfl

/-- Readout of the compact Hodge summary. -/
@[rep_depth operator]
def dagHodgeSummary (tc : DAG.TwoComplex α) : DAG.HodgeSummary :=
  DAG.hodgeSummary tc

@[rep_depth operator]
theorem dagHodgeSummary_eq (tc : DAG.TwoComplex α) :
    dagHodgeSummary tc = DAG.hodgeSummary tc := rfl

/-- Direct readout: the DAG Hodge summary records the node count of the finite complex. -/
@[rep_depth operator]
theorem dagHodgeSummary_nodes (tc : DAG.TwoComplex α) :
    (dagHodgeSummary tc).nodes = tc.base.toGraph.nodes.size := rfl

/-- Direct readout: the DAG Hodge summary records the edge count of the finite complex. -/
@[rep_depth operator]
theorem dagHodgeSummary_edges (tc : DAG.TwoComplex α) :
    (dagHodgeSummary tc).edges = tc.edges.size := rfl

/-- Direct readout: the graph-Dirac matrix dimension is `#vertices + #edges`. -/
@[rep_depth operator]
theorem dagHodgeSummary_diracDim (tc : DAG.TwoComplex α) :
    (dagHodgeSummary tc).diracDim =
      tc.base.toGraph.nodes.size + tc.edges.size := rfl

end DAGReadouts

end InfoGeometry.Canonical.DAGHodgeOperatorOwnerMap
