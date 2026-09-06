import DAG.GraphHodge
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Topology.CuntzCantorSpectralTriple

/-!
# DAG.GraphHodgeBridge

Canonical finite Hodge / Dirac / chiral bridge for the declaration DAG,
anchored on the real doubled Hestenes--Krein carrier.

This module does not introduce new operators. It packages the existing finite
graph-Hodge carrier from `GraphHodge.lean` into a single coherence layer:

* `TwoComplex` is the finite rational coordinate carrier;
* `graphDirac` is the bounded graph Dirac matrix;
* `laplacian0` and `laplacian1` are the finite Hodge Laplacians;
* `ChiralGrading` and `extendedChiralGrading` provide the grading data;
* `chiralAnticommutes` is the bounded chiral compatibility check;
* `HodgeSummary` is the readout/export packet.
* `RealDoubledKreinGraphHodgePacket` adds the actual Hestenes--Krein substrate:
  `DoubledSpace E` with `modular_j`, `spectral_epsilon`, and `clockAxis`.

The bridge is intentionally a packaging surface, not a new theorem owner.
-/

namespace DAG

open scoped InnerProductSpace
open InfoGeometry.Krein
open InfoGeometry.Topology

set_option linter.unusedVariables false

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

/-! ## Real doubled Hestenes--Krein carrier for the graph-Hodge packet -/

/-- The real doubled Hestenes--Krein carrier used by the declaration DAG. -/
abbrev RealDoubledKreinDAGCarrier
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  DoubledSpace E

/-- Endomorphism ring of the real doubled Hestenes--Krein DAG carrier. -/
abbrev RealDoubledKreinDAGEnd
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  RealDoubledKreinDAGCarrier E →L[ℝ] RealDoubledKreinDAGCarrier E

/--
Graph-Hodge packet over the real doubled Hestenes--Krein carrier.

The finite `TwoComplex`/matrix data remain in `finite`; the carrier fields
record the real doubled modular swap, fundamental symmetry, and clock axis
used by the Hestenes--Krein layer.
-/
structure RealDoubledKreinGraphHodgePacket
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α) [BEq α] [Hashable α] where
  finite : FiniteGraphHodgePacket α
  J : RealDoubledKreinDAGCarrier E →L[ℝ] RealDoubledKreinDAGCarrier E
  ε : RealDoubledKreinDAGCarrier E →L[ℝ] RealDoubledKreinDAGCarrier E
  K : RealDoubledKreinDAGCarrier E →L[ℝ] RealDoubledKreinDAGCarrier E
  J_eq : J = modular_j (E := E)
  epsilon_eq : ε = spectral_epsilon (E := E)
  K_eq : K = clockAxis (E := E)

namespace RealDoubledKreinGraphHodgePacket

/-- Canonical real doubled Hestenes--Krein lift of a finite graph-Hodge packet. -/
noncomputable def canonical
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (finite : FiniteGraphHodgePacket α) :
    RealDoubledKreinGraphHodgePacket E α :=
  { finite := finite
    J := modular_j (E := E)
    ε := spectral_epsilon (E := E)
    K := clockAxis (E := E)
    J_eq := rfl
    epsilon_eq := rfl
    K_eq := rfl }

@[simp]
theorem canonical_J
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (finite : FiniteGraphHodgePacket α) :
    (canonical (E := E) finite).J = modular_j (E := E) :=
  rfl

@[simp]
theorem canonical_epsilon
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (finite : FiniteGraphHodgePacket α) :
    (canonical (E := E) finite).ε = spectral_epsilon (E := E) :=
  rfl

@[simp]
theorem canonical_clockAxis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (finite : FiniteGraphHodgePacket α) :
    (canonical (E := E) finite).K = clockAxis (E := E) :=
  rfl

end RealDoubledKreinGraphHodgePacket

/-! ## Cuntz transfer on the real doubled Hestenes--Krein DAG carrier -/

/--
Real doubled Hestenes--Krein Cuntz transfer packet.

The Cuntz data live in the endomorphism ring of `DoubledSpace E`.  The state
laws are explicit: this packet proves fixed-point behavior only for states
whose left and right branch readouts each contribute one half.
-/
structure RealDoubledKreinCuntzTransferPacket
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α) [BEq α] [Hashable α] where
  graph : RealDoubledKreinGraphHodgePacket E α
  cuntz : CuntzO2Carrier (RealDoubledKreinDAGEnd E)
  state : RealDoubledKreinDAGEnd E → ℝ
  state_add : ∀ A B, state (A + B) = state A + state B
  state_left_half :
    ∀ A, state (cuntz.S_left * A * star cuntz.S_left) = (1 / 2 : ℝ) * state A
  state_right_half :
    ∀ A, state (cuntz.S_right * A * star cuntz.S_right) = (1 / 2 : ℝ) * state A

namespace RealDoubledKreinCuntzTransferPacket

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]

/-- The Cuntz canonical endomorphism on the real doubled Krein operator ring. -/
noncomputable def canonicalEndomorphism
    (P : RealDoubledKreinCuntzTransferPacket E α)
    (A : RealDoubledKreinDAGEnd E) : RealDoubledKreinDAGEnd E :=
  P.cuntz.S_left * A * star P.cuntz.S_left +
    P.cuntz.S_right * A * star P.cuntz.S_right

/--
The discrete modular step used by this packet.

This is deliberately an alias for the Cuntz canonical endomorphism, not a
claim that every continuous modular flow has already been identified with it.
-/
noncomputable def discreteModularStep
    (P : RealDoubledKreinCuntzTransferPacket E α)
    (A : RealDoubledKreinDAGEnd E) : RealDoubledKreinDAGEnd E :=
  canonicalEndomorphism P A

@[simp]
theorem discreteModularStep_eq_canonicalEndomorphism
    (P : RealDoubledKreinCuntzTransferPacket E α)
    (A : RealDoubledKreinDAGEnd E) :
    discreteModularStep P A = canonicalEndomorphism P A :=
  rfl

/-- The Cuntz transfer is unital by the `O₂` range-sum relation. -/
theorem canonicalEndomorphism_one
    (P : RealDoubledKreinCuntzTransferPacket E α) :
    canonicalEndomorphism P 1 = 1 := by
  simpa [canonicalEndomorphism] using P.cuntz.range_sum

/-- The packet's discrete modular step is unital. -/
theorem discreteModularStep_one
    (P : RealDoubledKreinCuntzTransferPacket E α) :
    discreteModularStep P 1 = 1 := by
  simpa [discreteModularStep] using canonicalEndomorphism_one P

/--
KMS fixed-point law for the Cuntz transfer.

If each branch readout contributes exactly one half, the state is fixed by the
Cuntz canonical endomorphism.
-/
theorem state_fixed_by_canonicalEndomorphism
    (P : RealDoubledKreinCuntzTransferPacket E α)
    (A : RealDoubledKreinDAGEnd E) :
    P.state (canonicalEndomorphism P A) = P.state A := by
  rw [canonicalEndomorphism, P.state_add, P.state_left_half, P.state_right_half]
  ring

/-- Fixed-point law for the packet's discrete modular step. -/
theorem state_fixed_by_discreteModularStep
    (P : RealDoubledKreinCuntzTransferPacket E α)
    (A : RealDoubledKreinDAGEnd E) :
    P.state (discreteModularStep P A) = P.state A := by
  simpa [discreteModularStep] using state_fixed_by_canonicalEndomorphism P A

/-- The Cuntz transfer packet is anchored on the real doubled Krein graph carrier. -/
theorem graph_carrier_is_real_doubled
    (P : RealDoubledKreinCuntzTransferPacket E α) :
    P.graph.J = modular_j (E := E) ∧
      P.graph.ε = spectral_epsilon (E := E) ∧
      P.graph.K = clockAxis (E := E) := by
  exact ⟨P.graph.J_eq, P.graph.epsilon_eq, P.graph.K_eq⟩

end RealDoubledKreinCuntzTransferPacket

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

/--
The graph-Hodge bridge lifts canonically to the real doubled
Hestenes--Krein carrier.
-/
theorem realDoubledKreinGraphHodgeBridgeTarget
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (α) [BEq α] [Hashable α] :
    ∀ (tc : TwoComplex α)
      (grading : ChiralGrading (tc.base.toGraph.nodes.size)),
      ∃ B : RealDoubledKreinGraphHodgePacket E α,
        B.finite.tc = tc ∧
        B.finite.dirac = graphDirac tc ∧
        B.J = modular_j (E := E) ∧
        B.ε = spectral_epsilon (E := E) ∧
        B.K = clockAxis (E := E) := by
  intro tc grading
  let finite := FiniteGraphHodgePacket.canonical tc grading
  refine ⟨RealDoubledKreinGraphHodgePacket.canonical (E := E) finite, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

end DAG
