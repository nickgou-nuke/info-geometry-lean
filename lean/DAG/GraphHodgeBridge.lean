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

namespace RealDoubledKreinGraphHodgePacket

/-- Canonical real doubled Hestenes--Krein lift of a finite graph-Hodge packet. -/
noncomputable def canonical
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (finite : FiniteGraphHodgePacket α) :
    RealDoubledKreinGraphHodgePacket E α :=
  { finite := finite }

/-! The operators are derived from the actual doubled-space owner, rather than
stored in the packet together with definitional equality proofs. -/

noncomputable def J
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (_P : RealDoubledKreinGraphHodgePacket E α) : RealDoubledKreinDAGEnd E :=
  modular_j (E := E)

noncomputable def ε
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (_P : RealDoubledKreinGraphHodgePacket E α) : RealDoubledKreinDAGEnd E :=
  spectral_epsilon (E := E)

noncomputable def K
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (_P : RealDoubledKreinGraphHodgePacket E α) : RealDoubledKreinDAGEnd E :=
  clockAxis (E := E)

theorem J_involution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (P : RealDoubledKreinGraphHodgePacket E α) :
    (P.J).comp P.J = ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E) :=
  modular_j_involution E

theorem epsilon_involution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (P : RealDoubledKreinGraphHodgePacket E α) :
    (P.ε).comp P.ε = ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E) :=
  spectral_epsilon_involution E

theorem J_epsilon_anticommute
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (P : RealDoubledKreinGraphHodgePacket E α) :
    (P.J).comp P.ε = -((P.ε).comp P.J) :=
  modular_j_spectral_epsilon_anticommute E

theorem K_square
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {α} [BEq α] [Hashable α]
    (P : RealDoubledKreinGraphHodgePacket E α) :
    (P.K).comp P.K = -(ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E)) :=
  clockAxis_sq E

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

/-- The Cuntz branch map preserves multiplication by isometry and range
orthogonality; this is the endomorphism law, not a definitional alias. -/
theorem canonicalEndomorphism_mul
    (P : RealDoubledKreinCuntzTransferPacket E α)
    (A B : RealDoubledKreinDAGEnd E) :
    canonicalEndomorphism P A * canonicalEndomorphism P B =
      canonicalEndomorphism P (A * B) := by
  have hleft := P.cuntz.left_isometry
  have hright := P.cuntz.right_isometry
  have hcross := P.cuntz.orthogonal_ranges
  have branch_mul {S : RealDoubledKreinDAGEnd E}
      (hS : star S * S = 1) (X Y : RealDoubledKreinDAGEnd E) :
      (S * X * star S) * (S * Y * star S) = S * (X * Y) * star S := by
    calc
      (S * X * star S) * (S * Y * star S) = S * X * (star S * S) * Y * star S := by
        noncomm_ring
      _ = S * X * 1 * Y * star S := by rw [hS]
      _ = S * (X * Y) * star S := by noncomm_ring
  have branch_cross {S T : RealDoubledKreinDAGEnd E}
      (hST : star S * T = 0) (X Y : RealDoubledKreinDAGEnd E) :
      (S * X * star S) * (T * Y * star T) = 0 := by
    calc
      (S * X * star S) * (T * Y * star T) = S * X * (star S * T) * Y * star T := by
        noncomm_ring
      _ = 0 := by rw [hST]; noncomm_ring
  have hLL := branch_mul hleft A B
  have hRR := branch_mul hright A B
  have hLR := branch_cross hcross.1 A B
  have hRL := branch_cross hcross.2 A B
  unfold canonicalEndomorphism
  calc
    (P.cuntz.S_left * A * star P.cuntz.S_left +
        P.cuntz.S_right * A * star P.cuntz.S_right) *
      (P.cuntz.S_left * B * star P.cuntz.S_left +
        P.cuntz.S_right * B * star P.cuntz.S_right)
        = (P.cuntz.S_left * A * star P.cuntz.S_left) *
              (P.cuntz.S_left * B * star P.cuntz.S_left) +
            (P.cuntz.S_left * A * star P.cuntz.S_left) *
              (P.cuntz.S_right * B * star P.cuntz.S_right) +
            (P.cuntz.S_right * A * star P.cuntz.S_right) *
              (P.cuntz.S_left * B * star P.cuntz.S_left) +
            (P.cuntz.S_right * A * star P.cuntz.S_right) *
              (P.cuntz.S_right * B * star P.cuntz.S_right) := by
          simp only [mul_add, add_mul, add_assoc]
          abel
    _ = P.cuntz.S_left * (A * B) * star P.cuntz.S_left +
          P.cuntz.S_right * (A * B) * star P.cuntz.S_right := by
      rw [hLL, hLR, hRL, hRR]
      simp
    _ = canonicalEndomorphism P (A * B) := rfl

/--
The discrete modular step used by this packet.

This is deliberately an alias for the Cuntz canonical endomorphism, not a
claim that every continuous modular flow has already been identified with it.
-/
noncomputable def discreteModularStep
    (P : RealDoubledKreinCuntzTransferPacket E α)
    (A : RealDoubledKreinDAGEnd E) : RealDoubledKreinDAGEnd E :=
  canonicalEndomorphism P A

/-- Multiplicativity of one discrete Cuntz modular step. -/
theorem discreteModularStep_mul
    (P : RealDoubledKreinCuntzTransferPacket E α)
    (A B : RealDoubledKreinDAGEnd E) :
    discreteModularStep P A * discreteModularStep P B =
      discreteModularStep P (A * B) := by
  simpa [discreteModularStep] using canonicalEndomorphism_mul P A B

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
    (P.graph.J).comp P.graph.J = ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E) ∧
      (P.graph.ε).comp P.graph.ε = ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E) ∧
      (P.graph.J).comp P.graph.ε = -((P.graph.ε).comp P.graph.J) ∧
      (P.graph.K).comp P.graph.K = -(ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E)) := by
  exact ⟨P.graph.J_involution, P.graph.epsilon_involution,
    P.graph.J_epsilon_anticommute, P.graph.K_square⟩

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
        (B.J).comp B.J = ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E) ∧
        (B.ε).comp B.ε = ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E) ∧
        (B.J).comp B.ε = -((B.ε).comp B.J) ∧
        (B.K).comp B.K = -(ContinuousLinearMap.id ℝ (RealDoubledKreinDAGCarrier E)) := by
  intro tc grading
  let finite := FiniteGraphHodgePacket.canonical tc grading
  let packet := RealDoubledKreinGraphHodgePacket.canonical (E := E) finite
  refine ⟨packet, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact packet.J_involution
  · exact packet.epsilon_involution
  · exact packet.J_epsilon_anticommute
  · exact packet.K_square

end DAG
