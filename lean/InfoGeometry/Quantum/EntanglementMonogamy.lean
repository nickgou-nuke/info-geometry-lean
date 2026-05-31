/-
InfoGeometry/Quantum/EntanglementMonogamy.lean

Finite entanglement, monogamy, ER-incidence, and complexity interfaces.

This module does not claim ER=EPR as a theorem of quantum gravity. It records
the logical layer exposed by the Susskind/AMPS discussion:

  entanglement readouts
  monogamy obstruction
  nontraversable ER bridge bookkeeping
  post-thermalization complexity monotonicity

The theorem payload is deliberately modest:

  MaxEntangled B A -> MaxEntangled B R -> Independent A R -> False

and an ER-style identification can evade that contradiction only by proving
`¬ Independent A R`.
-/

import Mathlib
import InfoGeometry.Geometry.EntanglementGeometry
import InfoGeometry.Meta.OwnerTarget

noncomputable section

namespace InfoGeometry.Quantum.EntanglementMonogamy

/-! ## 1. Bipartite observable readouts -/

/--
A bipartite quantum system, kept abstract at the carrier level.
-/
structure BipartiteQuantumSystem where
  Left : Type*
  Right : Type*
  State : Type*

/--
Observable readouts for a bipartite system.

The correlation field is the first non-vacuous hook: entanglement claims can be
tied to joint readouts rather than stored only as prose.
-/
structure BipartiteReadout
    (Q : BipartiteQuantumSystem) where
  ObsL : Type*
  ObsR : Type*
  outcomeL : Q.State → ObsL → ℝ
  outcomeR : Q.State → ObsR → ℝ
  correlation : Q.State → ObsL → ObsR → ℝ

/--
A correlation-calibrated entanglement datum.

`MaxEntangled` remains model-specific, but it is attached to a readout and a
state, not floated as a global slogan.
-/
structure EntanglementDatum
    (Q : BipartiteQuantumSystem)
    (R : BipartiteReadout Q) where
  state : Q.State
  MaxEntangled : Q.State → Prop
  max_entangled : MaxEntangled state
  correlation_calibration : Prop
  correlation_sorryProof : correlation_calibration

namespace EntanglementDatum

variable {Q : BipartiteQuantumSystem}
variable {R : BipartiteReadout Q}
variable (E : EntanglementDatum Q R)

/-- The stored state is certified maximally entangled for the chosen readout. -/
theorem state_maxEntangled :
    E.MaxEntangled E.state :=
  E.max_entangled

end EntanglementDatum

/-! ## 1A. Explicit observable correlation witnesses -/

/--
An explicit observable correlation witness.

This does not define all of finite-dimensional entanglement theory. It does
remove the weakest shadow: a claimed entanglement datum can expose concrete
left/right observables, their marginal readouts, and their joint correlation
readout.
-/
structure ObservableCorrelationWitness
    (Q : BipartiteQuantumSystem)
    (R : BipartiteReadout Q)
    (state : Q.State) where
  /-- Left observable used in the witness. -/
  leftObs : R.ObsL

  /-- Right observable used in the witness. -/
  rightObs : R.ObsR

  /-- Certified left marginal value. -/
  leftValue : ℝ

  /-- Certified right marginal value. -/
  rightValue : ℝ

  /-- Certified joint correlation value. -/
  jointValue : ℝ

  /-- Left marginal readout law. -/
  outcomeL_eq :
    R.outcomeL state leftObs = leftValue

  /-- Right marginal readout law. -/
  outcomeR_eq :
    R.outcomeR state rightObs = rightValue

  /-- Joint correlation readout law. -/
  correlation_eq :
    R.correlation state leftObs rightObs = jointValue

namespace ObservableCorrelationWitness

variable {Q : BipartiteQuantumSystem}
variable {R : BipartiteReadout Q}
variable {state : Q.State}
variable (W : ObservableCorrelationWitness Q R state)

/-- The left marginal value is read from the chosen left observable. -/
theorem left_readout :
    R.outcomeL state W.leftObs = W.leftValue :=
  W.outcomeL_eq

/-- The right marginal value is read from the chosen right observable. -/
theorem right_readout :
    R.outcomeR state W.rightObs = W.rightValue :=
  W.outcomeR_eq

/-- The joint value is read from the chosen observable pair. -/
theorem joint_readout :
    R.correlation state W.leftObs W.rightObs = W.jointValue :=
  W.correlation_eq

end ObservableCorrelationWitness

/--
An entanglement datum with an explicit observable witness.

`MaxEntangled` remains model-specific, but the datum now carries a concrete
readout witness rather than only a detached calibration proposition.
-/
structure ReadoutEntanglementDatum
    (Q : BipartiteQuantumSystem)
    (R : BipartiteReadout Q) where
  /-- The state being certified. -/
  state : Q.State

  /-- Model-specific maximal-entanglement predicate. -/
  MaxEntangled : Q.State → Prop

  /-- Proof that the state satisfies the model-specific predicate. -/
  max_entangled : MaxEntangled state

  /-- Explicit finite observable-correlation witness for the state. -/
  witness : ObservableCorrelationWitness Q R state

namespace ReadoutEntanglementDatum

variable {Q : BipartiteQuantumSystem}
variable {R : BipartiteReadout Q}
variable (E : ReadoutEntanglementDatum Q R)

/-- The stored state is certified maximally entangled for the chosen readout. -/
theorem state_maxEntangled :
    E.MaxEntangled E.state :=
  E.max_entangled

/-- The stored witness exposes the certified joint correlation value. -/
theorem joint_correlation_readout :
    R.correlation E.state E.witness.leftObs E.witness.rightObs =
      E.witness.jointValue :=
  E.witness.correlation_eq

end ReadoutEntanglementDatum

/-! ## 2. Monogamy and AMPS tension -/

/--
Monogamy backend for maximal entanglement.

The key law says one system cannot be maximally entangled with two independent
partners at once.
-/
structure MonogamyBackend where
  System : Type*
  MaxEntangled : System → System → Prop
  Independent : System → System → Prop
  monogamy :
    ∀ A B C,
      MaxEntangled A B →
      MaxEntangled A C →
      Independent B C →
      False

namespace MonogamyBackend

variable (M : MonogamyBackend)

/--
AMPS-style tension:

`B` cannot be maximally entangled with both an interior mode `A` and an early
radiation/distant mode `R` when those partners are independent.
-/
theorem amps_tension
    {B A R : M.System}
    (h_smooth : M.MaxEntangled B A)
    (h_old : M.MaxEntangled B R)
    (h_independent : M.Independent A R) :
    False :=
  M.monogamy B A R h_smooth h_old h_independent

/--
If the two maximal-entanglement hypotheses hold, then independence of the two
partners is impossible.
-/
theorem not_independent_of_two_maxEntangled
    {B A R : M.System}
    (h_smooth : M.MaxEntangled B A)
    (h_old : M.MaxEntangled B R) :
    ¬ M.Independent A R := by
  intro h_independent
  exact M.amps_tension h_smooth h_old h_independent

end MonogamyBackend

/-! ## 3. ER bridge bookkeeping -/

/--
ER bridge datum.

This records the nontraversability constraint explicitly: bridge existence does
not imply exterior-to-exterior signaling.
-/
structure ERBridgeDatum where
  LeftExterior : Type*
  RightExterior : Type*
  Interior : Type*
  entangled_pair : Prop
  bridge_exists : Prop
  exterior_to_exterior_signal : Prop
  interior_meeting_possible : Prop
  bridge_of_entanglement :
    entangled_pair → bridge_exists
  nontraversable :
    bridge_exists → ¬ exterior_to_exterior_signal

namespace ERBridgeDatum

variable (E : ERBridgeDatum)

/-- Entanglement gives bridge existence in this supplied ER bookkeeping datum. -/
theorem bridge_exists_of_entangled
    (h : E.entangled_pair) :
    E.bridge_exists :=
  E.bridge_of_entanglement h

/-- An existing ER bridge is nontraversable for exterior-to-exterior signaling. -/
theorem no_exterior_signal_of_bridge
    (h : E.bridge_exists) :
    ¬ E.exterior_to_exterior_signal :=
  E.nontraversable h

/-- Entangled ER pairs do not permit exterior-to-exterior signaling. -/
theorem no_exterior_signal_of_entangled
    (h : E.entangled_pair) :
    ¬ E.exterior_to_exterior_signal :=
  E.nontraversable (E.bridge_of_entanglement h)

end ERBridgeDatum

/-! ## 4. ER/EPR evasion of AMPS independence -/

/--
ER/EPR identification data for a monogamy backend.

The point is not to prove the conjecture. The point is to represent the exact
logical escape hatch: the interior partner is not independent of the radiation
or distant system once an encoding/bridge identification is supplied.
-/
structure EREPRIdentification
    (M : MonogamyBackend) where
  InteriorMode : M.System
  RadiationMode : M.System
  Bridge : Prop
  EncodedTogether : M.System → M.System → Prop
  encoded_of_bridge :
    Bridge → EncodedTogether InteriorMode RadiationMode
  not_independent_of_encoded :
    EncodedTogether InteriorMode RadiationMode →
      ¬ M.Independent InteriorMode RadiationMode

namespace EREPRIdentification

variable {M : MonogamyBackend}
variable (E : EREPRIdentification M)

/--
An ER/EPR bridge identification refutes the independence hypothesis needed for
the AMPS monogamy contradiction.
-/
theorem evades_amps_independence
    (hBridge : E.Bridge) :
    ¬ M.Independent E.InteriorMode E.RadiationMode :=
  E.not_independent_of_encoded (E.encoded_of_bridge hBridge)

end EREPRIdentification

/--
Named ER/EPR escape-hatch theorem.

This is not a theorem proving ER=EPR. It says that once a concrete bridge
identification supplies an encoding of the interior with the radiation/distant
mode, the independence hypothesis required by the AMPS contradiction is no
longer available.
-/
theorem er_epr_evades_amps
    {M : MonogamyBackend}
    (E : EREPRIdentification M)
    (hBridge : E.Bridge) :
    ¬ M.Independent E.InteriorMode E.RadiationMode :=
  E.evades_amps_independence hBridge

/--
With the ER/EPR identification in hand, the AMPS contradiction cannot be formed
using the identified interior/radiation pair as independent partners.
-/
theorem no_amps_independence_after_er_identification
    {M : MonogamyBackend}
    (E : EREPRIdentification M)
    (hBridge : E.Bridge)
    {B : M.System}
    (_h_smooth : M.MaxEntangled B E.InteriorMode)
    (_h_old : M.MaxEntangled B E.RadiationMode) :
    ¬ M.Independent E.InteriorMode E.RadiationMode :=
  er_epr_evades_amps E hBridge

/-! ## 5. Complexity growth layer -/

/--
Complexity/bridge backend.

This captures the transcript's second layer: after thermalization, the relevant
interior-growth readout is complexity, not ordinary entropy saturation.
-/
structure ComplexityBridgeBackend
    (State : Type*) where
  complexity : State → ℝ
  entropy : State → ℝ
  bridgeLength : State → ℝ
  thermalizedAt : ℝ
  evolve : ℝ → State → State
  bridgeLength_eq_complexity :
    ∀ ψ t,
      bridgeLength (evolve t ψ) = complexity (evolve t ψ)
  entropy_saturated_after_thermalization :
    ∀ ψ s t,
      thermalizedAt ≤ s →
      s ≤ t →
      entropy (evolve s ψ) = entropy (evolve t ψ)
  complexity_grows_after_thermalization :
    ∀ ψ s t,
      thermalizedAt ≤ s →
      s ≤ t →
      complexity (evolve s ψ) ≤ complexity (evolve t ψ)

namespace ComplexityBridgeBackend

variable {State : Type*}
variable (C : ComplexityBridgeBackend State)

/-- Bridge length is read out as complexity in the supplied backend. -/
theorem bridgeLength_eq_complexity_at
    (ψ : State)
    (t : ℝ) :
    C.bridgeLength (C.evolve t ψ) =
      C.complexity (C.evolve t ψ) :=
  C.bridgeLength_eq_complexity ψ t

/-- Entropy is saturated after the thermalization time. -/
theorem entropy_saturated
    (ψ : State)
    {s t : ℝ}
    (hs : C.thermalizedAt ≤ s)
    (hst : s ≤ t) :
    C.entropy (C.evolve s ψ) = C.entropy (C.evolve t ψ) :=
  C.entropy_saturated_after_thermalization ψ s t hs hst

/-- Complexity is monotone after the thermalization time. -/
theorem complexity_monotone_after_thermalization
    (ψ : State)
    {s t : ℝ}
    (hs : C.thermalizedAt ≤ s)
    (hst : s ≤ t) :
    C.complexity (C.evolve s ψ) ≤ C.complexity (C.evolve t ψ) :=
  C.complexity_grows_after_thermalization ψ s t hs hst

/-- Bridge length is monotone after thermalization whenever it equals complexity. -/
theorem bridgeLength_monotone_after_thermalization
    (ψ : State)
    {s t : ℝ}
    (hs : C.thermalizedAt ≤ s)
    (hst : s ≤ t) :
    C.bridgeLength (C.evolve s ψ) ≤ C.bridgeLength (C.evolve t ψ) := by
  rw [C.bridgeLength_eq_complexity_at ψ s, C.bridgeLength_eq_complexity_at ψ t]
  exact C.complexity_monotone_after_thermalization ψ hs hst

end ComplexityBridgeBackend

/-! ## 6. Owner target -/

/--
Owner target for the finite entanglement/monogamy/complexity layer.
-/
@[owner_target_tag]
def EntanglementMonogamyOwnerTarget : Prop :=
  ∀ (System : Type)
    (MaxEntangled Independent : System → System → Prop),
    (∀ A B C,
      MaxEntangled A B →
      MaxEntangled A C →
      Independent B C →
      False) →
    ∀ B A R : System,
      MaxEntangled B A →
      MaxEntangled B R →
      Independent A R →
      False

/-- The AMPS-style monogamy obstruction is constructively discharged. -/
theorem entanglementMonogamyOwnerTarget :
    EntanglementMonogamyOwnerTarget := by
  intro System MaxEntangled Independent hmonogamy B A R hBA hBR hAR
  exact hmonogamy B A R hBA hBR hAR

end InfoGeometry.Quantum.EntanglementMonogamy
