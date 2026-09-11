/-
InfoGeometry/Geometry/EntanglementGeometry.lean

Finite ER-incidence, monogamous pairing, and constructive witness complexity.

This module treats ER-style incidence as finite relation data rather than as a
metric spacetime theorem. It also treats circuit complexity as the length of a
supplied circuit witness, not as a proof of minimal circuit complexity.
-/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Geometry.EntanglementGeometry

/-! ## 1. Monogamous maximal entanglement -/

/--
A monogamous maximal-entanglement pairing.

`partner a = some b` means that `a` is maximally bipartite-entangled with `b`.

This is the finite constructive replacement for the informal statement:

"if `a` is maximally entangled with `b`, then it cannot also be maximally
entangled with a distinct `c`."
-/
structure MonogamousPairing
    (Node : Type*) where
  /-- Optional entanglement partner. -/
  partner : Node → Option Node

  /-- Pairing is symmetric. -/
  symmetric :
    ∀ {a b : Node},
      partner a = some b →
        partner b = some a

  /-- No node is paired with itself. -/
  no_self :
    ∀ {a b : Node},
      partner a = some b →
        b ≠ a

namespace MonogamousPairing

variable {Node : Type*}
variable (P : MonogamousPairing Node)

/--
`a` is paired with `b`.
-/
def IsPaired
    (a b : Node) : Prop :=
  P.partner a = some b

/--
Pairing is symmetric.
-/
theorem paired_symm
    {a b : Node}
    (h : P.IsPaired a b) :
    P.IsPaired b a :=
  P.symmetric h

/--
A node has at most one maximal entanglement partner.
-/
theorem partner_unique
    {a b c : Node}
    (hab : P.IsPaired a b)
    (hac : P.IsPaired a c) :
    b = c := by
  dsimp [IsPaired] at hab hac
  rw [hab] at hac
  exact Option.some.inj hac

/--
A paired node is not paired with itself.
-/
theorem paired_ne_self
    {a b : Node}
    (h : P.IsPaired a b) :
    b ≠ a :=
  P.no_self h

/--
No self-pairing.
-/
theorem not_paired_self
    (a : Node) :
    ¬ P.IsPaired a a := by
  intro h
  exact P.no_self h rfl

/--
If `a` is paired with `b`, then `a` is not paired with any distinct `c`.
-/
theorem no_second_partner
    {a b c : Node}
    (hab : P.IsPaired a b)
    (hbc : b ≠ c) :
    ¬ P.IsPaired a c := by
  intro hac
  exact hbc (P.partner_unique hab hac)

/--
If `a` appears paired with two partners, those partners are equal.

This is the formal AMPS monogamy obstruction.
-/
theorem two_partners_force_equal
    {a b c : Node}
    (hab : P.IsPaired a b)
    (hac : P.IsPaired a c) :
    b = c :=
  P.partner_unique hab hac

end MonogamousPairing

/-! ## 2. ER bridge readout -/

namespace MonogamousPairing

variable {Node : Type*}
variable (P : MonogamousPairing Node)

/--
In this finite readout layer, an Einstein-Rosen bridge is exactly a
monogamous entanglement pairing.
-/
def HasERBridge
    (a b : Node) : Prop :=
  P.IsPaired a b

/--
ER bridges are symmetric.
-/
theorem erBridge_symm
    {a b : Node}
    (h : P.HasERBridge a b) :
    P.HasERBridge b a :=
  P.paired_symm h

/--
A node cannot have two distinct ER bridge partners.
-/
theorem erBridge_unique
    {a b c : Node}
    (hab : P.HasERBridge a b)
    (hac : P.HasERBridge a c) :
    b = c :=
  P.partner_unique hab hac

end MonogamousPairing

/-! ## 3. AMPS-style obstruction and ER identification -/

/--
AMPS-style double-pairing datum.

`exterior` is the near-horizon exterior mode `B`.

`interior` is the putative smooth-horizon partner `A`.

`distant` is the distant purifier `B'`.

The data records the two attempted maximal pairings:

* `B ↔ A`
* `B ↔ B'`

Monogamy then forces `A = B'`. This is not assumed.
-/
structure AMPSDoublePairing
    (Node : Type*) where
  /-- Monogamous pairing data. -/
  pairing : MonogamousPairing Node

  /-- Near-horizon exterior mode. -/
  exterior : Node

  /-- Putative interior partner. -/
  interior : Node

  /-- Distant purifier. -/
  distant : Node

  /-- Smooth-horizon pairing: exterior mode with interior mode. -/
  exterior_interior :
    pairing.HasERBridge exterior interior

  /-- The exterior mode is paired with the distant purifier. -/
  exterior_distant :
    pairing.HasERBridge exterior distant

namespace AMPSDoublePairing

variable {Node : Type*}
variable (A : AMPSDoublePairing Node)

/--
The AMPS double-pairing datum forces the interior mode and the distant purifier
to be the same effective readout.
-/
theorem interior_eq_distant :
    A.interior = A.distant :=
  A.pairing.erBridge_unique
    A.exterior_interior
    A.exterior_distant

/--
There is no monogamy violation: the two apparent partners collapse to one.
-/
theorem no_monogamy_violation :
    A.interior = A.distant :=
  A.interior_eq_distant

/--
If the interior mode and distant purifier are asserted to be distinct, the
AMPS double-pairing datum is impossible.
-/
theorem impossible_of_distinct
    (h : A.interior ≠ A.distant) :
    False :=
  h A.interior_eq_distant

/--
The exterior cannot have both partners if the two partners are distinct.
-/
theorem no_double_pairing_of_distinct_partners
    (h : A.interior ≠ A.distant) :
    False :=
  A.impossible_of_distinct h

end AMPSDoublePairing

/--
Resolved AMPS readout.

This is obtained from `AMPSDoublePairing` after monogamy has forced
`interior = distant`.
-/
structure AMPSReadout
    (Node : Type*) where
  /-- Monogamous pairing data. -/
  pairing : MonogamousPairing Node

  /-- Near-horizon exterior mode. -/
  exterior : Node

  /-- Putative interior partner. -/
  interior : Node

  /-- Distant purifier. -/
  distant : Node

  /-- The exterior mode is paired with the distant purifier. -/
  exterior_distant :
    pairing.HasERBridge exterior distant

  /--
  Derived ER identification: the interior bit and distant purifier are the same
  effective information readout.
  -/
  interior_identification :
    interior = distant

namespace AMPSDoublePairing

variable {Node : Type*}
variable (A : AMPSDoublePairing Node)

/--
Convert a double-pairing datum into a resolved AMPS readout by deriving the
interior/distant identification from monogamy.
-/
def toResolvedReadout :
    AMPSReadout Node where
  pairing := A.pairing
  exterior := A.exterior
  interior := A.interior
  distant := A.distant
  exterior_distant := A.exterior_distant
  interior_identification := A.interior_eq_distant

end AMPSDoublePairing

namespace AMPSReadout

variable {Node : Type*}
variable (A : AMPSReadout Node)

/--
The exterior mode is also paired with the interior mode because the interior
mode is identified with the distant purifier.
-/
theorem exterior_interior_bridge :
    A.pairing.HasERBridge A.exterior A.interior := by
  dsimp [MonogamousPairing.HasERBridge, MonogamousPairing.IsPaired]
  rw [A.interior_identification]
  exact A.exterior_distant

/--
There is no monogamy violation: the two apparent partners are equal.
-/
theorem no_monogamy_violation :
    A.interior = A.distant :=
  A.interior_identification

end AMPSReadout

/--
Without ER identification, two simultaneous maximal partners force equality.

So if `interior ≠ distant`, the data

`exterior ↔ interior`

and

`exterior ↔ distant`

cannot both hold.
-/
theorem AMPS_two_partner_obstruction
    {Node : Type*}
    (P : MonogamousPairing Node)
    {exterior interior distant : Node}
    (hEI : P.HasERBridge exterior interior)
    (hED : P.HasERBridge exterior distant) :
    interior = distant :=
  P.erBridge_unique hEI hED

/--
Contrapositive obstruction: if the interior bit and distant purifier are
distinct, then the exterior mode cannot be paired with both.
-/
theorem AMPS_no_double_pairing_of_distinct_partners
    {Node : Type*}
    (P : MonogamousPairing Node)
    {exterior interior distant : Node}
    (hdistinct : interior ≠ distant)
    (hED : P.HasERBridge exterior distant) :
    ¬ P.HasERBridge exterior interior := by
  intro hEI
  exact hdistinct (P.erBridge_unique hEI hED)

/-! ## 4. Nontraversable ER causal incidence -/

/--
The two exterior sides of a two-sided ER bridge.
-/
inductive Side where
  | left
  | right
deriving DecidableEq, Repr

namespace Side

/--
Opposite side.
-/
def opposite : Side → Side
  | left => right
  | right => left

@[simp]
theorem opposite_left :
    opposite left = right :=
  rfl

@[simp]
theorem opposite_right :
    opposite right = left :=
  rfl

@[simp]
theorem opposite_opposite
    (s : Side) :
    opposite (opposite s) = s := by
  cases s <;> rfl

end Side

/--
Exterior/interior zones of a two-sided ER geometry.
-/
inductive ERZone where
  | exterior : Side → ERZone
  | interior : Side → ERZone
deriving DecidableEq, Repr

/--
Causal incidence through the ER bridge.

The model permits exterior-to-opposite-interior incidence, but not
exterior-to-exterior traversal.
-/
def ThroughER : ERZone → ERZone → Prop
  | ERZone.exterior s, ERZone.interior t => t = Side.opposite s
  | _, _ => False

/--
Left exterior can influence the right interior.
-/
theorem left_exterior_to_right_interior :
    ThroughER
      (ERZone.exterior Side.left)
      (ERZone.interior Side.right) := by
  simp [ThroughER]

/--
Right exterior can influence the left interior.
-/
theorem right_exterior_to_left_interior :
    ThroughER
      (ERZone.exterior Side.right)
      (ERZone.interior Side.left) := by
  simp [ThroughER]

/--
Exterior-to-interior ER incidence occurs exactly to the opposite side.
-/
theorem throughER_exterior_to_interior_iff
    (s t : Side) :
    ThroughER
      (ERZone.exterior s)
      (ERZone.interior t)
      ↔
    t = Side.opposite s := by
  cases s <;> cases t <;> simp [ThroughER, Side.opposite]

/--
No exterior mode reaches the same-side interior through the ER bridge.
-/
theorem no_same_side_exterior_to_interior
    (s : Side) :
    ¬ ThroughER
      (ERZone.exterior s)
      (ERZone.interior s) := by
  cases s <;> simp [ThroughER]

/--
No ER exterior-to-exterior traversal.
-/
theorem no_exterior_to_exterior
    (s t : Side) :
    ¬ ThroughER
      (ERZone.exterior s)
      (ERZone.exterior t) := by
  cases s <;> cases t <;> simp [ThroughER]

/--
No interior-to-exterior escape in this incidence model.
-/
theorem no_interior_to_exterior
    (s t : Side) :
    ¬ ThroughER
      (ERZone.interior s)
      (ERZone.exterior t) := by
  cases s <;> cases t <;> simp [ThroughER]

/-! ## 5. GHZ measurement incidence -/

/--
Three parties used for the finite GHZ incidence model.
-/
inductive TripleNode where
  | alice
  | bob
  | charlie
deriving DecidableEq, Fintype, Repr

/--
Finite incidence states:

* `bellAB`: Alice and Bob have a Bell-pair link.
* `ghzABC`: Charlie has measured Bob, producing a tripartite GHZ-type knot.

This is not a Hilbert-space formalization. It is the finite incidence layer
needed to process the lecture claim:

after the measurement, no pair is Bell-entangled, but the triple has a global
correlation knot.
-/
inductive EntanglementIncidence where
  | bellAB
  | ghzABC
deriving DecidableEq, Repr

open TripleNode
open EntanglementIncidence

/-
`PairEntangled` tracks Bell-pair incidence only.

In the `ghzABC` state, this finite incidence model says no pair remains
Bell-linked. It does not assert that all statistical pairwise correlations
vanish in every Hilbert-space readout.
-/

/--
Pairwise Bell-link readout.
-/
def PairEntangled :
    EntanglementIncidence → TripleNode → TripleNode → Prop
  | bellAB, x, y =>
      (x = alice ∧ y = bob) ∨ (x = bob ∧ y = alice)
  | _, _, _ => False

/--
Tripartite GHZ-knot readout.
-/
def GlobalKnot :
    EntanglementIncidence → Prop
  | inc => inc = ghzABC

/--
Charlie measures Bob.
-/
def measureBobWithCharlie
    (_ : EntanglementIncidence) :
    EntanglementIncidence :=
  ghzABC

/--
Before measurement, Alice and Bob have a Bell link.
-/
theorem bell_alice_bob :
    PairEntangled bellAB alice bob := by
  simp [PairEntangled]

/--
Before measurement, Bob and Alice have the symmetric Bell link.
-/
theorem bell_bob_alice :
    PairEntangled bellAB bob alice := by
  simp [PairEntangled]

/--
Charlie is not Bell-linked in the initial Bell-pair incidence.
-/
theorem bell_no_charlie_pair
    (x : TripleNode) :
    ¬ PairEntangled bellAB charlie x := by
  cases x <;> simp [PairEntangled]

/--
After Charlie's measurement, no pair remains Bell-entangled.
-/
theorem measurement_kills_pairwise_bell_links
    (s : EntanglementIncidence)
    (x y : TripleNode) :
    ¬ PairEntangled (measureBobWithCharlie s) x y := by
  cases x <;> cases y <;> simp [measureBobWithCharlie, PairEntangled]

/--
After Charlie's measurement, the tripartite GHZ knot exists.
-/
theorem measurement_creates_global_knot
    (s : EntanglementIncidence) :
    GlobalKnot (measureBobWithCharlie s) := by
  simp [measureBobWithCharlie, GlobalKnot]

/--
The GHZ incidence has global knot data but no pairwise Bell links.
-/
theorem ghz_global_without_pairwise
    (x y : TripleNode) :
    GlobalKnot ghzABC ∧ ¬ PairEntangled ghzABC x y := by
  constructor
  · simp [GlobalKnot]
  · cases x <;> cases y <;> simp [PairEntangled]

/-! ## 6. Quantum circuits as constructive complexity witnesses -/

/--
A two-qubit gate.

The gate content is abstract. The constructive complexity readout counts
explicit gates.
-/
structure TwoQubitGate
    (Qubit : Type*) where
  /-- First qubit touched by the gate. -/
  left : Qubit

  /-- Second qubit touched by the gate. -/
  right : Qubit

/--
A finite quantum circuit.
-/
abbrev QuantumCircuit
    (Qubit : Type*) :=
  List (TwoQubitGate Qubit)

namespace QuantumCircuit

variable {Qubit : Type*}

/-
This is constructive witness complexity: the length of the supplied circuit.

It is an upper-bound witness for usual minimal circuit complexity, not a proof
that no shorter circuit exists.
-/

/--
Constructive circuit complexity: the number of gates in the explicit circuit.
-/
def complexity
    (C : QuantumCircuit Qubit) : ℕ :=
  C.length

/--
The empty circuit has zero complexity.
-/
theorem complexity_nil :
    complexity ([] : QuantumCircuit Qubit) = 0 :=
  rfl

/--
Appending one gate increases constructive complexity by one.
-/
theorem complexity_append_gate
    (C : QuantumCircuit Qubit)
    (g : TwoQubitGate Qubit) :
    complexity (C ++ [g]) = complexity C + 1 := by
  simp [complexity]

/--
Complexity is additive under circuit concatenation.
-/
theorem complexity_append
    (C D : QuantumCircuit Qubit) :
    complexity (C ++ D) =
      complexity C + complexity D := by
  simp [complexity]

/--
A nonempty circuit has positive constructive complexity.
-/
theorem complexity_pos_of_ne_nil
    {C : QuantumCircuit Qubit}
    (hC : C ≠ []) :
    0 < complexity C := by
  cases C with
  | nil =>
      exact False.elim (hC rfl)
  | cons _ _ =>
      simp [complexity]

end QuantumCircuit

/-! ## 7. Circuit-generated bridge length -/

/--
A bridge slice generated by an explicit circuit.

The bridge length readout is not an independent hypothesis; it is defined to
be the constructive circuit complexity.
-/
structure CircuitBridgeSlice
    (Qubit : Type*) where
  /-- Explicit circuit generating the slice. -/
  circuit : QuantumCircuit Qubit

namespace CircuitBridgeSlice

variable {Qubit : Type*}

/--
Constructive bridge length readout.
-/
def bridgeLength
    (B : CircuitBridgeSlice Qubit) : ℕ :=
  QuantumCircuit.complexity B.circuit

/--
Grow the bridge by appending one gate.
-/
def grow
    (B : CircuitBridgeSlice Qubit)
    (g : TwoQubitGate Qubit) :
    CircuitBridgeSlice Qubit where
  circuit := B.circuit ++ [g]

/--
Appending one gate increases bridge length by one.
-/
theorem bridgeLength_grow
    (B : CircuitBridgeSlice Qubit)
    (g : TwoQubitGate Qubit) :
    (B.grow g).bridgeLength =
      B.bridgeLength + 1 := by
  simp [bridgeLength, grow, QuantumCircuit.complexity]

/--
Appending a whole circuit increases bridge length by the length of that
circuit.
-/
def growByCircuit
    (B : CircuitBridgeSlice Qubit)
    (C : QuantumCircuit Qubit) :
    CircuitBridgeSlice Qubit where
  circuit := B.circuit ++ C

/--
Bridge length is additive under circuit growth.
-/
theorem bridgeLength_growByCircuit
    (B : CircuitBridgeSlice Qubit)
    (C : QuantumCircuit Qubit) :
    (B.growByCircuit C).bridgeLength =
      B.bridgeLength + QuantumCircuit.complexity C := by
  simp [bridgeLength, growByCircuit, QuantumCircuit.complexity]

end CircuitBridgeSlice

/-! ## 8. Constructive circuit trajectories -/

/--
The circuit obtained after appending the first `t` gates from a gate stream.
-/
def circuitFromGateStream
    {Qubit : Type*}
    (gates : ℕ → TwoQubitGate Qubit) :
    ℕ → QuantumCircuit Qubit
  | 0 => []
  | Nat.succ t => circuitFromGateStream gates t ++ [gates t]

namespace circuitFromGateStream

variable {Qubit : Type*}
variable (gates : ℕ → TwoQubitGate Qubit)

/--
The circuit at time zero is empty.
-/
theorem zero :
    circuitFromGateStream gates 0 = [] :=
  rfl

/--
The successor circuit is obtained by appending exactly one gate.
-/
theorem succ
    (t : ℕ) :
    circuitFromGateStream gates (Nat.succ t) =
      circuitFromGateStream gates t ++ [gates t] :=
  rfl

/--
The constructive complexity of the circuit at time `t` is exactly `t`.
-/
theorem complexity_eq_time
    (t : ℕ) :
    QuantumCircuit.complexity
      (circuitFromGateStream gates t) = t := by
  induction t with
  | zero =>
      simp [circuitFromGateStream, QuantumCircuit.complexity]
  | succ t ih =>
      calc
        QuantumCircuit.complexity
            (circuitFromGateStream gates (Nat.succ t))
            =
            QuantumCircuit.complexity
              (circuitFromGateStream gates t ++ [gates t]) := by
              rfl
        _ = QuantumCircuit.complexity
              (circuitFromGateStream gates t) + 1 := by
              exact QuantumCircuit.complexity_append_gate
                (circuitFromGateStream gates t)
                (gates t)
        _ = t + 1 := by
              rw [ih]

end circuitFromGateStream

/--
A canonical growing circuit trajectory generated by a gate stream.

No evolution law is stored. The evolution is definitional.
-/
structure CanonicalGrowingCircuitTrajectory
    (Qubit : Type*) where
  /-- Gate appended at each discrete time. -/
  stepGate : ℕ → TwoQubitGate Qubit

namespace CanonicalGrowingCircuitTrajectory

variable {Qubit : Type*}
variable (T : CanonicalGrowingCircuitTrajectory Qubit)

/--
Circuit at time `t`.
-/
def circuitAt
    (t : ℕ) :
    QuantumCircuit Qubit :=
  circuitFromGateStream T.stepGate t

/--
Constructive complexity at time `t`.
-/
def complexityAt
    (t : ℕ) : ℕ :=
  QuantumCircuit.complexity (T.circuitAt t)

/--
Bridge length at time `t`.

This is defined as the constructive circuit complexity.
-/
def bridgeLengthAt
    (t : ℕ) : ℕ :=
  T.complexityAt t

/--
The circuit successor law is definitional.
-/
theorem circuitAt_succ
    (t : ℕ) :
    T.circuitAt (Nat.succ t) =
      T.circuitAt t ++ [T.stepGate t] :=
  rfl

/--
Complexity at time `t` is exactly `t`.
-/
theorem complexityAt_eq_time
    (t : ℕ) :
    T.complexityAt t = t := by
  simp [
    complexityAt,
    circuitAt,
    circuitFromGateStream.complexity_eq_time
  ]

/--
Bridge length at time `t` is exactly `t`.
-/
theorem bridgeLengthAt_eq_time
    (t : ℕ) :
    T.bridgeLengthAt t = t := by
  simp [
    bridgeLengthAt,
    complexityAt_eq_time
  ]

/--
Complexity grows by one at each gate-append step.
-/
theorem complexity_succ
    (t : ℕ) :
    T.complexityAt (Nat.succ t) =
      T.complexityAt t + 1 := by
  rw [T.complexityAt_eq_time (Nat.succ t)]
  rw [T.complexityAt_eq_time t]

/--
After `n` explicit append steps, constructive complexity has increased by `n`,
relative to time zero.
-/
theorem complexityAt_eq_initial_add_time
    (n : ℕ) :
    T.complexityAt n = T.complexityAt 0 + n := by
  rw [T.complexityAt_eq_time n]
  rw [T.complexityAt_eq_time 0]
  simp

/--
After `n` explicit append steps, bridge length has increased by `n`,
relative to time zero.
-/
theorem bridgeLengthAt_eq_initial_add_time
    (n : ℕ) :
    T.bridgeLengthAt n =
      T.bridgeLengthAt 0 + n := by
  simpa [bridgeLengthAt] using
    T.complexityAt_eq_initial_add_time n

/--
Bridge length grows by one at each gate-append step.
-/
theorem bridgeLength_succ
    (t : ℕ) :
    T.bridgeLengthAt (Nat.succ t) =
      T.bridgeLengthAt t + 1 := by
  rw [T.bridgeLengthAt_eq_time (Nat.succ t)]
  rw [T.bridgeLengthAt_eq_time t]

end CanonicalGrowingCircuitTrajectory

/-! ## 9. Scale readouts for entropy, complexity, and recurrence -/

/--
Classical maximum complexity scale for `K` bits, using the lecture-level
`K / 2` coin-flip model.
-/
def classicalMaxComplexityScale
    (K : ℕ) : ℕ :=
  K / 2

/--
Quantum maximum complexity scale for `K` qubits.
-/
def quantumMaxComplexityScale
    (K : ℕ) : ℕ :=
  2 ^ K

/--
Quantum recurrence scale for `K` qubits.
-/
def quantumRecurrenceScale
    (K : ℕ) : ℕ :=
  2 ^ (2 ^ K)

/--
The quantum recurrence scale is exponential in the quantum maximum complexity
scale.
-/
theorem quantumRecurrenceScale_eq_two_pow_quantumMaxComplexityScale
    (K : ℕ) :
    quantumRecurrenceScale K =
      2 ^ quantumMaxComplexityScale K :=
  rfl

/--
The quantum maximum complexity scale is exponential in the entropy-scale
parameter `K`.
-/
theorem quantumMaxComplexityScale_eq_two_pow
    (K : ℕ) :
    quantumMaxComplexityScale K = 2 ^ K :=
  rfl

end InfoGeometry.Geometry.EntanglementGeometry
