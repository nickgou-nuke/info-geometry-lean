# Graph-Resident Hive Runtime Design

This document captures a runtime architecture where ArangoDB is the durable substrate and Lean remains the sole source of theorem truth.

## Core invariant

- Lean owns truth.
- Arango owns memory.
- The model owns proposals only.
- Bees are stateless and disposable.

## Runtime planes

1. **Lean truth plane**: Lean sources, Lake build, kernel checks, DAG exporters, audit/vacuity tooling.
2. **Graph substrate plane**: declaration + expression graph, topology overlays, motifs, and hole/Hodge metrics.
3. **Hive runtime plane**: goals/tasks/workers/resources plus immutable packet/event history.
4. **Bee worker plane**: specialized workers (retrieval, proposal, verification, audit, promotion, frontier, Hodge).
5. **Control plane**: leases, monitoring, replay, and scheduling feedback.

## Why this fits the existing repository

- `lean/DAG/README.md` already frames DAG outputs as navigation/audit under Lean truth.
- `lean/DAG/ExprArangoExport.lean` already emits Arango-style node/edge exports for declarations and expressions.
- `tools/infra/hive_arango_queue.py` already defines queue/task/event/lease and lineage primitives.
- `tools/infra/hive_bee.py` already follows retrieve → propose → Lean verify → fossil/deadend flow.

The implementation direction is therefore modularization and hardening, not wholesale rewrite.

## Data model

### Current-state collections

- `hive_goals`
- `hive_tasks`
- `hive_workers`
- `hive_resources`
- `hive_resource_leases`

### Immutable packet/event collections

- `hive_events`
- `hive_retrieval_packets`
- `hive_proof_state_packets`
- `hive_proposals`
- `hive_critiques`
- `hive_execution_intents`
- `hive_verifications`
- `hive_build_packets`
- `hive_audit_packets`
- `hive_candidate_packets`
- `hive_promotions`
- `hive_replay_packets`

### Memory/failure collections

- `hive_fossils`
- `hive_deadends`
- `hive_negative_constraints`
- `hive_sorry_obligations`

### Lineage collections

- `hive_task_for_goal`
- `hive_event_about`
- `hive_task_emits_packet`
- `hive_task_consumes_packet`
- `hive_packet_depends_on`
- `hive_goal_closed_by`
- `hive_goal_rejected_by`

## Authority levels

Enforce monotonic packet authority:

- `navigation`
- `semantic`
- `proposal`
- `execution_intent`
- `lean_checked`
- `build_checked`
- `audit_checked`
- `promoted`

Only verifier/build/audit/promotion workers can emit their corresponding elevated authorities.

## Worker split

- `MotherBee`: schedules tasks from goal impact + topology pressure.
- `RetrievalBee`: deterministic context packets from graph + fossils + negatives.
- `HydrationBee`: prompt-ready rendering, no model calls.
- `ProposalBee`: structured edits/proofs (JSON packets only).
- `CritiqueBee`: cheap policy gates before Lean.
- `VerifierBee`: Lean command execution and normalized failure recording.
- `AuditBee`: no-sorry/no-vacuity/layer policy checks.
- `PromotionBee`: success→fossil / failure→deadend+constraint.
- `FrontierBee`: Arango-native frontier scoring and enqueueing.
- `HodgeBee` and `GWHoleMetricBee`: derived geometric pressure metrics for scheduling.

## Queue and lease semantics

- Task claim is atomic and lease-based.
- Workers heartbeat in `hive_workers`.
- Work executes outside long transactions.
- Every meaningful state transition is reflected in immutable packets/events.

## Negative cache strategy

1. **Tactic-level** dedupe on `(state_before_hash, prompt_hash, patch_hash, failure_class)`.
2. **State-level** pruning on recurring dead-end goal-shape clusters.

Both should be consulted before expensive Lean invocations.

## Retrieval packet contract

Deterministically include:

1. Target declaration/signature/state hash.
2. SCC/topology placement and dominators.
3. Nearby support lemmas.
4. Shape-equivalent fossils.
5. Motif evidence.
6. Hole/Hodge pressure metrics.
7. Relevant negative constraints.
8. Namespace-density decision.

## Recommended package structure

```text
src/igf/hive/
  db.py
  schema.py
  queue.py
  packets.py
  retrieval.py
  hydration.py
  prompt.py
  model.py
  verifier.py
  audit.py
  negative_cache.py
  scheduler.py
  hodge_metrics.py
  gw_hole_metrics.py
  bees/
```

Keep existing scripts as wrappers while migrating internals.

## Minimal bring-up sequence

1. Export Lean declaration/expression graph.
2. Ingest into Arango (`ig_nodes`, `ig_edges`).
3. Build topology overlays.
4. Initialize hive queue/runtime collections.
5. Run one smoke-test bee.
6. Split specialized bees after end-to-end packet flow is verified.

## Smoke test expectations

For a canary target, verify:

1. Goal insertion.
2. Task creation/claim.
3. Retrieval packet write.
4. Proposal packet write.
5. Lean verification write.
6. Fossil or deadend emission.
7. Negative cache blocks duplicate failure attempts.

## Non-goals / guardrails

- No single monolithic orchestrator class.
- No model-selected dependencies outside retrieval envelope.
- No treating LSP diagnostics as theorem truth.
- No conflating graph metrics with kernel validity.
- No direct frontier mutation of source without verifier/audit/promotion chain.
- No removal of existing artifact workflows while introducing Arango-native runtime mode.


## Symmetry closure correction: affine–Virasoro, not finite-dimensional closure

For the symmetry substrate, the mathematically precise closure is an **affine–Virasoro extension** of the split real form, not an ordinary closure of finite-dimensional `E_{8(8)}`.

Start from the finite-dimensional Lie algebra:

- `g0 = e_{8(8)}`.

Loop/current algebra:

- `L e_{8(8)} = e_{8(8)} \otimes R[z, z^{-1}]` with generators `J^a_n = T^a \otimes z^n`.

Affine central extension (level `k`):

- `[J^a_m, J^b_n] = f^{ab}{}_c J^c_{m+n} + k m \kappa^{ab} \delta_{m+n,0} K`.
- `[K, J^a_n] = 0`.

This is the algebraic form of affine `E_9 \simeq E_8^{(1)}` (in split real notation, often emphasized as `\widehat{E}_{8(8)}` / `E_{9(9)}` contextually).

Promoting loop rotation to full circle reparametrizations gives Witt/Virasoro generators `L_n = -z^{n+1} d/dz` with:

- `[L_m, L_n] = (m-n) L_{m+n} + (c/12) m(m^2-1) \delta_{m+n,0} C`.
- `[L_m, J^a_n] = -n J^a_{m+n}`.

So the closed algebra is:

- `G_closed = Vir_c \ltimes \widehat{e}_{8(8),k}`.

with central elements `K` and `C` commuting with everything.

Sugawara realization for affine `E_8` currents:

- `L_n = 1/(2(k+h^\vee)) \sum_m :\kappa_{ab} J^a_{n-m} J^b_m:`.
- For `E_8`: `h^\vee = 30`, `dim E_8 = 248`.
- Central charge: `c = k dim(E_8)/(k+h^\vee) = 248k/(k+30)`; at `k=1`, `c=8`.

Compact axiom statement:

- **Affine–Virasoro closure axiom**: `e_{8(8)} \mapsto Vir_c \ltimes \widehat{e}_{8(8),k}`.

Geometrically, this upgrades the symmetry object from finite `G = E_{8(8)}` to an extended loop-diffeomorphism form (often written as a centrally extended `Diff(S^1) \ltimes \widehat{L E}_{8(8)}`), whose Lie algebra is exactly `Vir_c \ltimes \widehat{e}_{8(8),k}`.


## Physical implications of affine–Virasoro closure

If the six-axiom framework closes as `Vir_c \ltimes \widehat{e}_{8(8),k}`, the main implication is that symmetry is **infinite-dimensional conformal-current symmetry**, not merely a finite particle/internal symmetry.

Key consequences:

1. **From finite charges to current towers**
   - `E_{8(8)}` modes become `J^a_n` (`a=1..248`, `n\in Z`), so states are organized by current excitations, not only finite charges.
2. **Conformal reparametrization is intrinsic**
   - Virasoro generators `L_n` are in the same closed algebra as current modes, so modular/scale/reparametrization flow is internal to the symmetry substrate.
3. **Hamiltonian interpretation shifts**
   - Natural dynamics ties to `L_0` (or modular combinations with `J^i_0`), e.g. Gibbs/modular states of the form `exp(-\beta L_0 - \sum_i \mu_i J^i_0)`.
4. **Partition functions become affine–Virasoro characters**
   - Spectral data is constrained by representation theory and modular covariance, using character-like traces `Tr(q^{L_0-c/24} e^{2\pi i z_i J^i_0})`.
5. **Representation-stratified state space**
   - Hilbert sectors decompose by affine label and conformal weight: `H = \bigoplus_{\lambda,h} H_{\lambda,h}`.
6. **Entropy becomes representation-theoretic**
   - Asymptotic state growth (Cardy-type under standard assumptions) links entropy to modular/character data.
7. **Strong holographic/near-horizon signal**
   - `Vir \ltimes \widehat{e}_{8(8)}` aligns with 2D reductions/boundary descriptions of higher-dimensional gravity.
8. **Anomaly data is physical**
   - Level `k` and central charge `c` encode current/conformal anomalies and must satisfy consistency constraints.
9. **Split-real `E_{8(8)}` is gravity-facing**
   - It naturally points to maximal supergravity/U-duality contexts, not directly to `SU(3)\times SU(2)\times U(1)` without explicit breaking/embedding machinery.
10. **Topological subsectors can be protected**
    - Gromov–Witten/TQFT observables provide deformation-invariant amplitudes/indices in sectors stable under geometric fluctuations.

Practical modeling warning:

- This closure gives a strong mathematical framework, but predictive physics still requires explicit choices of Hilbert space, observable algebra, state, dynamics, unitarity/real-form constraints, anomaly matching, and symmetry-breaking path to low-energy phenomenology.

## One-line summary

A lease-driven, packet-emitting Hive where Arango is durable memory, Lean is truth authority, and every attempt—successful or failed—becomes reusable graph memory.

## Symmetry-breaking note: modular/barrier flow vs explicit breaking

To avoid ambiguity in this framework, we treat the relevant dynamics as **modular-gradient flow inside the extended symmetry algebra**, not as ad hoc explicit symmetry breaking.

Working interpretation:

- The negative log generating potential (barrier/free-energy potential) defines a convex/Bregman geometry on state space.
- Relative entropy and relative log-density terms (Radon–Nikodym style in operator-algebra language) act as information-geometric coordinates for flow.
- Modular evolution (`log Δ` / Tomita–Takesaki generator language) is interpreted as a canonical derivation direction for thermodynamic/conformal dynamics.
- In this view, “symmetry reduction” is primarily gauge/sector selection (Weyl-chamber and representation-sector choice), not arbitrary patchwork breaking rules.

For implementation in this repo, this means:

1. Keep algebraic closure statements explicit (`Vir_c ⋉ ê_{8(8),k}`) at the packet/schema layer.
2. Encode entropy/barrier/free-energy objectives as **scheduler potentials** and **cost functionals**, not as theorem-truth claims.
3. Record sector/gauge choices (e.g., chamber, representation branch, normalization) as immutable packet metadata so reductions are auditable.
4. Treat super-geometry/super-algebra language as modeling overlays unless and until Lean witnesses are supplied.

This preserves the core invariant:

- Lean adjudicates formal truth.
- Arango stores geometric/thermodynamic guidance and provenance.
- Bees apply guided search under declared symmetry and potential metadata.
## One-line summary

A lease-driven, packet-emitting Hive where Arango is durable memory, Lean is truth authority, and every attempt—successful or failed—becomes reusable graph memory.
