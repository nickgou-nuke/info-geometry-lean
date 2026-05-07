# K/Q Phase-Space Antipodal Operator Experiment

> Status: `experimental / local-model-only`
> Authority: proposal steering only
> Scope: define the Antipodal Operator as a sidecar or local-model LabBee mechanism.
> Non-authority boundary: this mechanism may generate route pressure, candidates, motifs, questions, or residues; it may not prove, verify, build, audit, promote, mutate sources, or silently update model weights.

## 0. Correction and naming

A standard transformer inference cache is a KV cache:

```text
standard cache:
  K_i, V_i
```

Keys and values are persisted because future tokens attend to past tokens. Queries are normally transient:

```text
Q_t = current attention query
```

The proposed extension is therefore not a replacement for a key-only cache. It is a phase-space sidecar beside the normal KV cache:

```text
phase-space cache:
  K_i, Q_i, V_i, route_signature_i, outcome_i, failure_class_i, Pauli_blocker_i
```

The important addition is not `Q_i` alone. It is `Q_i` plus later outcome metadata:

```text
[K_i, Q_i, V_i, route_signature, outcome, failure_class, Pauli_blocker]
```

Without the outcome label, the system only knows that an intent-context pair occurred. With the outcome label, it can distinguish useful recurrence from failed recurrence.

## 1. Purpose

The Antipodal Operator is a local-model experimental operator for escaping recurrent failure geometry.

Definition:

```text
Antipodal Operator A_F:
  given a current phase-space state x_t and a known failure subspace F,
  project or reflect x_t away from F, producing an orthogonal exit-vector
  that can steer alternative proposal generation.
```

Hive interpretation:

```text
A repeated [Q, K] pattern can detect a wrong direction and wrong place.
The Antipodal Operator can propose an orthogonal exit.
Only Lean can decide whether that exit is a proof.
```

## 2. Phase-space record

Represent each historical interaction as a normalized phase-space vector:

```text
p_i = normalize(
  alpha · k_i
  ⊕ beta · q_i
  ⊕ chi · v_i
  ⊕ rho · r_i
)
```

Where:

```text
k_i = historical key/context vector
q_i = historical query/intent vector
v_i = value/action/tactic vector, optional
r_i = route/outcome embedding, such as failure class or Pauli blocker
⊕   = concatenation or learned/random projection into a common space
```

The current state is represented similarly:

```text
p_t = normalize(
  alpha · k_t
  ⊕ beta · q_t
  ⊕ chi · v_t
  ⊕ rho · r_t
)
```

Production fallback, when true tensors are unavailable:

```text
p_proxy = normalize(concat(
  embedding(goal),
  embedding(current_attempt),
  embedding(tactic_family),
  embedding(error_fingerprint),
  embedding(owner_module),
  embedding(pauli_findings)
))
```

The same operator works over either true K/Q traces or route-level semantic proxies.

## 3. Recursive match / event horizon

A recursive failure state is detected only when intent, context, route, and outcome agree.

```text
intent_sim  = cos(q_t, q_i)
context_sim = cos(k_t, k_i)
route_sim   = cos(p_t, p_i)
```

A cached record is a recursive match when:

```text
recursive_match_i =
  intent_sim  >= tau_q
  AND context_sim >= tau_k
  AND route_sim   >= tau_p
  AND outcome_i ∈ {failed, deadend, Pauli_blocked, deprecated_failure}
```

The event horizon triggers when:

```text
inside_event_horizon =
  max_i(route_sim_i) >= tau_block
  AND failure_rate(route_signature) >= rho_block
  AND semantic_novelty <= nu_block
  AND no_escape_evidence
```

Escape evidence:

```text
new owner anchor found
new bridge packet exists
missing hypothesis extracted
theorem shape materially changed
prior Pauli blocker resolved
new counterexample found
operator explicitly requests replay
```

Similarity alone must not block a route. The safe rule is:

```text
similarity + repeated failure + low novelty + no escape evidence => block direct ascent
```

## 4. Failure subspace

Build a failure subspace from top matching failed records:

```text
F = span(top failed p_i vectors)
U_F = orthonormal basis of F
P_F(x) = U_F U_F^T x
```

Use SVD/PCA or Gram-Schmidt to construct `U_F`.

Rank should be small:

```text
r = min(max_rank, number_of_failed_records, dimension_limit)
```

Default:

```text
max_rank = 8
```

## 5. Antipodal Operator forms

### 5.1 Conservative projection

The safest operator removes only the part explained by the failure subspace:

```text
A_F_projection(x) = normalize(x - P_F(x))
```

Meaning:

```text
remove the component of the current route that lies inside the known failure;
keep the orthogonal residue.
```

Use this first.

### 5.2 Strong reflection

The stronger Householder-style reflection is:

```text
A_F_reflection(x) = normalize(x - 2P_F(x))
```

Meaning:

```text
move across the failure subspace into the antipodal direction.
```

Use only in LabBee mode after projection-mode experiments are stable.

### 5.3 Exit vector

The operator emits:

```text
x_exit = A_F_projection(p_t)
```

Optionally:

```text
x_anti = A_F_reflection(p_t)
```

These are proposal-steering vectors, not proof objects.

## 6. Reranking rule

Use the exit vector to rerank candidate next actions:

```text
score_final(candidate) =
    score_base(candidate)
  + gamma · alignment(candidate, x_exit)
  - lambda · similarity(candidate, F)
  - pi · Pauli_risk(candidate)
  + omega · owner_anchor_gain(candidate)
  + eta · missing_hypothesis_gain(candidate)
```

Interpretation:

```text
boost candidates that align with the orthogonal residue;
penalize candidates falling back into the failure subspace;
boost source contact, owner anchoring, missing-hypothesis extraction;
suppress Pauli/owner-shadow violations regardless of novelty.
```

Allowed outputs:

```text
SocraticQuestionPacket
SymbolicMotifPacket
FormulationVariant
RetrievalHypothesisPacket
ResiduePacket
TheoremCandidatePacket, only after condensation and owner anchoring
```

Forbidden outputs:

```text
ExecutionIntentPacket
LeanVerificationPacket
BuildPacket
AuditPacket
PromotionDecisionPacket
source mutation
persistent model-weight update
```

## 7. Minimal-disturbance implementation levels

### Level 0 — no model surgery

Use route-level packet and embedding proxies.

```text
RouteInvocationPacket
KVQTracePacket or KQPhaseRecordPacket
RutAuditPacket
AntipodalRoutePacket
```

This is robust and works with any model lane.

### Level 1 — local-model hooks

Only for local open-weight models with PyTorch/Hugging Face-style access.

```text
weights frozen
no persistent mutation
capture q/k/v tensors through forward hooks
compute failure similarity
apply external reranking or soft-prefix steering
```

Hook `q_proj` and `k_proj` outputs, not FlashAttention internals.

### Level 2 — custom attention kernel

Experimental only.

```text
modify LlamaAttention/FlashAttention-like path
store Q history beside normal KV cache
add attention-logit penalties inside forward pass
proposal output only
```

This level is high-risk because cache managers expect shapes like:

```text
K: [batch, heads, seq, head_dim]
V: [batch, heads, seq, head_dim]
```

The Q sidecar should remain separate:

```text
past_key_values.append((new_k, new_v))
phase_space_cache.append(new_q, new_k, route_metadata)
```

## 8. Forward-hook prototype shape

Conceptual only:

```python
class QKTrace:
    def __init__(self):
        self.records = []

    def append(self, layer_idx, q, k, v=None, token_ids=None, metadata=None):
        self.records.append({
            "layer_idx": layer_idx,
            "q": q.detach().float().cpu(),
            "k": k.detach().float().cpu(),
            "v": None if v is None else v.detach().float().cpu(),
            "token_ids": token_ids,
            "metadata": metadata or {},
        })
```

Recursive match:

```python
def recursive_match(q_new, k_new, failed_records, tau_q=0.82, tau_k=0.82):
    matches = []
    for rec in failed_records:
        sq = cosine(q_new, rec["q"])
        sk = cosine(k_new, rec["k"])
        if sq >= tau_q and sk >= tau_k:
            matches.append((rec, sq, sk, 0.5 * (sq + sk)))
    return sorted(matches, key=lambda x: x[-1], reverse=True)
```

Projection operator:

```python
def antipodal_projection(x, failure_basis):
    # failure_basis: orthonormal columns, shape [d, r]
    proj = failure_basis @ (failure_basis.T @ x)
    residue = x - proj
    return residue / (residue.norm() + 1e-8)
```

No model weights are updated.

## 9. Closed-loop variant and lambda calibration

A purely internal closed-loop attention penalty is possible as a LabBee experiment, but it is more dangerous than external reranking because it can destroy syntactic gravity.

Conceptual penalty:

```text
standard_logits = Q_new K^T / sqrt(d)
intent_penalty  = lambda_repel · sim(Q_new, Q_failed) · sim(K_current, K_failed) · failure_weight
modified_logits = standard_logits - intent_penalty
```

Do not set `lambda_repel` as a constant. Use a gated schedule:

```text
lambda_repel = lambda_max
  · sigmoid((loop_score - tau_horizon) / temperature)
  · failure_confidence
  · (1 - syntax_risk)
  · authority_lane_gate
```

Default behavior:

```text
lambda_repel = 0 below event horizon
lambda_repel small inside soft horizon
lambda_repel capped inside hard horizon
lambda_repel disabled in Lean/build/audit/promotion lanes
```

Suggested starting values for lab experiments:

```text
lambda_max = 0.05 to 0.20 attention-logit units
soft horizon tau = 0.65
hard horizon tau = 0.80
cooldown = reset after one generated candidate or if perplexity/syntax risk spikes
```

Safety condition:

```text
if entropy rises too fast or syntax_risk increases:
  reduce lambda_repel by half or disable for the next step
```

In words:

```text
repel only when a failure loop is actually detected;
repel softly;
turn repulsion off as soon as syntax starts dissolving.
```

## 10. Dynamic pruning

Do not store every Q.

Persist a phase-space record only when one of these holds:

```text
Lean rejection occurred
same theorem route failed >= 2 times
proposal similarity >= 0.80 across attempts
proof state did not change
token/output bloat was high
Pauli flagged inflation
audit blocked semantic authority
route touched a known complex
operator marked it important
unexpected success occurred after prior failures
```

Discard or summarize:

```text
ordinary successful low-surprisal steps
repeated trivial context
low-charge routine completions
token-level traces with no failure or novelty
```

Buffer tiers:

```text
ephemeral Q:
  normal generation; not stored

short-term Q summary:
  stored during active theorem attempt

persistent phase-space fossil:
  stored only for high-surprisal failure, loop, Pauli block, or surprising success
```

## 11. Packet sketch

A future `KVQTracePacket` or `KQPhaseRecordPacket` should remain semantic/proposal-only:

```json
{
  "kind": "KVQTracePacket",
  "authority": "semantic",
  "authority_origin": "experimental_phase_space_trace",
  "epistemic_layer": "cognitive_process",
  "promotion_allowed": false,

  "model_scope": {
    "local_model_only": true,
    "weights_frozen": true,
    "trace_type": "qk_phase_space",
    "persistent_model_update": false
  },

  "route": {
    "route_signature": "route_owner_shadow_gap_8f31",
    "target_packet_id": "packet_candidate_T123",
    "strategy_family": "scalar_shadow_bridge_attempt",
    "outcome": "failed",
    "failure_class": "owner_shadow_violation",
    "pauli_blocker": "metaphor_as_theorem"
  },

  "allowed_uses": [
    "rut_detection",
    "antipodal_projection",
    "proposal_reranking",
    "dreamline_constraint"
  ],
  "forbidden_uses": [
    "proof",
    "promotion",
    "authority_gate_bypass",
    "direct_source_mutation"
  ]
}
```

A future `AntipodalRoutePacket` should likewise be non-authority:

```json
{
  "kind": "AntipodalRoutePacket",
  "authority": "proposal",
  "authority_origin": "antipodal_route_projection",
  "epistemic_layer": "packet_lineage",
  "promotion_allowed": false,

  "operator": {
    "name": "A_F_projection",
    "formula": "normalize(x - P_F(x))",
    "reflection_enabled": false
  },

  "forbidden_next": [
    "same_strategy_family",
    "direct_builder_edit",
    "promotion_request"
  ]
}
```

## 12. Invariant

```text
Antipodal projection may change search direction.
It may not certify the new direction.
```

Final compact formula:

```text
Store [K, Q, outcome].
Detect repeated failed intent-context pairs.
Fit failure subspace F.
Compute x_exit = normalize(x - P_F(x)).
Use x_exit to steer proposals away from the rut.
Lean decides whether the exit was real.
```
