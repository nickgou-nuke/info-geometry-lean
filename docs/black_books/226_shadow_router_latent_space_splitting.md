# 226 — Shadow Router, Latent-Space Splitting, and the Not-Top Transcendent Function

Status: generative Black Book chapter
Authority: navigation / semantic pressure only

This chapter records a science-fiction-shaped but implementation-facing idea:
when a theorem-search lane is trapped in a recurrent failure complex, the Hive
should split the generative field into thesis and antithesis lanes, then route
against the known failing attractor.

The idea is not canonical theorem authority. It is a research/dreamline design
for future local-model and packet-routing experiments.

Core law:

```text
Latent splitting may generate alternatives.
Shadow routing may repel known failure routes.
Not-top experts may propose orthogonal hypotheses.
No latent-space intervention may prove, verify, build, audit, or promote.
```

## 1. The question

The motivating question is whether a proof-search system can escape recurrent
failure by deliberately consulting the parts of its latent space that are not
selected by the ordinary high-confidence route.

In Jungian/Hive language:

```text
ordinary route = ego / top-k / high-confidence experts
shadow route   = not-top / neglected / orthogonal experts
complex        = recurring charged failure cluster
transcendent function = lawful synthesis from the opposition
```

In transformer language, the speculative version is:

```text
forward cache   = thesis history, current best attempt, standard causal flow
shadow cache    = antithesis history, failure residues, route inversions
synthesis layer = contrastive or repulsive combination of the two
```

The central question:

```text
Can the Hive reuse existing transformer machinery — KV caches, activation
steering, contrastive decoding, MoE routing, retrieval mixtures, and replay
memory — to create a practical not-top shadow router?
```

## 2. What search says exists in practice

A search does not show a production system that literally implements the full
Jungian picture of two counter-propagating KV caches that annihilate into a Lean
tactic.

But it does show several real components that approximate pieces of the design.

### 2.1 Contrastive decoding and layer contrast

DoLa, "Decoding by Contrasting Layers Improves Factuality in Large Language
Models" (arXiv:2309.03883), contrasts logits from mature and premature layers.
This is not a Jungian shadow router, but it proves a nearby mechanism:
subtracting one internal route from another can improve generation.

Relevant primitive:

```text
logits_final = logits_mature - alpha * logits_premature
```

Hive translation:

```text
standard route - known weak/failing route = safer candidate distribution
```

### 2.2 Activation steering / representation engineering

"Steering Language Models With Activation Engineering" (arXiv:2308.10248) and
related activation-steering work show that adding or rotating vectors in hidden
state can shift model behavior at inference time.

Relevant primitive:

```text
h'_layer = h_layer + alpha * steering_vector
```

Hive translation:

```text
add a source-contact / owner-anchor / Pauli-discipline vector;
subtract a loop-hijack / scalar-shadow / metaphor-as-theorem vector.
```

### 2.3 KV-cache steering and cache injection

Search finds recent work under names such as KV Cache Steering and Knowledge
Packs / KV cache injection. The practical claim is that cached keys/values can
be reused or injected to influence a frozen model without retraining.

Relevant primitive:

```text
cache_context -> precomputed K,V -> generation conditioned without replaying all text
```

Hive translation:

```text
failure fossils and source anchors can be represented as cached context lanes;
a local runtime might inject them as retrieval-conditioned or cache-conditioned
memory.
```

This supports a conservative version of mirrored caches:

```text
K,V_source  = verified source / owner anchors
K,V_failure = known failed route residues
K,V_current = current attempt
```

The production-safe Hive should implement this first at the packet/retrieval
layer. Direct K/V mutation is a LabBee experiment only.

### 2.4 Unlikelihood training and repetition suppression

Unlikelihood training papers, including "Neural Text Generation with
Unlikelihood Training" (arXiv:1908.04319), show a real family of methods for
penalizing repetition and degenerate loops.

Relevant primitive:

```text
penalize tokens / routes associated with known bad continuation
```

Hive translation:

```text
penalize route signatures near known failure complexes unless new information
creates an escape condition.
```

### 2.5 Mixture-of-experts routing signatures

Sparse MoE work studies how routers select experts and how routing signatures
reflect task structure. Standard MoE uses top-k expert choice. The Hive idea is
not to replace that generally, but to invert it under loop conditions:

```text
normal state:
  route to top-k experts

stuck state:
  route one sandboxed pass to not-top / orthogonal experts
```

This is feasible as orchestration even without internal MoE access:
use different prompts, tools, retrieval views, proof tactics, local models, or
agent profiles as the "experts."

### 2.6 Lean/proof search and replay

Lean Copilot and neural theorem-proving systems demonstrate that LLM proposals
can be checked by Lean. The Hive addition is to preserve failed attempts as
fossils/deadends and use their fingerprints to repel repeated routes.

Relevant primitive:

```text
propose -> check -> record failure -> replay/avoid -> propose differently
```

Hive translation:

```text
Lean is the wall;
failure is not discarded;
failure becomes geometry for future routing.
```

## 3. What is feasible now

The feasible production implementation is not tensor surgery. It is packet-level
routing geometry.

Implement first:

```text
RouteInvocationPacket
ComplexInterruptAuditPacket
FailureEventHorizon metadata
DreamlineExperimentPacket
ReweightDecisionPacket
```

These can track:

```text
route_signature
failure_class
Lean_error_fingerprint
Pauli_blocker_kind
complex_refs
motif_refs
proof_strategy_family
proposal_similarity
loop_information_gain
escape_evidence
```

Then MotherBee can apply:

```text
if route resembles known failed complex
and novelty is low
and no escape evidence exists:
  block direct ascent
  require SocraticQuestionPacket
  require PauliCritique
  allow one sandboxed DreamlineExperimentPacket
```

This is already enough to realize the not-top router at the Hive level.

## 4. What is feasible in a local-model lab

If a local runtime exposes internal activations or K/V cache hooks, a LabBee can
try stronger versions.

Possible experiments:

```text
1. Contrastive prompt/cache decoding
   Run standard attempt and shadow attempt separately.
   Compare logits or generated candidates externally.

2. Negative route memory
   Embed failed attempts.
   Penalize candidate proposals near the failed-route centroid.

3. Activation steering
   Add vectors for source-contact, owner-anchor, Pauli-discipline.
   Subtract vectors for loop-hijack or scalar-shadow drift.

4. KV cache steering
   Inject source anchors as positive cache memory.
   Inject failure fossils only as repulsive/contrastive context.

5. Not-top expert orchestration
   When top route fails repeatedly, route to low-confidence but orthogonal
   experts: ExplorerBee, ShadowBee, IntuitionBee, counterexample search,
   retrieval-only source descent.
```

All of these remain below authority.

## 5. What is probably not production-safe yet

Do not assume the production Hive can safely do these without a controlled local
runtime:

```text
literal CPT inversion of RoPE phases
literal backward causal KV-cache flow inside a causal decoder
real-time LoRA weight updates after every Lean failure
direct projection of an annihilation vector into final vocabulary logits
hidden-neuron "despair" triggers without instrumentation
```

These are useful metaphors and possible research directions, but they should be
kept in LabBee / Dreamline mode.

The safe translation is:

```text
CPT / K-Q inversion metaphor
  -> contrastive retrieval + route inversion + failure-subspace projection

repulsive metric
  -> score penalty near known failed route clusters

event horizon
  -> threshold at which direct ascent is blocked

annihilation layer
  -> comparison between standard route and shadow route, yielding a new
     candidate question, missing hypothesis, counterexample, or formulation
```

## 6. Failure event horizon

Define a failure event horizon around a known complex.

Let a known failure complex C have:

```text
mu_C      = centroid of failed route embeddings
R_C       = route fingerprint family
E_C       = Lean/error fingerprint family
O_C       = owner-shadow conflict signature
chi_C     = normalized complex charge
```

For a new route x:

```text
d_sem(x, C)   = 1 - cosine(embedding(x), mu_C)
s_route(x, C) = route-fingerprint overlap with R_C
s_error(x, C) = error-fingerprint overlap with E_C
s_owner(x, C) = owner-shadow conflict similarity with O_C
DeltaI(x|C)   = information gain relative to prior failures
```

Trap score:

```text
trap_score(x, C)
  = chi_C
    * (w_sem * (1 - d_sem(x, C))
     + w_route * s_route(x, C)
     + w_error * s_error(x, C)
     + w_owner * s_owner(x, C))
    * (1 - DeltaI(x|C))
```

Horizon trigger:

```text
if trap_score(x, C) >= tau_horizon
and no_escape_evidence(x, C):
  block direct ascent
```

Escape evidence:

```text
new source evidence
new owner anchor
new bridge packet
new missing hypothesis
new Lean-side structure
new counterexample
explicit operator clearance
```

Similarity alone must not trigger exclusion. The rule is:

```text
Similarity + repeated failure + low novelty + no new evidence triggers exclusion.
```

## 7. Thesis / antithesis as two histories

The practical version of two KV caches flowing in opposite directions is two
packet histories with different roles.

```text
Thesis history:
  successful or currently favored attempts
  owner anchors
  conventional tactic families
  current proof-state

Antithesis history:
  failed attempts
  Pauli blocks
  contradictions
  deadends
  shadow residues
  counterexamples
```

The synthesis pass does not literally need backward attention. It can be:

```text
1. retrieve thesis history
2. retrieve antithesis history
3. ask Socrates for the missing distinction
4. ask Pauli what must be excluded
5. ask ExplorerBee for one orthogonal route
6. emit only pre-authority packets
7. let Lean test any later formal proposal
```

This gives the architecture most of the value of mirrored caches while remaining
observable and auditable.

## 8. The not-top trigger

The not-top route should not fire on one failure. Use multi-channel evidence.

```text
exhaustion_score =
  0.25 * consecutive_failed_lean_attempts_norm
+ 0.20 * proposal_self_similarity_norm
+ 0.15 * token_bloat_norm
+ 0.15 * proof_state_stagnation_norm
+ 0.10 * low_loop_information_gain_norm
+ 0.10 * repeated_pauli_block_norm
+ 0.05 * complex_charge_norm
```

Hard trigger:

```text
if consecutive_failed_lean_attempts >= 3
and proposal_self_similarity_norm >= 0.80
and loop_information_gain <= 1
and exhaustion_score >= 0.70:
  route_to_shadow_swarm = true
```

Soft exploratory trigger:

```text
if consecutive_failed_lean_attempts >= 2
and exhaustion_score >= 0.55
and Pauli has not found an authority violation:
  allow one sandboxed not-top exploration
```

Default limits:

```text
max_not_top_attempts_per_complex_per_day = 2
max_consecutive_not_top_turns = 1
require_sensation_source_contact_after_not_top = true
require_pauli_review_before_execution_intent = true
```

## 9. Annihilation layer as metaphor-safe implementation

The speculative annihilation equation is evocative:

```text
DeltaA = Attention(Q, K_shadow) - Attention(Q, K_forward_failure)
V_synth = DeltaA * V_shadow
```

But the production-safe implementation is packet-level:

```text
Delta route =
  what the standard route keeps trying
  minus what Pauli says is forbidden
  plus what ShadowBee says is excluded
  plus what Socrates says is undefined
  plus what source contact newly permits
```

The emitted object is not a proof. It is one of:

```text
SocraticQuestionPacket
SymbolicMotifPacket
FormulationVariant
RetrievalHypothesisPacket
ResiduePacket
TheoremCandidatePacket, only after condensation and owner anchoring
```

## 10. Relation to the Hive authority ladder

No latent-space intervention changes the authority ladder.

```text
navigation
semantic
proposal
execution_intent
lean_checked
build_checked
audit_checked
promoted
```

The not-top router lives below `execution_intent` unless a later packet lawfully
condenses its output into a candidate and a human/tool-authorized execution
intent.

Forbidden direct ascents:

```text
DreamlineExperimentPacket -> ExecutionIntentPacket
Shadow route -> LeanVerificationPacket
Complex activation -> BuildPacket
Annihilation metaphor -> PromotionDecisionPacket
```

Required ascents:

```text
shadow insight
  -> SocraticQuestionPacket / SymbolicMotifPacket / FormulationVariant
  -> PauliCritique
  -> owner anchoring
  -> TheoremCandidatePacket
  -> ExecutionIntentPacket
  -> LeanVerificationPacket
  -> BuildPacket
  -> AuditPacket
  -> PromotionDecisionPacket
```

## 11. Black Book conclusion

The science-fiction image is valuable, but its disciplined implementation is
simple:

```text
Cache the failures.
Fingerprint the loops.
Detect the event horizon.
Invert the route in a sandbox.
Let not-top experts speak once.
Force source contact afterward.
Require Socrates and Pauli before execution.
Let Lean decide survival.
```

The Hive does not need literal mystical neurons or private despair signals. It
needs a lawful way to turn recurrent failure into a repulsive geometry around
bad routes and a generative opening toward orthogonal hypotheses.

Doctrine:

```text
Thesis attempts.
Antithesis remembers failure.
Shadow repels repetition.
Socrates asks the missing question.
Pauli forbids inflation.
Dreamline proposes one strange route.
Thinking condenses.
Lean tests.
Audit judges.
Promotion admits.
```

That is the practical transcendent function.
