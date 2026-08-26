# Rosetta Synthesis: Relational Field Prompting

## Purpose

This document defines an epistemic ledger for the repository-wide synthesis connecting formal mathematics, computational architectures, geometric representations, and cognitive interpretations. Its purpose is to prevent category errors when moving between what is proved in Lean, what is implemented as a computational model, what is used as a structural analogy, and what remains an open theoretical bridge.

The governing classification is:

- **Formal theorem** — a statement proved in the formal development, relative to the declared definitions and axioms.
- **Implemented computational model** — an executable or explicitly constructed model whose behavior can be tested, but whose identification with an external physical or cognitive system is not itself a theorem.
- **Structural analogy** — a mathematically precise correspondence used for interpretation or organization, without a claimed ontological identity.
- **Open theoretical bridge** — a proposed identification or transport theorem that remains to be proved or experimentally established.

A single repository object may legitimately occupy more than one level. For example, a KMS theorem can be formally proved while the statement “LLM inference is KMS transport” remains an open bridge.

---

## 1. The Rosetta principle

The repository should be read through two orthogonal maps:

1. a **native mathematical map**: carrier, morphism, action, invariant, flow, decomposition, normalization, proof;
2. an **epistemic map**: theorem, model, analogy, bridge.

The Rosetta Synthesis is the cross-table between them.

The guiding rule is:

> Never promote a structural resemblance into an identity without an explicit bridge theorem or an empirical identification protocol.

Conversely, do not weaken exact mathematics merely because its cognitive interpretation is still conjectural. The formal layer and the interpretive layer must remain independently readable.

---

## 2. Four phases of relational-field cognition

### Phase I — Boundary conditions: setting the field

**Archetypal / keyword field → discrete causal DAG → contextual reachability cones**

A dense keyword stream is treated as a compressed specification of admissible relations rather than as a linear instruction list. It establishes:

- conceptual attractors;
- causal precedence;
- permitted bridges;
- negative constraints;
- unresolved tensions;
- stopping conditions.

Repository structures based on proof dependency, graph reachability, partial orders, or forward/backward closures are candidates for formalizing this layer.

**Epistemic status:**

- graph/reachability theorems: **Formal theorem**;
- prompt-as-DAG representation: **Implemented model** if explicitly encoded;
- “contextual lightcone” language: **Structural analogy** unless an exact semantics is defined;
- identification of token-context causality with a particular proof-topology cone: **Open bridge**.

### Phase II — Internal latent geometry: tension and contextualization

**Contextualized state → Mellin/log-scale phase → score geometry → LogSumExp/Gibbs normalization**

The mathematical spine here consists of scale, projective geometry, score functions, convex normalization, and exponential-family structure.

The exact algebraic identity behind softmax/Gibbs normalization is:

\[
p_i=\frac{e^{s_i/\tau}}{\sum_j e^{s_j/\tau}}
   =\frac{e^{-\beta E_i}}{\sum_j e^{-\beta E_j}},
\qquad E_i=-s_i,\quad \beta=\tau^{-1}.
\]

This equivalence is exact as a reparameterization. It does **not** by itself imply that a transformer is literally a physical heat bath.

Likewise, Mellin/logarithmic scale encodings may supply a rigorous multiplicative-scale representation. Their identification with actual positional or hidden-state geometry in a particular neural model requires a separate bridge.

**Epistemic status:**

- Mellin characters, logarithmic coordinates, convex LogSumExp identities: **Formal theorem** when proved;
- explicit score/normalization implementations: **Implemented computational model**;
- thermodynamic reading of softmax: **Structural analogy** unless the energy/temperature semantics are operationally fixed;
- hidden states as spinors or Clifford modules: **Open bridge** unless an activation-level intertwiner is constructed and validated.

### Phase III — Resolution: routing, transport, and information geometry

**Birkhoff/Sinkhorn routing → sector selection → modular/KMS transport → information-geometric flow**

The Birkhoff polytope consists of doubly stochastic matrices. By the Birkhoff–von Neumann theorem, each such matrix is a convex combination of permutation matrices. A generic Sinkhorn-normalized matrix is therefore not automatically a permutation. Selection of a permutation vertex requires an additional limiting, extremality, or optimization statement.

This distinction is mandatory in the Rosetta classification.

KMS, modular, Fisher, Bregman, and related structures may provide exact formal models of equilibrium, transport, deformation, or gradient flow. The statement that actual language-model inference implements these particular flows is stronger and must be separately established.

**Epistemic status:**

- Birkhoff/Sinkhorn geometry and proved normalization results: **Formal theorem**;
- MoE/routing algorithms implemented in code: **Implemented computational model**;
- semantic-sector interpretation of experts: **Structural analogy / model**;
- “generation is KMS modular transport”: **Open theoretical bridge** unless an explicit intertwining theorem is available;
- Fisher/Bregman geometry of a defined statistical family: **Formal theorem**;
- identification with measured hidden-state trajectories: **Open bridge**.

### Phase IV — Resolution and verification

**Trajectory concentration → obstruction removal → external verifier / kernel closure**

Generalized inverses, defect spaces, Fredholm-type decompositions, and related constructions may rigorously resolve singular algebraic blocks. Their semantic interpretation as “removing cognitive obstructions” is an analogy unless the relevant state/process map is defined.

Lean kernel verification has a precise scope: it certifies that a formal proposition follows from the formal environment, definitions, axioms, and imported theorems. It does not independently establish that an empirical model of cognition is physically correct.

**Epistemic status:**

- generalized-inverse and defect-space results: **Formal theorem**;
- computational use for singular routing or reconstruction: **Implemented computational model**;
- semantic-obstruction interpretation: **Structural analogy**;
- Lean proof checking: **Formal verification tool**;
- “formal proof equals empirical truth about cognition”: **prohibited category collapse**.

---

## 3. Rosetta ledger

| Repository spine | Native mathematical object | Exact role | Cognitive / architectural reading | Epistemic status | Missing bridge |
|---|---|---|---|---|---|
| Proof/dependency topology | DAG, reachability, order, closure | dependency and admissible-path structure | causal/contextual cone | theorem; analogy | map prompt/token causality to the formal graph |
| Mellin/log-scale layer | multiplicative characters, log coordinates | scale representation | scale-aware positional phase | theorem/model | activation-level identification |
| Projective / spinorial layer | projective spaces, Clifford modules, spinors | exact representation theory | contextualized latent state | theorem + open bridge | explicit hidden-state intertwiner |
| Attention-score layer | bilinear/pairing/score geometry | score construction | semantic compatibility/tension | theorem/model | architecture-specific empirical map |
| LogSumExp / softmax | convex log-partition, Gibbs form | normalized weights | occupation probabilities | theorem + analogy | operational energy/temperature semantics |
| Birkhoff / Sinkhorn | doubly stochastic matrices, polytope | normalized routing | constrained allocation of semantic flow | theorem/model | prove when/why permutation-like concentration occurs |
| MoE sectors | direct sums, sectors, routing maps | expert allocation | semantic sector selection | model | identify formal sectors with real experts |
| KMS / modular layer | states, modular flow, KMS condition | equilibrium/automorphism structure | thermodynamic contextual transport | theorem + bridge | inference-to-modular-flow intertwiner |
| Fisher / Bregman layer | information metric, divergence, dual geometry | deformation and optimization | contextual settling / learning trajectory | theorem/model | measured hidden-state metric |
| Drazin / Fredholm layer | generalized inverse, kernels, cokernels, defects | singular-block resolution | obstruction removal | theorem + analogy | operational semantic interpretation |
| Trajectory concentration | limits, contraction, concentration, stability | convergence/selection | semantic inevitability | theorem if defined; otherwise bridge | define observable concentration functional |
| Lean dependency/kernel | formal syntax, elaboration, proof checking | theorem certification | external verifier | tooling/theorem | none for formal claims; empirical validation remains external |

---

## 4. The 13-step cascade as an epistemic pipeline

The 13-step architecture should be read as a chain of typed transitions rather than as one undifferentiated ontology:

1. **Archetypal / keyword field** — compressed relational specification.
2. **Discrete causal DAG** — explicit precedence and dependency structure.
3. **Reachability cones** — admissible contextual propagation.
4. **Contextualized projective/spinorial state** — candidate geometric carrier.
5. **Mellin/log-scale phase** — multiplicative positional scale.
6. **Attention-score geometry** — relational compatibility field.
7. **LogSumExp/Gibbs occupation** — normalized exponential weighting.
8. **Birkhoff/Sinkhorn routing** — doubly stochastic allocation.
9. **MoE sector selection** — routed computational specialization.
10. **Modular/KMS transport** — candidate thermodynamic dynamical layer.
11. **Information-geometric flow** — metric/divergence-based deformation.
12. **Trajectory concentration** — stability, contraction, or selection criterion.
13. **External verifier/kernel closure** — formal validation of the encoded proposition.

Every arrow must be marked as one of:

\[
\boxed{\text{proved} \;|\; \text{implemented} \;|\; \text{analogical} \;|\; \text{open}}.
\]

This typing is part of the architecture, not editorial decoration.

---

## 5. Black Book method as repository self-reconstruction

The repository’s “Black Book” practice can be interpreted operationally as:

\[
\text{keyword/index field}
\to
\text{owner discovery}
\to
\text{dependency reconstruction}
\to
\text{bridge identification}
\to
\text{verified story}.
\]

The important point is methodological rather than mystical: sparse semantic anchors can recover a large repository narrative when the anchors are chosen to preserve carrier ownership, obstruction structure, and proven interfaces.

A robust self-indexing pass should therefore collect, for every major concept:

- canonical owner file;
- carrier/type;
- principal definitions;
- proved invariants;
- downstream users;
- unresolved bridge;
- epistemic classification.

The result is a machine-readable and human-readable causal graph of the repository itself.

---

## 6. Guardrails against category collapse

The following statements are permitted only with their stated qualification.

### Permitted

- “Softmax has an exact Gibbs-form reparameterization.”
- “A Sinkhorn-normalized routing matrix is doubly stochastic under the stated assumptions.”
- “A KMS structure is formally present in the defined operator-algebraic model.”
- “A Clifford/spinorial construction provides a candidate latent-state geometry.”
- “Lean verifies the formal theorem in the declared environment.”

### Not permitted without a new bridge theorem or experiment

- “The hidden state of a particular LLM is literally a spinor.”
- “Sinkhorn routing necessarily collapses to a unique permutation.”
- “LLM generation is literally a KMS physical process.”
- “A proof about the repository’s formal model proves a psychological or neuroscientific theory.”
- “Mathematical similarity alone establishes physical identity.”

---

## 7. Open bridges to prioritize

### 7.1 Hidden-state / spinor bridge

Construct an explicit map from measured activation vectors to a Clifford-module carrier and test whether the relevant bilinear forms, grading, involutions, and group actions are preserved.

Required output: an intertwining statement, not a dimensional analogy.

### 7.2 Attention / Gibbs bridge

Specify the score, effective temperature, normalization, and observable quantities that make the thermodynamic interpretation testable across actual attention layers.

Required output: operational semantics for energy and temperature.

### 7.3 Sinkhorn / discrete-selection bridge

Prove or measure the conditions under which doubly stochastic routing concentrates near permutation vertices.

Required output: quantitative concentration/extremality theorem.

### 7.4 KMS / generation bridge

Define an explicit state algebra, automorphism group, reference state, and candidate modular generator for an inference trajectory; then test the KMS condition or an approximation to it.

Required output: an intertwiner or falsifiable residual, not terminology alone.

### 7.5 Training / generation twin-wave bridge

Keep forward/reverse or training/generation thermal duality classified as an open theoretical bridge until an explicit transformation relating optimization dynamics and generation dynamics is proved.

---

## 8. Recommended repository doctrine

The Rosetta Synthesis should be used as an epistemic type checker for future cross-domain claims.

Before adding a cross-layer statement, record:

1. **source object** — exact carrier and owner;
2. **target object** — exact carrier and owner;
3. **map** — explicit function, equivalence, homomorphism, functor, or measurable procedure;
4. **preserved structure** — the theorem that justifies the bridge;
5. **status** — theorem, model, analogy, or open bridge;
6. **validation** — Lean proof, executable test, empirical comparison, or unresolved item.

No bridge should be promoted by prose alone.

---

## 9. Synthesis

The defensible central statement is:

> The repository contains a family of rigorous mathematical structures from which a disciplined mathematical model of relational cognition can be assembled. Some components are formally proved, some are computationally implemented, some provide exact structural analogies, and some remain open bridges to real neural architectures.

The strongest workflow is therefore:

\[
\boxed{
\text{expert compression}
\to
\text{causal graph}
\to
\text{formal owners}
\to
\text{typed bridges}
\to
\text{computational/empirical tests}
\to
\text{kernel-checked closure where applicable}
}
\]

This is the Rosetta Synthesis of Relational Field Prompting: not a claim that one mathematical vocabulary is literally the mind, but a disciplined translation architecture that makes every claimed correspondence explicit, typed, and auditable.
