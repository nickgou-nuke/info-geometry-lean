# Epistemic Compilation: Early Computational Models (1936–1970), Gromov's Ergobrain, and Contemporary ML Theory

## Scope and Provenance

This compilation processes a synthesis connecting foundational 1934–1970 mathematical models of thought and computation (Turing, Curry–Howard, McCulloch–Pitts, Hebb, Shannon, Kleene, Chomsky, Rosenblatt, Solomonoff, Gold, Minsky–Papert) with Mikhail Gromov's *Ergosystems* / *Math Currents in the Brain* / *Memorandum Ergo* critiques and contemporary deep-learning theory, supplemented by digested peer-reviewed literature from 1984–2025.

Per [`skills/epistemic-compilation/SKILL.md`](../skills/epistemic-compilation/SKILL.md) and [`docs/EPISTEMIC_COMPILER_FIELD_PROTOCOL.md`](EPISTEMIC_COMPILER_FIELD_PROTOCOL.md), historical narrative, philosophical interpretation, and literature summaries are strictly separated from kernel-checked Lean 4 theorems.

## Fundamental Cut

1. **Theorem-backed discrete boundaries (kernel-checked in Lean 4):**
   - **Threshold-unit expressivity boundary (`EarlyLearningFoundations.lean`):** A single linear-threshold perceptron cannot compute Boolean `XOR`, whereas a depth-2 McCulloch–Pitts threshold network computes `XOR` exactly.
   - **Prediction–compression lower bound (`EarlyLearningFoundations.lean`):** Over any finite positive alphabet distribution, expected cross-entropy decomposes exactly as $H(p, q) = H(p) + D_{\mathrm{KL}}(p \| q) \ge H(p)$, with equality iff $p = q$.
   - **Finite automata and learning-rule cores (`EarlyLearningFoundations.lean`):** deterministic finite-state runs compose over word concatenation; the scalar Hebbian update has an exact co-activity increment; and the finite-dimensional perceptron update has exact score-change and non-decrease identities.
   - **Positive-text non-identifiability (`EarlyLearningFoundations.lean`): No learner can identify in the limit from positive-only text every bounded finite language $\{x \le k\}$ together with $\mathbb{N}$.
   - **Continuous group-representation geometry in attention (`PositionalEncodingRepresentation.lean`, `PositionalEncodingClassification.lean`):** Normalized translation-covariant linear query/key modifiers force one-parameter/commuting matrix exponential flows, normal-mode decoupling (elliptic RoPE, hyperbolic/decaying linear attention, Jordan/ALiBi polynomial biases).
2. **Scoped mathematical theory in literature (not promoted in Lean):**
   - Transformer circuit complexity bounds ($\mathsf{TC}^0$ for constant depth vs. $\mathsf{P}$ with polynomial Chain-of-Thought steps: Merrill–Sabharwal–Smith 2022, Strobl et al. 2024, Merrill–Sabharwal 2024).
   - Valiant (1984) PAC learnability replacing Gold's worst-case exact identification with $(\varepsilon, \delta)$ distributional error bounds.
   - Restricted overparameterization / NTK / linear-model implicit-bias results.
3. **Open mathematical & interpretive boundary:**
   - A complete, general theorem explaining why finite-width overparameterized deep networks trained by SGD avoid bad minima and generalize on natural data distributions ("Gromov's mathematical mystery") remains **open mathematical debt**.
   - Interpretive claims ("Curry–Howard is only slow conscious output", "LLMs solved Chomsky vs. Shannon in favor of pure Markov statistics") are downgraded or refined below.

---

## Stage 1 (`Solve`): Atomic Claim Ledger

| ID | Source / Topic | Core Mathematical or Theoretical Claim | Required Hypotheses / Criterion | Disposition |
|---|---|---|---|---|
| **G1** | Minsky–Papert (1969) | No single linear-threshold unit $(w_1, w_2, \theta)$ computes Boolean `XOR`. | Binary inputs $\{0,1\}^2$; strict threshold $\theta < w_1 x_1 + w_2 x_2$. | `[kernel_verified]` (`minsky_papert_no_single_layer_xor`) |
| **G2** | McCulloch–Pitts (1943) | Depth-2 threshold circuits compute `XOR` (and arbitrary Boolean functions). | 2-layer threshold network with real weights/biases. | `[kernel_verified]` (`mcculloch_pitts_two_layer_computes_xor`) |
| **G3** | Shannon (1948); Delétang–Hutter et al. (2024) | Cross-entropy equals source Shannon entropy plus KL divergence excess code length, lower-bounded by $H(p)$ with equality iff $p = q$. | Finite alphabet; strictly positive normalized distributions $p, q$. | `[kernel_verified]` (`crossEntropy_eq_shannonEntropy_add_kl`, `shannon_compression_lower_bound`, `klDivergence_eq_zero_iff`) |
| **G4** | Gold (1967) | No learner identifies every superfinite class $\{x \le k\} \cup \{\mathbb{N}\}$ in the limit from arbitrary positive-only text streams. | Total stream emitting every member of target language (`IsPositiveText`), exact convergence (`IdentifiesInLimit`). | `[kernel_verified]` (`gold_1967_superfinite_nonidentifiable`) |
| **G5** | Positional group theory | Continuous geometric position representations in transformers act via matrix exponentials of generators (rotations, real exponential decay, nilpotent Jordan shifts). | Linear per-token modifiers, translation covariance, $A(0)=I$, differentiability at $0$. | `[kernel_verified]` (`PositionalEncodingRepresentation.lean`, `PositionalEncodingClassification.lean`) |
| **G6** | Kleene / Hebb / Rosenblatt finite core | Deterministic automaton runs compose over concatenated words; a scalar Hebbian update changes weight by rate times co-activity; the perceptron score change is error times input self-correlation. | Explicit finite-state and real-vector carriers; no biological or convergence interpretation. | `[accepted_limited_scope]` (`EarlyLearningFoundations.lean`) |
| **G7** | Turing (1936); Curry (1934) & Howard (1969/1980) | Turing completeness defines algorithmic computability; Curry–Howard establishes propositions-as-types and proof-normalization-as-evaluation isomorphism. | Constructive type theory / $\lambda$-calculus. *(Repo holds finite proof-carrying quadratic model & de Bruijn beta-reduction preorder, not full meta-theoretic strong normalization.)* | `[accepted_limited_scope]` / `[bucket_3_open_debt]` |
| **G7a** | Kleene (1956); Chomsky (1956/1957); Strobl et al. (2024) | Regular languages $\equiv$ finite automata $\equiv$ McCulloch–Pitts nerve nets; transformer expressivity is NOT simply Chomsky-regular/CFG, but aligns with uniform $\mathsf{TC}^0$ (fixed depth) and $\mathsf{P}$ (poly CoT steps). | Precision, softmax vs. hard attention, LayerNorm, step count. | `[bucket_2_conditional]` (literature-established; not in Lean) |
| **G8** | "LLMs completely revindicated Shannon over Chomsky" (prompt narrative) | Overstatement as stated: modern LLMs do not operate merely as low-order Markov chains nor capture all context-free/P problems at constant depth without CoT; they succeed statistically within $\mathsf{TC}^0$/CoT-$\mathsf{P}$ and continuous distributional geometry. | Architectural depth, precision, CoT length. | `[countermodel_found]` (narrative refinement against Strobl et al. 2024) |
| **G9** | Gold (1967) vs. Valiant (1984) PAC learning | Gold's theorem is NOT falsified by LLMs; rather, modern ML switches from worst-case exact identification to $(\varepsilon, \delta)$ PAC distributional approximation and cross-entropy minimization. | Independent or natural data-generating distribution; $\varepsilon, \delta > 0$ tolerance. | `[bucket_2_conditional]` (paradigm distinction) |
| **G10** | Solomonoff (1964) & Hutter AIXI | Solomonoff universal prior achieves optimal sequence prediction asymptotically across computable sources. | Computable measures, uncomputable universal mixture over prefix-free Turing machines. | `[bucket_3_open_debt]` |
| **G11** | Gromov (2011, 2014) *Ergobrain* / SGD non-convex mystery | Unsupervised compression into internal geometric invariants explains structural learning; high-dimensional overparameterized SGD avoids bad local minima and generalizes via flat/connected basins & implicit bias. | Open unifying finite-width deep-network theorem; proved only in special regimes (NTK, linear/matrix factorization, SDE heuristics). | `[bucket_3_open_debt]` |
| **G12** | Gromov (2011, 2014) philosophical claim | "Early pioneers confused conscious deductive output (logic/grammar) with the subsymbolic geometric engine." | Cognitive/philosophical thesis outside formal Lean proof types. | `interpretation-only` |

---

## Stage 2 (`Coniunctio`): Repository Owner Map

| Thread / Mechanism | Repository Owner File & Key Declarations | Exact Scope Covered |
|---|---|---|
| Single-layer vs. two-layer XOR threshold boundary | [`lean/InfoGeometry/LLM/EarlyLearningFoundations.lean`](../lean/InfoGeometry/LLM/EarlyLearningFoundations.lean) (`bitToReal`, `singleLayerThreshold`, `minsky_papert_no_single_layer_xor`, `twoLayerThresholdXOR`, `mcculloch_pitts_two_layer_computes_xor`) | Exact ℝ-arithmetic threshold hyperplanes on `Bool × Bool` |
| Finite automata and learning-rule cores | [`lean/InfoGeometry/LLM/EarlyLearningFoundations.lean`](../lean/InfoGeometry/LLM/EarlyLearningFoundations.lean) (`DeterministicAutomaton.run_append`, `DeterministicAutomaton.accepts_append`, `hebbianUpdate_sub`, `hebbianUpdate_lt_of_pos`, `dotProduct_perceptronUpdate`, `dotProduct_self_nonneg`, `perceptron_score_nondec`) | Finite-state word composition and explicit real update identities; no convergence or biological claim |
| Shannon entropy & prediction-as-compression lower bound | [`lean/InfoGeometry/LLM/EarlyLearningFoundations.lean`](../lean/InfoGeometry/LLM/EarlyLearningFoundations.lean) (`shannonEntropy`, `crossEntropy`, `klDivergence`, `crossEntropy_eq_shannonEntropy_add_kl`, `klDivergence_nonneg`, `shannon_compression_lower_bound`, `klDivergence_eq_zero_iff`) | Finite alphabet, strictly positive normalized pmfs `p, q` |
| Gold (1967) superfinite identification-in-the-limit obstruction | [`lean/InfoGeometry/LLM/EarlyLearningFoundations.lean`](../lean/InfoGeometry/LLM/EarlyLearningFoundations.lean) (`IsPositiveText`, `IdentifiesInLimit`, `gold_1967_superfinite_nonidentifiable`) | Abstract learners `List ℕ → (ℕ → Prop)` on `{x ≤ k} ∪ {ℕ}` |
| Continuous geometric attention & positional group actions | [`lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean`](../lean/InfoGeometry/LLM/PositionalEncodingRepresentation.lean), [`lean/InfoGeometry/LLM/PositionalEncodingClassification.lean`](../lean/InfoGeometry/LLM/PositionalEncodingClassification.lean) (`attentionScore_diagonalizable_exp` :135, `jordanBlock` :442, `exp_smul_jordanBlock` :516, `real_exp_decay_tendsto_zero` :629, `decayFlow_eq_exp` :682, `linearAttentionReadout_eq_pairwise_sum` :792, `multiDim_generators_commute_and_exp` :942) | Matrix exponential representations, RoPE, ALiBi Jordan blocks, causal linear-attention decay |
| Gromov / Jaynes finite counting probability | `lean/InfoGeometry/GromovProbability.lean`, `lean/InfoGeometry/Probability/GromovFiniteCounting.lean`, `lean/InfoGeometry/GromovJaynesProbability.lean` | Finite subset counting and secondary rational normalization |
| Shannon entropy / softmax Gibbs KL variational principle | `lean/InfoGeometry/Probability/HomologicalProbability.lean`, `lean/InfoGeometry/Thermodynamics/SoftmaxGibbsVariationalPrinciple.lean` | Finite-state Gibbs free energy and KL optimality |
| Proof-carrying optimization & de Bruijn lambda preorder | `lean/InfoGeometry/Epistemology/CurryHowardReality.lean`, `lean/DAG/LambdaReductionPreorder.lean` | Proof-carrying quadratic optimum; syntactic $\beta$-reduction preorder (not full CH meta-theory) |

---

## Stage 3 (`Causal Poset`): Dependency Graph of Proved Statements

```text
N1 (bitToReal / singleLayerThreshold)
  ├─→ N2 (minsky_papert_no_single_layer_xor)
  └─→ N3 (mcculloch_pitts_two_layer_computes_xor)

N4 (Real.log_le_sub_one_of_pos, Real.log_lt_sub_one_of_pos, Real.log_div)
  ├─→ N5 (kl_term_sub_ge_zero)
  │     ├─→ N6 (klDivergence_nonneg)
  │     └─→ N8 (klDivergence_eq_zero_iff)
  └─→ N7 (crossEntropy_eq_shannonEntropy_add_kl)
        └─→ N9 (shannon_compression_lower_bound)  [depends on N6, N7]

N10 (IsPositiveText, IdentifiesInLimit, prefixList_prefixText_append)
  └─→ N11 (gold_stage_step)
        └─→ N12 (gold_1967_superfinite_nonidentifiable)

N13 (deterministic automaton word composition)
  ├─→ N14 (finite Hebbian update identities)
  └─→ N15 (finite perceptron score-change identity)

[Outside DAG — Literature / Open Debt / Interpretation Only]:
  - Uniform TC^0 vs. CoT-P Transformer bounds (Strobl et al. 2024; Merrill–Sabharwal 2024)
  - Valiant PAC learnability & empirical LLM compression (Delétang–Hutter et al. 2024)
  - Gromov Ergobrain (2011, 2014), SGD implicit bias, flat-minima & mode-connectivity theory
```

---

## Digested Literature Supplement (1934–2025)

### 1. The Foundational Era (1934–1970)
- **Turing (1936)** — *On Computable Numbers, with an Application to the Entscheidungsproblem*; **Turing (1948 / 1950)** — *Intelligent Machinery* (unorganized B-type machines) & *Computing Machinery and Intelligence* (educable child-machine).
- **Curry (1934) & Howard (1969, circulated 1969 / published 1980)** — *The Formulae-as-Types Notion of Construction*: structural isomorphism between intuitionistic natural deduction proofs and simply-typed $\lambda$-calculus normalization.
- **McCulloch & Pitts (1943)** — *A Logical Calculus of the Ideas Immanent in Nervous Activity*: binary threshold networks compute Boolean logic and bounded temporal patterns.
- **Shannon (1948)** — *A Mathematical Theory of Communication*: entropy rate, $n$-gram Markov source models, and source-coding compression limits.
- **Hebb (1949)** — *The Organization of Behavior*: associative synaptic plasticity rule.
- **Kleene (1956)** — *Representation of Events in Nerve Nets and Finite Automata*: equivalence between regular expressions, finite automata, and finite-memory McCulloch–Pitts nets.
- **Chomsky (1956, 1957)** — *Three Models for the Description of Language* & *Syntactic Structures*: Chomsky Hierarchy (regular, context-free, context-sensitive, RE) and critique of finite-order Markov approximations of syntax.
- **Rosenblatt (1958)** — *The Perceptron: A Probabilistic Model for Information Storage and Organization in the Brain*: tunable continuous-weight linear threshold classifier and convergence theorem for linearly separable data.
- **Solomonoff (1964)** — *A Formal Theory of Inductive Inference* (universal algorithmic prior over programs/descriptions).
- **Gold (1967)** — *Language Identification in the Limit*: superfinite language classes cannot be identified exactly in the limit from positive examples alone.
- **Minsky & Papert (1969)** — *Perceptrons: An Introduction to Computational Geometry*: exact impossibility results for single-layer/order-bounded perceptrons on `XOR`, `Parity`, and topological connectedness.

### 2. Mikhail Gromov's Ergosystems & Brain Geometry Corpus
- **Mikhail Gromov (Dec 30, 2011)** — *Structures, Learning and Ergosystems* (IHES preprint, Chapters 1–4, 6; often referred to as *Ergobrain*): distinguishes pragmatic *ego-mind* survival heuristics from *ergobrain*—goal-free unsupervised extraction and compression of symmetry, metric, and topological invariants from high-dimensional sensory streams.
- **Mikhail Gromov (June 13, 2014)** — *Math Currents in the Brain* (IHES) & *Memorandum Ergo*: argues that formal symbolic logic (*Ergologic* critique) is a secondary conscious overlay atop continuous geometric/topological pattern formation; poses why high-dimensional non-convex optimization finds smooth, generalizing structures as an open mathematical challenge.

### 3. Modern Theoretical Synthesis (1984–2025)
- **Beyond Gold's Impossibility — PAC Learning (Valiant, 1984):** *A Theory of the Learnable* replaced worst-case exact identification of adversarial streams with probably approximately correct ($1 - \delta$ confidence, $\le \varepsilon$ generalization error) learning under a probability distribution, explaining why statistical learners succeed where exact grammar identification fails.
- **Transformers and Circuit Complexity (Merrill–Sabharwal–Smith 2022; Strobl, Merrill, Weiss, Chiang, & Angluin, *TACL* 2024; Merrill & Sabharwal 2024):**
  - *What Formal Languages Can Transformers Express? A Survey* (*TACL* 2024) maps transformer expressivity not coarsely onto the Chomsky hierarchy, but onto uniform threshold circuit classes: constant-depth fixed/log-precision softmax and hard-attention transformers lie in **uniform $\mathsf{TC}^0$** (which computes majority/counting strictly outside regular languages, yet fails unbounded sequential state tracking like arbitrary-depth Dyck languages or $\mathsf{NC}^1$-hard / $\mathsf{P}$-complete problems in constant depth).
  - Allowing autoregressive **Chain-of-Thought (CoT)** generation steps scales expressivity sharply: logarithmic steps offer modest gains, linear projected pre-norm steps reliably capture regular languages, and **polynomial CoT steps characterize $\mathsf{P}$** exactly (Merrill & Sabharwal 2024).
- **Prediction as Compression (Delétang, Ruoss, Grau-Moya, Hutter, et al., 2024):** *Language Modeling Is Compression* proves empirically and information-theoretically (via arithmetic coding and Shannon's cross-entropy bound $H(p, q) = H(p) + D_{\mathrm{KL}}(p \| q)$) that probabilistic sequence predictors act as universal lossless compressors—connecting Shannon (1948) and Solomonoff (1964) / Hutter's compression-as-intelligence directly to modern transformers.
- **Overparameterization, SGD Implicit Bias, Loss Landscapes & Mode Connectivity:**
  - *Interpolation & degenerate manifolds:* overparameterized loss minima form continuous high-dimensional submanifolds rather than isolated traps; **Neural Tangent Kernel (NTK)** regimes linearize infinite-width training into kernel regression (though finite-width feature learning goes beyond NTK).
  - *Implicit bias & flatness:* gradient descent biases linear/factorized models toward minimum-norm / max-margin solutions, while SGD gradient covariance noise steers trajectories away from sharp Hessian directions toward flat minima.
  - *Mode connectivity & Gromov-type metric geometry:* permutation-aligned SGD minima exhibit low-barrier path connectivity across basins, and high-dimensional representational comparison uses metric-measure / Gromov–Wasserstein geometry—leaving a single unifying mathematical proof for finite-width transformer generalization as active open theory.

---

## Stage 4 (`Coagula`): Verification Record

- **Owner modules:** [`lean/InfoGeometry/LLM/EarlyLearningFoundations.lean`](../lean/InfoGeometry/LLM/EarlyLearningFoundations.lean), [`lean/InfoGeometry/LLM/PositionalEncodingClassification.lean`](../lean/InfoGeometry/LLM/PositionalEncodingClassification.lean).
- **Exact-path 4-gate verification (`PASS`):**
  - `EarlyLearningFoundations.lean`: `opengauss_screener.py` (`0 traps detected`), `run_locked_lake_build.py` (`Build completed successfully (3198 jobs).`, exit `0`), `axiom_check.lean` (`all 67 declarations clean`, `MODULE_RESULT:.lake/build/lib/lean/InfoGeometry/LLM/EarlyLearningFoundations.olean:PASS`), and `proof_proxy_staged_gate.py` (`proof_proxy_staged_gate: ok`).
  - `PositionalEncodingClassification.lean`: `opengauss_screener.py` (`0 traps detected`), `run_locked_lake_build.py` (`Build completed successfully (8992 jobs).`, exit `0`), `axiom_check.lean` (`all 202 declarations clean`, `MODULE_RESULT:.lake/build/lib/lean/InfoGeometry/LLM/PositionalEncodingClassification.olean:PASS`), and `proof_proxy_staged_gate.py` (`proof_proxy_staged_gate: ok`).
- **Scope:** full unscoped staged gate is not claimed where unrelated files in the shared worktree differ between worktree and active index; verification above is exact-path and module-local.
- **Open debt retained honestly:** see the claim ledger; notably finite-width SGD generalization, uniform circuit-complexity bounds, Valiant PAC bounds, full Curry–Howard meta-theory, Solomonoff uncomputability, full Hebbian dynamics, and Rosenblatt convergence remain unclosed. The newly closed results cover only the finite automaton and algebraic learning-rule cores.
