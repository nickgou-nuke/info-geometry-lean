# Deep Research: Lean4 + LLM Theorem Proving Landscape (as of 2026-04-18)

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

## Scope
This note focuses on **recent (2025–2026)** public work relevant to your current architecture:
- DAG/InfoTree-driven retrieval and training data generation
- Lean4 proof generation in nonstandard codebases
- Agentic orchestration with local models and compiler feedback loops

Only primary sources were used (arXiv/OpenReview/official docs/repositories).

## Date Anchoring (2026 check)
- Current date used for this pass: **2026-04-18**.
- Lean ecosystem is active in 2026; release and model references below include exact dates.

## What Others Are Doing Recently

### 1) Unified Lean4 data+training stacks are becoming standard
**LeanDojo-v2** positions itself as an end-to-end framework (tracing, dataset mgmt, fine-tuning, proving, IDE integration), not just a dataset extractor.
- Publicized at NeurIPS MATH-AI 2025.
- Includes both local HF fine-tuning paths and API-backed inference.
- Active packaging updates in 2026 (PyPI `lean-dojo-v2` 1.0.8 on 2026-03-10).

Why it matters for your repo: your InfoTree/DAG pipeline is aligned with where the field moved; the differentiator is **your theory-specific graph semantics and nonstandard theorem links**.

### 2) Training is shifting from plain SFT to verifier-coupled RL + decomposition
Across top open systems (DeepSeek-Prover-V2, Goedel-Prover-V2, BFS-Prover-V2), a recurring pattern appears:
- Subgoal decomposition and staged curriculum
- Verifier/compiler feedback for iterative correction
- RL or preference-style optimization over tactic/proof trajectories

#### DeepSeek-Prover-V2 (arXiv 2504.21801)
- Submitted: 2025-04-30; revised 2025-07-18.
- Core pattern: recursive decomposition + synthetic cold-start + RL.
- Reports strong MiniF2F/PutnamBench numbers and introduces ProverBench.

#### Goedel-Prover-V2 (arXiv 2508.03613)
- Submitted: 2025-08-05.
- Core pattern: scaffolded data synthesis + verifier-guided self-correction + checkpoint/model averaging.
- Strong emphasis on self-correction loop quality and compute efficiency at smaller sizes.

#### BFS-Prover-V2 (arXiv 2509.06493; repo integration)
- Submitted: 2025-09-08; revised 2025-10-09.
- Core pattern: multi-turn off-policy RL + planner-enhanced multi-agent tree search.
- Practical angle: explicit Lean integration path (LLMLean/Ollama) for local interactive workflows.

Why it matters for your repo: your dual-hypothesis + gate scripts are pointed in the right direction. The next step is tightening the **feedback-policy loop**, not only generating hypotheses.

### 3) Benchmarks are shifting from olympiad math saturation to code verification realism
Recent benchmark work highlights a known ceiling on MiniF2F-style progress and a gap in software-grade formal reasoning:

#### VeriBench-FTP (OpenReview, 2025-10-17; modified 2025-11-21)
- 857 theorems from 140 code verification problems.
- Reported pass rates are much lower than math-only benchmarks, showing practical difficulty remains high.

#### VeriBench (OpenReview, submitted to ICLR 2026; modified 2026-02-11)
- End-to-end Lean4 code verification framing (implementation + tests + specs + proofs).
- Shows current models still struggle and iterative agentic/debug loops matter.

Why it matters for your repo: for nonstandard theorem webs, “can it compile and prove in your codebase” is a better target metric than generic benchmark pass@k.

### 4) Lean core itself is evolving toward verification workflows
Lean **4.28.0 (2026-02-17)** introduced a symbolic simulation framework integrated with `grind`, explicitly supporting verification-condition and symbolic-execution style workflows.

Why it matters for your repo: this reduces friction for building verification-oriented proof tactics around your own generated hypotheses and graph-derived obligations.

### 5) Specialized Lean4 model products are appearing (2026)
**Leanstral** (Mistral, 2026-03-16) is explicitly positioned as a Lean4-oriented open-source code/proof agent.
- Docs/model card report a large sparse architecture (119B total, ~6.5B active, 256k context).
- Strong capability target, but memory/serving overhead is still high for many local setups.

Why it matters for your repo: a single huge specialist is not always the best local answer; **small specialist + orchestration + verifier loops** can be more practical on constrained memory.

## Practical Conclusions for *This* Repository

### A) Keep DAG as first-class training signal, but separate three channels
1. **Structure channel**: graph topology, dependency edges, theorem neighborhood fingerprints.
2. **Execution channel**: tactic traces, goal transitions, compiler errors, self-correction logs.
3. **Semantic channel**: normalized theorem statements/lemmas and context windows.

Your advantage is in channel coupling; most generic Lean models underweight unusual but proven local links.

### B) Do not train directly on raw `.olean` bytes as primary modality
You can read `.olean`, but byte-level training is usually low signal for proof behavior. Better approach:
- extract symbolic artifacts from `.olean`/environment (constants, declarations, dependencies),
- align with `.lean` source + InfoTree traces,
- train on semantically typed records rather than raw binary streams.

`.olean` is useful as a **ground-truth index and dependency oracle**, not as the main token stream.

### C) Model strategy for DGX Spark-like constraints
Prefer a two-tier system:
- **Worker prover (small, local, frequent):** 7B–8B class (quantized if needed), fine-tuned on your repo traces.
- **Teacher/planner (larger, sparse or API):** used for hard decomposition/planning, not every step.

This is usually better than trying to keep a very large specialist always resident in memory.

### D) Hermes orchestration is a good fit if you enforce hard gates
Keep Hermes if you make gates strict:
- Lean compile success
- theorem proof completion
- no regression on curated nonstandard theorem set
- novelty score from DAG locality (new useful links, not random drift)

If these gates are weak, any orchestrator will overfit to plausible-looking but low-value generations.

## Suggested Immediate Next Work (repo-specific)
1. Add a **nonstandard theorem evaluation pack** (repo-native), separate from MiniF2F-style metrics.
2. Extend `hypothesis_fuser_and_lean_gate.py` with explicit error-class bucketing (parser/typeclass/rewrite/search timeout).
3. Add DPO/GRPO-style preference signals from accepted vs rejected trajectories.
4. Build a persistent graph store (ArangoDB is reasonable) with theorem node IDs, proof states, and tactic edges for retrieval-time conditioning.
5. Keep `dual_hypothesis_sampler.py` as asymmetric sampler (conservative branch + creative branch) and gate strictly in Lean.

## Local Deep-Research Controller Status
`tools/infra/deep_research/controller.py` is wired for OpenAI-backed deep research, but this environment currently has:
- `OPENAI_API_KEY=unset`

So full API-driven controller runs are blocked until a key is provided.

## Sources
- LeanDojo-v2 site: https://leandojo.org/leandojo.html
- LeanDojo-v2 paper (OpenReview PDF): https://openreview.net/pdf?id=tnx1VvrcAn
- lean-dojo-v2 PyPI release history: https://pypi.org/project/lean-dojo-v2/
- DeepSeek-Prover-V2 (arXiv): https://arxiv.org/abs/2504.21801
- DeepSeek-Prover-V2 repo: https://github.com/deepseek-ai/DeepSeek-Prover-V2
- Goedel-Prover-V2 (arXiv): https://arxiv.org/abs/2508.03613
- Goedel-Prover-V2 repo: https://github.com/Goedel-LM/Goedel-Prover-V2
- BFS-Prover (arXiv 2502.03438): https://arxiv.org/abs/2502.03438
- BFS-Prover-V2 (arXiv 2509.06493): https://arxiv.org/abs/2509.06493
- BFS-Prover-V2 repo: https://github.com/ByteDance-Seed/BFS-Prover-V2
- VeriBench-FTP (OpenReview): https://openreview.net/forum?id=wDjOpXKgtU
- VeriBench (OpenReview, ICLR 2026 submission): https://openreview.net/forum?id=P7NUVF6wo4
- Lean 4.28.0 release notes (2026-02-17): https://lean-lang.org/doc/reference/latest/releases/v4.28.0/
- Leanstral announcement (2026-03-16): https://mistral.ai/news/leanstral
- Leanstral docs: https://docs.mistral.ai/models/leanstral-26-03
- Leanstral model card: https://huggingface.co/mistralai/Leanstral-2603
