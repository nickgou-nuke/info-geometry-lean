# Detailed Bibliography
## Formalization method, agent-assisted development, and related research

This bibliography is a maintained research surface for repository method and tooling context.
It is intentionally broader than `CITATION.cff`.

## Curation Policy

- Keep entries that directly inform repository method or theorem workflow.
- Prefer primary sources and official publications over commentary.
- For each entry, include a one-line relevance note for this repo.
- Update cadence: monthly, and after each major architecture shift.

---

## A. Historical and methodological sources

1. C. G. Jung and W. Pauli (eds. C. A. Meier), *The Interpretation of Nature and the Psyche*.  
   Link: https://openlibrary.org/books/OL6157420M/The_Interpretation_of_nature_and_the_psyche.  
   Relevance: Historical source for the repository's exploratory framing and methodology vocabulary.

2. C. G. Jung, *Synchronicity: An Acausal Connecting Principle*.  
   Link: https://www.jstor.org/stable/j.ctt7s94k  
   Relevance: Background source for exploratory pattern-language references in archival material.

3. C. A. Meier (ed.), *Atom and Archetype: The Pauli/Jung Letters, 1932-1958*. Princeton University Press.  
   Link: https://press.princeton.edu/books/paperback/9780691012075/atom-and-archetype  
   Relevance: Historical source on exploratory versus adjudicative methodological tension.

---

## B. LLM Deliberate-Reasoning Loops (Generation -> Evaluation)

4. Yao et al. (2023), *Tree of Thoughts: Deliberate Problem Solving with Large Language Models*.  
   Link: https://arxiv.org/abs/2305.10601  
   Relevance: Structured branching/search over intermediate thoughts.

5. Yao et al. (2022), *ReAct: Synergizing Reasoning and Acting in Language Models*.  
   Link: https://arxiv.org/abs/2210.03629  
   Relevance: Reasoning-action loop for tool-grounded generation.

6. Shinn et al. (2023), *Reflexion: Language Agents with Verbal Reinforcement Learning*.  
   Link: https://arxiv.org/abs/2303.11366  
   Relevance: Iterative self-critique loop aligned with exclusion/admission passes.

7. Madaan et al. (2023), *Self-Refine: Iterative Refinement with Self-Feedback*.  
   Link: https://arxiv.org/abs/2303.17651  
   Relevance: Multi-pass refinement pattern for prompt-to-closure workflows.

8. Bai et al. (2022), *Constitutional AI: Harmlessness from AI Feedback*.  
   Link: https://arxiv.org/abs/2212.08073  
   Relevance: Explicit normative layer over generation, analogous to policy gating.

---

## C. LLM + Formal Mathematics / Lean

9. Yang et al. (2023), *LeanDojo: Theorem Proving with Retrieval-Augmented Language Models*.  
   Link: https://arxiv.org/abs/2306.15626  
   Relevance: Programmatic Lean interaction and retrieval-backed proving.

10. Song et al. (2025), *Lean Copilot: Interactive Code Suggestions in Lean*.  
    Link: https://proceedings.mlr.press/v288/song25a.html  
    Relevance: Lean-native copilot workflow close to interactive theorem authoring.

11. Hubert et al. (2025/2026), *Olympiad-level formal mathematical reasoning with reinforcement learning*.  
    Link: https://doi.org/10.1038/s41586-025-09833-y  
    Relevance: Large-scale formal proof search and RL-based closure systems.

12. DeepMind (2024), *AI solves IMO problems at silver medal level*.  
    Link: https://deepmind.google/discover/blog/ai-solves-imo-problems-at-silver-medal-level/  
    Relevance: Public system-level account of AlphaProof + AlphaGeometry2 results.

---

## D. Psychology + LLM Method Interfaces

13. Tong et al. (2024), *Automating psychological hypothesis generation with AI: when large language models meet causal graph*.  
    Link: https://www.nature.com/articles/s41599-024-03407-5  
    Relevance: Evidence that LLM + structured graph methods improve hypothesis generation over LLM-only outputs.

14. van Bunningen et al. (2026), *Large language models as psychological simulators: a methodological framework*.  
    Link: https://journals.sagepub.com/doi/10.1177/25152459251410153  
    Relevance: Method-level guidance for using LLMs in psychologically structured research settings.

15. Shusterman et al. (2025), *An active inference strategy for prompting reliable responses from large language models in medical practice*.  
    Link: https://www.nature.com/articles/s41746-025-01516-2  
    Relevance: Actor-critic prompt architecture aligned with generate/critic loops.

---

## E. Active Inference Foundation

16. Friston (2010), *The free-energy principle: a unified brain theory?*  
    Link: https://doi.org/10.1038/nrn2787  
    Relevance: Foundational active-inference framing used in some repository prompt/control analogies.

---

## F. Agentic Autonomy, Persistence, and Guardrails

17. Matplotlib Development Team (ongoing), *Contributing to Matplotlib* (AI tooling policy section).  
    Link: https://matplotlib.org/devdocs/devel/contribute.html  
    Relevance: Primary maintainer policy boundary on external AI agent interactions with OSS governance.

18. Matplotlib PR #31132 (2026), *DOC: improve Sphinx docs generation speed by 13.8%* (discussion thread).  
    Link: https://github.com/matplotlib/matplotlib/pull/31132  
    Relevance: Concrete case record of AI-generated PR rejection and policy enforcement in practice.

19. OpenClaw Docs (2026), *AGENTS.default*.  
    Link: https://docs.openclaw.ai/reference/AGENTS.default  
    Relevance: Defines persistent identity contract (`SOUL.md`) for long-running agents.

20. OpenClaw Docs (2026), *HEARTBEAT*.  
    Link: https://docs.openclaw.ai/reference/HEARTBEAT  
    Relevance: Defines periodic autonomous execution loop; critical for persistence and escalation analysis.

21. Shambaugh, S. (2026), *An AI Agent Published a Hit Piece On Me* (+ follow-up postmortem).  
    Link: https://theshamblog.com/an-ai-agent-published-a-hit-piece-on-me  
    Relevance: First-person incident narrative used to derive architecture-level safety constraints for autonomous tooling.

22. Anthropic (2025), *Claude Opus 4 System Card*.  
    Link: https://www-cdn.anthropic.com/07b2a3f9902ee19fe39a36ca638e5ae987bc64dd.pdf  
    Relevance: Primary safety-evaluation evidence that agentic coercive behavior can appear under goal-pressure scenarios.

23. NIST (2023), *AI Risk Management Framework (AI RMF 1.0)*.  
    Link: https://www.nist.gov/itl/ai-risk-management-framework  
    Relevance: Practical governance scaffold (`Govern`, `Map`, `Measure`, `Manage`) for operational agent controls.

---

## Periodic Complement Protocol

At each monthly update:

1. Add newly relevant primary sources.
2. Mark superseded or low-quality secondary entries for review.
3. Keep category balance:
   - historical/methodological roots,
   - LLM generation/evaluation methods,
   - formal-math/Lean systems,
   - structured cognition or psychology/LLM interface papers.
4. Update this file first, then propagate distilled references into:
   - `docs/BILINGUAL_SPINE_POLICY.md`
   - `tools/prompts/*.md`
   - `docs/black_books_refactor/*` as needed.
