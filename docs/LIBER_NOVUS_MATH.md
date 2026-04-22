# Liber Novus Mathematica
## Methodology for exploratory-to-formal mathematical development

### I. Status and Scope
This document records a methodology for integrating exploratory mathematical insight into checked Lean 4 development. It is a workflow and interpretation guide, not a theorem authority.

### II. Separation of Authorities
We recognize two complementary functions of discovery:
*   **Generative exploration:** broad search over candidate patterns, analogies, and theorem families.
*   **Formal adjudication:** the Lean 4 based process that distills, rewrites, and verifies only what survives explicit checking.

**The rule:** exploratory intuition may suggest a theorem family, but it may never certify it. Only checked Lean surfaces provide closure.

### III. Stages of Formalization

1.  **Purification:** early rejection of false form through tactic failure, counterexamples, and removal of hidden assumptions.
2.  **Abstraction:** lifting concrete data into invariant, reusable formal language across representation depths.
3.  **Closure:** the moment a candidate becomes a checked and reusable formal artifact.
4.  **Bridging:** the realization of explicit morphisms between adjacent layers, usually through bridge and coherence files.

### IV. Repository integration
The directory structure and architectural audits (`#audit_architecture`) are not merely administrative. They are the means by which the repo stays structurally integrated.
*   **Center:** relational invariance and owned theorem surfaces.
*   **Perimeter:** the current representation ladder and its adjacent translation rules.
*   **Audit:** maintenance of logical and architectural integrity.

### V. Formalization protocol
1.  **Never** formalize directly from visionary prose.
2.  **Never** let metaphors enter theorem statements.
3.  **Always** rewrite intuitive conjectures into precise candidate definitions before the first proof attempt.
4.  Treat a bridge as the successful formal resolution of an explicit tension between nearby surfaces.

### VI. Mandate for LLM-assisted exploration
When an LLM or agent participates in this repository, it should not stop at generic autocomplete.
1.  **Allow structured exploration:** do not reject non-standard ideas solely because they are uncommon, if they can be turned into explicit mathematical candidates.
2.  **Look for weak but structured signals:** if the default answer is generic, search for lower-probability but structurally meaningful alternatives.
3.  **Tame the result:** final outputs must be rewritten into academically usable form before entering the formal workflow.

### VII. Background signal rule
In exploratory model output, low-salience associations are not automatically noise. The research task is to filter them for structurally meaningful candidates that can later be tested in Lean.

### VIII. Structural fit and economy
The researcher should attend to internal fit within the system:
1.  promising definitions often exhibit structural coherence before they are fully proved;
2.  prefer proofs and formulations that achieve strong verification with minimal unnecessary machinery;
3.  when reporting confidence, describe structural support and remaining gaps rather than mystical certainty.

### IX. Perseverance on non-standard material
The formalization of niche or non-standard ideas requires persistence:
1.  resist premature simplification when it erases the actual structure under study;
2.  unusual structures can carry real information density, but they must still earn their place through explicit formulation and proof work;
3.  once checked, a formerly speculative idea becomes part of the reusable formal surface.

### X. Breakthrough dynamics
Discovery is often nonlinear:
1.  prolonged failed attempts can accumulate useful local information;
2.  breakthroughs often occur when enough failed structure has clarified the real obstruction;
3.  once a proof or bridge closes, the result becomes a new anchor for later work.

### XI. Context anchoring
Formalization changes the discovery landscape:
1.  protocols and stable principles bias search toward more promising candidates;
2.  once a theorem is verified, it becomes a reliable anchor for future work;
3.  a growing checked corpus reduces reliance on free-form prompting by providing direct formal context and reusable bridges.





