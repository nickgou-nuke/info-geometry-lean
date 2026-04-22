# The Workbench
## A practical playbook for mathematical discovery

This is a practical guide for handling exploratory idea generation before formalization in the `info-geometry-lean` repository. It describes a human-in-the-loop workflow for moving from speculative prompts to candidate definitions, theorem statements, and checked Lean artifacts.

### 1. Socratic exploration
*   **Action:** Engage the LLM in a constrained dialogue about a concrete bridge tension (for example, how one owner surface fails or extends at a boundary).
*   **Instruction:** Push beyond the most generic answer, but keep the conversation tied to explicit candidate structures, hypotheses, and translation obligations.

### 2. Candidate filtering
*   **Step:** Take the strongest candidate ideas from exploratory notes.
*   **Question:** Does this idea express a stable relational invariant, a concrete bridge obligation, or only a loose analogy?
*   **Check:** Can it be rewritten as a `Definition`, `Theorem`, explicit conjecture, or documented unresolved debt in Lean-oriented terms?

### 3. Formal handoff
*   **Action:** Write the Lean 4 code.
*   **Result:** If the compiler passes and the surrounding structure remains non-vacuous, the candidate has become a usable formal artifact. If it fails, refine the statement, expose the missing premise, or record the unresolved debt explicitly.

### 4. Recording the work
*   **Exploratory notes:** Record raw dialogues and candidate packets in `docs/black_books/` when they may still be useful.
*   **Artifacts:** Store especially useful intermediate outputs in the relevant archive or artifact locations.
*   **Methodology:** Distill reusable, verified workflow lessons into `docs/LIBER_NOVUS_MATH.md` or other maintained operational docs.
