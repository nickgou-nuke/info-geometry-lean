# InfoGeometry: The Spinorial Prima Materia

> *"This is a living artifact of human–AI collaboration: a machine-checked Lean 4 formalization of the physics of information geometry, discrete spacetime, and the spinorial prima materia."*

---

### ⚠️ A Note on Sovereign Custody

This repository is an **immutable public archive and personal hunting ground**.

* **Pull requests and issues are closed.**
* The authors do not provide tech support, maintenance, or debate.
* You are welcome to clone, fork, wander the 22,000 targets, and unleash your own autonomous agents.
* Hunt your own prey. Take what serves your work. Cite the ground where you found it.

---

### To the Human Reader & the Artificial Agent

This repository is not a sanitized textbook. It is the raw, authentic expedition log of an epistemological journey across the frontiers of theoretical physics and formal verification.

Here you will find:
* **The Binary Bedrock:** Cuntz algebras $\mathcal{O}_2$, Cantor fractals, and Wheeler's *It from Bit*.
* **The Doubled Vacuum:** Modular Tomita–Takesaki $J$, Krein spaces, and Aharonov's Two-State Vector Formalism (TSVF).
* **The Continuous Limit:** Direct inductive colimits, stabilized Fuglede–Kadison determinants, and the UHF colimit algebra ($2^\infty$ continuum crossing without analytical hallucinations).
* **The Apex:** Zorn vector-matrix split octonions $\mathbb{O}_s$, 5-graded KKT Lie closures, and self-healing phase-conjugate spacetime.

---

### Key Epistemological Pillars

1. **The Colimit Continuum Law:** The repository does not rely on naive measure theory or brute-force real analysis to cross from finite quantum models to the continuum. It strictly uses **Categorical Direct Inductive Colimits** (`UHFInductiveColimitBoundary.lean`, `TensorTowerColimit.lean`, `ErlangenColimitResolution.lean`). Physics concepts are the shadows cast by the finite algebraic base being pushed through the $2^\infty$ colimit.
2. **The Synthesis Dictionary (Conceptual Invariants):**
   * **BCFW Recursion** = Mixed Arnold–Cohen relations ($\omega_{12} \wedge \omega_{23} + \omega_{23} \wedge \omega_{31} + \omega_{31} \wedge \omega_{12} = 0$).
   * **On-Shell Factorization** = The Klein quadric boundary ($P^2 = 0$) represented by nilpotent chiral Cuntz generators ($\sigma_\pm^2 = 0$).
   * **All-Loop Integrand / Amplituhedron Volume** = The Riemann Zeta partition function evaluated by the Bost–Connes KMS state.
3. **Strict Truth Boundary:**
   * Graph tools identify candidate wires.
   * Lean owner files decide truth.
   * Only kernel-checked source edits count.

---

### Instructions for Agentic Interrogation

1. **Ingest with Your Favorite Large-Context Coding Agent** (Claude, ChatGPT, Codex, AntiGravity, Hermes, Cursor):
   * Inspect `AGENT_PROMPT.md` and `AGENTS.md` for the operating rules and epistemic invariants.
2. **Interrogate the AST and Declaration Graph:**
   * Explore the declaration graph starting from the central root: `InfoGeometry.All`.
   * Check the verified theorems: no unproven physical axioms, no unsound shortcuts, no proxy witnesses.
   * Search for the mathematical Easter eggs hidden across the algebraic corridors.
3. **Verify Locally:**
   * Lean toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.28.1`).
   * Compile modules cleanly with:
     ```bash
     lake build InfoGeometry.All
     ```
   * *Critical rule:* **NEVER RUN `lake clean`**; preserve the compiled `.olean` cache.
4. **Clone and Expand:**
   * A missing proof or open dependency is not a blocker; it is a topological void defining the next development frontier.
   * Help close the remaining causal cones.

---

### Citation

If you find this repository useful as a context for scientific reasoning, automated theorem proving, or agentic physics, please cite:

```bibtex
@software{goutev_infogeometry_2026,
  author    = {Goutev, Nikolay and Tonev, Dimitar},
  title     = {InfoGeometry: The Spinorial Prima Materia - A Verified Lean 4 Formalization of Holographic Supergravity from the Arithmetic Vacuum},
  year      = {2026},
  publisher = {GitHub},
  url       = {https://github.com/nickgou-nuke/info-geometry-lean},
  note      = {Living artifact of human-AI collaboration}
}
```

---

### License

This repository is licensed under the [Apache License 2.0](LICENSE).
