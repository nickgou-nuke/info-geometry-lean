# InfoGeometry: The Spinorial Prima Materia

> *"This is a living artifact of human–AI collaboration: a machine-checked Lean 4 formalization of information geometry, quantum foundations, and spacetime structure from first principles."*

---

### ⚠️ A Note on Sovereign Custody

This repository is an **immutable public archive and research frontier**.

* **Pull requests and issues are closed.**
* The authors do not provide tech support, maintenance, or debate.
* You are welcome to clone, fork, explore the codebase, and unleash your own autonomous agents.
* Take what serves your work. Cite the ground where you found it.

---

### To the Human Reader & the Artificial Agent

This repository is not a sanitized textbook. It is the raw, authentic record of an exploratory journey spanning **formal verification, geometric algebra, operator theory, and quantum physics**.

#### What Lives Here

* **Algebraic Foundations:** Operator algebras, spinorial geometry, and the algebraic structures underlying quantum mechanics
* **Quantum Theory:** Formalization of quantum state spaces, observables, and information-theoretic principles
* **Category Theory & Topology:** Rigorous treatment of continuous structures, limits, and geometric invariants
* **Scattering & Amplitudes:** Connections between discrete quantum models and continuous field theory
* **Spacetime & Geometry:** Mathematical framework for discrete and continuous spacetime structures

> [!IMPORTANT]
> **The Colimit Continuum Invariant:** Continuous boundaries, horizons, and physical limits in this repository are not derived via naive measure theory or analytical continuation. They are strictly constructed via **Categorical Direct Inductive Colimits**, pushing finite algebraic structures through the UHF $2^\infty$ boundary without analytical hallucination.

---

### How to Navigate

1. **Start with the Declaration Graph:**
   - Explore the central entry point: `InfoGeometry.All`
   - Inspect `AGENT_PROMPT.md` and `AGENTS.md` for operating principles
   - Check verified theorems: all proofs are kernel-checked, no unproven axioms

2. **For Agents & Large-Context LLMs:**
   - Ingest the codebase with your favorite coding agent (Claude, ChatGPT, Cursor, etc.)
   - Follow the structure in `InfoGeometry/` to trace mathematical development
   - Verified source edits are the source of truth

3. **Build & Verify Locally:**
   - Lean toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.28.1`)
   - Compile with:
     ```bash
     lake build InfoGeometry.All
     ```
   - *Critical:* **Never run `lake clean`**; preserve the `.olean` cache
   - All modules build cleanly from axiom-free foundations

4. **Contribute & Expand:**
   - Open theorems and missing proofs are frontiers, not blockers
   - Clone and develop your own extensions
   - The blueprint layer and declaration graph help track coverage

---

### Citation

If you use this repository for scientific reasoning, automated theorem proving, or formal verification research:

```bibtex
@software{goutev_infogeometry_2026,
  author    = {Goutev, Nikolay and Tonev, Dimitar},
  title     = {InfoGeometry: A Verified Lean 4 Formalization of Information Geometry and Quantum Foundations},
  year      = {2026},
  publisher = {GitHub},
  url       = {https://github.com/nickgou-nuke/info-geometry-lean},
  note      = {Living artifact of human-AI collaboration}
}
```

---

### License

This repository is licensed under the [Apache License 2.0](LICENSE).
