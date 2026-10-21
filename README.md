<!-- repository-context-rule -->
> **Repository grounding:** For repository work, the checked-out codebase is
> the context. Search existing implementation and trace its real definitions,
> imports, instances, theorems, and uses before declaring a structure missing
> or incorrect. A finding in one file is not a repo-wide finding. See
> [`docs/REPO_DEEP_SEARCH_PROTOCOL.md`](docs/REPO_DEEP_SEARCH_PROTOCOL.md).

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
>
> **The Kernel Source-of-Truth & Operator Wavefront Law (OpenGauss Protocol QMS-SOP-IAA-001):**
> 1. **Lean owner files decide truth:** Only kernel-checked source edits count. Graph tools, transcripts, and CAS outputs are navigation aids only.
> 2. **Zero fake proofs:** Exactly 0 `sorry`, 0 `admit`, 0 custom axioms; strictly foundational Lean 4 axioms (`[propext, Classical.choice, Quot.sound]`).
> 3. **Trap T16 Permanent Prohibition (Zero Scalar Toy Proxies):** Non-commutative operator algebras and infinite-dimensional quantum structures must never be replaced by coordinate/scalar surrogates.
> 4. **Operator Wavefront Duality:** Retarded/Advanced waves are operator wavefront shells $\mathcal{O}_{\text{foc}}(\tau) = \sigma_{-\tau}(\mathcal{O}_0)$ and $\mathcal{O}_{\text{defoc}}(\tau) = \sigma_{+\tau}(\mathcal{O}_0')$ in von Neumann algebras $\mathcal{M}$ intertwined by Tomita modular conjugation $J \mathcal{O}_{\text{foc}}(\tau) J = \mathcal{O}_{\text{defoc}}(-\tau)$, Klein glide reflection $\mathcal{G}_{\text{Klein}}(\mathcal{O}_{\text{foc}}(\tau)) = \mathcal{O}_{\text{defoc}}(-\tau)$, KMS thermal periodicity $\tau \to \tau + i\beta$, and chiral ideal splits $P_L \leftrightarrow P_R$.
> 5. **Sequential Build Discipline:** Never run `lake clean`. Acquire `/tmp/info-geometry-build.lock` via `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock`. Proactively stage all edits with `git add -A`.

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
   - Lean toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.34.1`)
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

### Read-only concept-bridge navigation

For a bounded comparison of concept corridors in the compiler-backed
declaration DAG, use:

```bash
python3 tools/infra/astaql_concept_bridge.py \
  --quantum-term tomita --quantum-term kms \
  --classical-term fisher --classical-term onsager \
  --depth 3 --json-out /tmp/astaql_concept_bridge.json
```

This queries `decls` and `edges` read-only. Shared prerequisites are
navigation evidence only. Read owner source and prove every claimed
comparison in Lean; do not infer semantic edges such as `INHERITS_FROM` or
`HAS_PROPERTY` from graph proximity.

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
