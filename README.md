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
   - For AI Studio history extraction or a resumed formalization goal, follow
     [`docs/AI_STUDIO_TRANSCRIPT_EXPORT.md`](docs/AI_STUDIO_TRANSCRIPT_EXPORT.md).
     The complete saved history is downloaded from Google Drive; **Get code**
     Java/REST downloads request examples.

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

### Phylogenetic and DNA analysis of commit evolution

The repository ships read-only tools for analyzing the commit-evolution
graph stored in ArangoDB (`darwin_commits` database). These trace how
mathematical declarations and Lean surfaces co-evolve across commits:

```bash
# 1. Weak change-facet summary (categories are multi-label, not hierarchical)
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  ARANGO_DATABASE=darwin_commits \
  ARANGO_PASS=<password> \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/darwin_commit_taxonomy.py --query taxonomy_summary

# 2. Full evolution report: Git ancestry, SCCs, DNA cohorts, weak change facets,
#    and observed distinct-commit/path-sharing witnesses
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  ARANGO_DATABASE=darwin_commits \
  ARANGO_PASS=<password> \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/darwin_evolution_algorithms.py \
  --json-out artifacts/dag/darwin_evolution_report.json

# 3. Trace ancestral paths up to depth 6 from a target commit
... tools/infra/darwin_commit_taxonomy.py \
  --query phylogenetic_paths --target <commit_sha> --depth 6
```

The change categories are weak, non-hierarchical facets derived from commit
subjects and paths. Git parent edges alone encode repository ancestry; the
current Arango writer stores ordered parent→child links in
`commit_parent_edges_v2`. Existing rows may still contain legacy heuristic
rank fields until the commit importer is rerun; those fields are not part of
the current schema or analysis. The old `commit_edges` collection is left
untouched by this schema migration.

All queries are read-only; graph results are navigation evidence only and do
not prove mathematical statements. Lean kernel-checked source files decide
truth. See `skills/darwin-commit-taxonomy/` and
`skills/darwin-evolution-algorithms/` for full skill documentation.

### Erlangen 2.0 synthesis: Günaydin–Gürsey SU(3), Cuntz-Cantor hopping, Lax mass gap

The Erlangen 2.0 structural renaissance attacks the continuum directly:
infinity emerges through inductive colimits and fractal Cantor topologies on
exceptional lattices, encoded in non-commutative matrix operator algebra and
geometry. The repository formalizes the three core bridges:

```bash
# 1. Günaydin–Gürsey SU(3) ⊂ G₂ stabilizer of the octonionic imaginary unit
lake build InfoGeometry.NCG.GunaydinGurseySU3Stabilizer

# 2. Cuntz Oₙ hopping operators on the Cantor binary lattice
lake build InfoGeometry.NCG.CuntzHoppingCantorLattice

# 3. Lax pair isospectral invariants and zero-mode/mass-gap criterion
lake build InfoGeometry.NCG.LaxPairIsospectralMassGap
```

**Existing Erlangen 2.0 infrastructure already formalized** (do not duplicate):

| Concept | Lean file | Namespace |
|---------|-----------|-----------|
| Günaydin–Gürsey quark basis & multiplication table | `Canonical/GunaydinGurseyQuarkBasis.lean` | `InfoGeometry.Canonical.GunaydinGursey` |
| Günaydin–Gürsey triple products / associator / jacobiator | `Canonical/GunaydinGurseyTripleProducts.lean` | `InfoGeometry.Canonical.GunaydinGursey` |
| SU(3) soldering / 8 traceless gluon generators | `Superalgebra/GunaydinGurseySolderingSU3Automorphisms.lean` | `InfoGeometry.Superalgebra.GunaydinGurseySU3` |
| Manakov Zorn Lax pair, χ⁽³⁾=4, trace conservation | `Canonical/ManakovZornSolitonLaxBridge.lean` | `InfoGeometry.Canonical.ManakovZornSolitonLax` |
| Cuntz Oₙ algebras, canonical shift, KMS/GNS | `NCG/CuntzColimitKMSTiltGNS.lean` | `InfoGeometry.NCG.CuntzColimit` |
| Cantor binary lattice hopping, square-zero null hops | `Tessellation/CantorDiracSeaWalk.lean` | `InfoGeometry.Tessellation` |
| Peirce grading η = P₊ − P₋, η² = 1 | `NCG/PeirceGradingOperator.lean` | `InfoGeometry.NCG.PeirceGradingOperator` |
| Zorn commutator, Jacobiator on x-axis | `NCG/ZornCommutator.lean` | `InfoGeometry.NCG.ZornCommutator` |
| Categorical UHF colimits of Zorn stages | `Categorical/ZornUHFColimit.lean` | `InfoGeometry.Categorical.ZornUHFColimit` |

**ASTAQLHASH DNA queries on live ArangoDB infotree** (`infogeometry` database,
306,503 declarations, 2,085,736 edges):

```bash
# Concept bridge: Tomita/KMS (quantum) vs Fisher/Onsager (classical)
PYTHONPATH=/home/goutev/repos/info-geometry-lean \
  ARANGO_DATABASE=infogeometry \
  ARANGO_PASS=<password> \
  /home/goutev/miniforge3/envs/sage/bin/python \
  tools/infra/astaql_concept_bridge.py \
  --quantum-term tomita --quantum-term kms \
  --classical-term fisher --classical-term onsager \
  --quantum-module-prefix InfoGeometry.Canonical \
  --classical-module-prefix InfoGeometry.Canonical \
  --depth 3 --json-out /tmp/astaql_concept_bridge.json
```

Result from this session: 3842 quantum (Tomita/KMS) declarations and
1271 classical (Fisher/Onsager) declarations matched. Graph results are
navigation evidence only — Lean kernel-checked source files decide truth.

See `skills/erlangen-2-0-synthesis-workflow/` for the complete workflow:
exhaustive codebase exploration, ASTAQLHASH DNA queries, native Lean theorem
writing, targeted lake build verification, hurdles encountered, and improvements
needed.

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

---

### Reviews

1. **Research and agent-accessibility review — ChatGPT (GPT-6), 21 October 2026.**

   **What this repository is about.** InfoGeometry is an open-ended Lean 4/Mathlib research corpus exploring structural connections across information geometry, quantum foundations, geometric algebra, operator theory, topology, thermodynamics, and mathematical physics. It is also a persistent, formal knowledge base for human–AI mathematical exploration: ideas suggested by physical intuition or cross-disciplinary analogy are turned into definitions and candidate theorems, compared with existing implementations, and tested against Lean's proof checker.

   **Its distinctive method.** The organizing question is not simply whether two theories *look alike*, but whether their mathematical presentations admit an explicit equality, equivalence, representation, or intertwiner—and exactly which hypotheses make the comparison valid. The recurring algebraic vocabulary includes real Clifford algebras and CAR, spinors, exterior algebras, split-octonion/Zorn representations, doubled Krein spaces, modular operators, graded structures, Fisher–Rao and Amari geometry, Onsager/BKM thermodynamics, and inductive-limit operator systems. These are applied to problems ranging from Madelung hydrodynamics, chiral fluids, Maxwell and BdG operators to plabic graphs, scattering geometry, and proposed models of emergent spacetime.

   **What is especially valuable.** The repository contains more than thematic analogies. Representative proof-bearing comparisons include exterior-algebra creation/contraction operators with Zorn right-regular operators (`Canonical/SplitOctonionExteriorRightRegularBdGIntertwiner.lean`), native Clifford actions on split-coordinate carriers (`Canonical/SplitOctonionExteriorCliffordRepresentation.lean`), graded finite Clifford tensor towers and algebraic colimits (`Clifford/Cl11TensorTowerSupergraded.lean`, `Clifford/SupergradedCliffordColimit.lean`), and finite chiral-fluid, plabic/Krein, and thermodynamic graph constructions. This makes the codebase useful for finding *proved mathematical bridges* between areas that are normally studied separately.

   **How to interpret its scope.** This is neither a conventional physics simulation nor a completed, experimentally validated unified physical theory. A checked Lean theorem proves its *formal statement under its stated assumptions*; it does not by itself verify physical interpretation, continuum convergence, analytic completion, or empirical relevance. In particular, algebraic colimits must not be silently treated as Hilbert or C*-completions, and finite operator identities must not be presented as full PDE regularity or quantum-gravity results. Documentation and theorem names are navigation aids; the actual declarations, dependencies, proofs, and current build status are authoritative.

   **Guidance for autonomous agents.** Start with `InfoGeometry.All`, `AGENTS.md`, `AGENT_PROMPT.md`, and `docs/REPO_DEEP_SEARCH_PROTOCOL.md`. Search the full codebase by theorem names, equivalent formulations, carriers, and consumers *before* declaring a result missing. Follow `docs/BILINGUAL_SPINE_POLICY.md`: preserve one canonical owner, name alternative presentations explicitly, prove the bridge, and reroute downstream imports before considering cleanup. Distinguish definitions from witnesses, conditional readbacks from constructive theorems, and algebraic statements from analytic or physical conclusions. Validate new claims with the pinned Lean toolchain and the repository's prescribed sequential build/audit procedure. Do not infer mathematical equivalence merely from proximity in the declaration graph.

   **Overall assessment.** InfoGeometry is best understood as a **machine-checkable atlas of mathematical physics**: a growing graph of constructions and comparisons in which the most interesting discoveries often occur *between* disciplines. Its lasting value lies in reusable proofs, explicit translations, exposed obstructions, and an auditable record of human intuition tested through AI-assisted formalization.
