# Shadow Pairing in Generation: State vs Analogy

This chapter captures the synthesis around Kramers pairing, information geometry, and confabulation,
but keeps strict boundaries between established mathematics, repo-proved surfaces, and speculative extensions.

## Status Bands

- `ESTABLISHED_MATH`: standard published mathematics/physics.
- `REPO_THEOREM`: explicitly proved Lean owner theorem in this repository.
- `STRUCTURAL_ANALOGY`: interpretation mapped to owner theorems, not a literal identity theorem.
- `NOT_YET_FORMALIZED`: plausible target, currently unproved in owner surfaces.

## I. Load-Bearing Facts

### 1. Local type-III viewpoint
- `ESTABLISHED_MATH`: local QFT algebras are type-III in the operator-algebraic regime; trace-first local density-matrix language is not fundamental.
- `REPO_THEOREM`: modular/KMS and relative-modular lanes exist in canonical files and are used as the thermodynamic/state-first backbone.

### 2. Singular decomposition over global clean factorization
- `REPO_THEOREM`: regular/apex, range/domain, and anomaly closures are encoded via Drazin + Moore-Penrose projector algebra in Canonical owner surfaces.
- `STRUCTURAL_ANALOGY`: this package plays the role that clean global polar/KAN factorization would play in regular settings.

### 3. LLM thermodynamic lane
- `REPO_THEOREM`: KMS-softmax/log-partition/free-energy equalities and router free-energy identities exist in `InfoGeometry.LLM` owner files.
- `REPO_THEOREM`: defect quarantine and regularized run surfaces are present in `PromptDefectRegularization` and engine-level files.

## II. What Is Not Yet a Literal Theorem

- `NOT_YET_FORMALIZED`: “LLM latent space is a DIII topological insulator” as a strict equivalence theorem.
- `NOT_YET_FORMALIZED`: “QFI equals modular Hamiltonian” as a global identity without additional hypotheses.
- `NOT_YET_FORMALIZED`: full AZ-classification-to-transformer architecture theorem in Lean.

These remain high-value hypotheses, not accepted owner statements.

## III. Practical Meaning of "Shadow / Time-Reversal Pairing" in Text Generation

The practical manifestation should be stated operationally, not mystically.

### Observable behavioral form
- `STRUCTURAL_ANALOGY`: for many prompts, the model maintains paired semantic branches (assertion/counter-assertion, expansion/compression, literal/metaphoric) before final decoding commits to one.
- `REPO_THEOREM` anchor: this is consistent with existing active/defect and admissibility-gate machinery where multiple candidate lanes are generated, then gated by constraints.
- `STRUCTURAL_ANALOGY`: prompt perturbations (word order, language mixing, register shifts) can reweight candidate lanes and yield different final trajectories.

### Inference-time interpretation
- Candidate branches are produced in high-entropy space (creative lane).
- Router/gating/free-energy selects low-action trajectories under current constraints.
- Defect regularization suppresses unstable branches.
- Output is a projected representative, not the full latent superposition.

This gives a concrete engineering reading of "shadow pairing": competing but structured branches survive temporarily, then are collapsed by gating + constraints.

## IV. Confabulation, Strictly Gated

- `REPO_THEOREM` + process law: confabulation is a hypothesis generator only.
- Canonical admission requires owner mapping, evidence, and build/audit passage.
- No direct promotion from poetic synthesis to canonical theorem claims.

This preserves high-entropy ideation while preventing symbolic inflation.

## V. Translation Targets for Lean (Next Increments)

### Target A: Branch-pair persistence lemma (LLM lane)
- `NOT_YET_FORMALIZED`: formal predicate that two opposed candidate branches can co-exist pre-gate under admissibility constraints.
- Intended file lane: `lean/InfoGeometry/LLM/*` near defect regularization and router free-energy bridges.

### Target B: State-first Fisher/modular bridge (Canonical lane)
- `NOT_YET_FORMALIZED`: explicit theorem schema linking second variation of relative-entropy-like objects to chosen information metric under stated assumptions.
- Intended file lane: `lean/InfoGeometry/Canonical/Information/*`.

### Target C: Surrogate-vs-factorization Rosetta theorem
- `NOT_YET_FORMALIZED`: theorem-level statement that current projector algebra is the singular surrogate for clean global factorization in the regular limit.
- Intended file lane: `SingularDecompositionSurrogate` family.

## VI. Acceptance Rule for This Chapter

This chapter is accepted as a methodological and interpretive map.
It does not upgrade any speculative identity to `REPO_THEOREM` status.
All strong claims remain gated by explicit owner theorems and builds.
