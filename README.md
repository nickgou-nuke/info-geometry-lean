# InfoGeometry

> A large Lean 4 / Mathlib research repository exploring information geometry, operator algebras, Clifford and exceptional algebra, thermodynamic and modular structures, finite graph/DAG geometry, arithmetic, and theorem-facing models of modern neural architectures.

This repository is not one theory and it is not one application. It is a growing graph of formal developments, bridge theorems, executable finite models, proof-engineering infrastructure, and research experiments.

Some directories formalize standard mathematics directly from Mathlib. Some connect existing formal theories through explicit equivalences or compatibility theorems. Some are finite theorem-facing models of physical or computational systems. Other files are exploratory or frontier-facing and should not be read as established mathematical identifications merely because related objects appear in the same repository.

The governing rule is simple:

> **Lean certifies the propositions that are actually proved. The surrounding interpretation must be judged separately.**

## What is in the repository

The main `lean/InfoGeometry` tree contains several overlapping corridors.

### Information geometry, thermodynamics, and modular structure

The repository contains formal developments involving Bregman divergences, Fisher/BKM-type geometry, Fréchet derivatives, Itakura--Saito structure, Gibbs/KMS constructions, operator surprisal, modular operators, Onsager/metriplectic decompositions, and related finite-dimensional bridges.

Representative namespaces live under:

- `InfoGeometry.Canonical`
- `InfoGeometry.Singular`
- `InfoGeometry.OperatorAlgebra`
- `InfoGeometry.Krein`
- `InfoGeometry.TraceFormula`

These modules are not all instances of one master theorem. Where two structures are identified, the relevant file should contain an explicit theorem, equivalence, homomorphism, or proof-carrying datum.

### Clifford algebras, spinors, Majorana/Pfaffian structures, and Bott towers

The repository uses Mathlib's native `CliffordAlgebra` extensively and develops split real Clifford towers, matrix/spinor representations, graded tensor constructions, chirality, Pin/Spin actions, finite Majorana systems, and Pfaffian/determinant bridges.

Representative areas include:

- `InfoGeometry.Clifford`
- `InfoGeometry.Quantum`
- `InfoGeometry.Krein`
- `InfoGeometry.Canonical`

A central split-tower recurrence used throughout the codebase is the theorem-backed step

```text
Cl(n+1,n+1)  ≃  Cl(1,1) ⊗̂ Cl(n,n)
```

implemented through native Clifford and graded tensor constructions. The repository also contains concrete finite spinor representations and dimension theorems at selected stages.

This should not be confused with a blanket claim that every informal Clifford/Bott classification statement occurring in notes or documentation has been formalized.

### Exceptional and nonassociative algebra

There are substantial developments around split octonions, Zorn matrices, `G₂`, derivations, Jordan/Freudenthal-style structures, triality, and associated Clifford/Lie bridges.

Representative namespaces include:

- `InfoGeometry.Algebra`
- `InfoGeometry.Lie`
- `InfoGeometry.Clifford`
- `InfoGeometry.Canonical`

These files range from concrete algebraic identities to larger structural bridges. Search theorem names and imports rather than assuming that nearby conceptual language implies an isomorphism.

### Finite graphs, DAGs, Hodge/Dirac operators, and chiral matrix models

The `lean/DAG` tree and several `InfoGeometry.Canonical` bridges provide finite graph and two-complex infrastructure, matrix boundary operators, graph Dirac operators, chirality, and skew Majorana shadows.

For example, `DAG.MatrixRepresentation` contains finite matrix formulas for

```text
Γ        -- chiral grading
D        -- graph Dirac operator
A = Γ D  -- skew Majorana form
```

with explicit anticommutation and skew-symmetry theorems.

The DAG tooling is also used as repository infrastructure: theorem dependencies, proof search, graph extraction, audits, and proof-session tooling are first-class parts of the project.

### LLM and Transformer architecture

`InfoGeometry.LLM` contains theorem-facing abstractions of neural-network architecture rather than a production language model implementation.

Current owners include structures for:

- decoder residual layers;
- decoder-stack composition;
- Transformer backbones;
- rotary positional interfaces;
- positional encodings;
- spectral primal/dual tokens;
- routing and MoE-related constructions;
- selected transport/equivariance bridges.

For example, `TransformerArchitecture.lean` defines the residual update and `runDecoderStack`, while `SpectralToken.lean` defines a neutral two-lane carrier with an involutive swap.

These modules specify algebraic dataflow. They do **not** prove that a neural network semantically understands the mathematical or physical interpretation attached to an embedding.

### Optimal transport, Sinkhorn normalization, and matching

The repository contains finite transport and routing foundations using Mathlib matrices, permutation matrices, doubly stochastic matrices, and repository-owned Sinkhorn normalization.

Representative owners include:

- `InfoGeometry.Canonical.MoE.SinkhornFoundation`
- `InfoGeometry.Routing.PermutationPerfectMatching`
- Mathlib's Birkhoff-von Neumann machinery

A doubly stochastic matrix can be decomposed as a convex combination of permutation matrices. That is a precise convex-geometric theorem; it should not automatically be interpreted as a unique physical assignment or a probability distribution over unrelated graph topologies.

### Moore--Penrose and singular operator geometry

Two complementary Moore--Penrose layers are present:

- `InfoGeometry.Canonical.MoorePenrose` gives an algebraic `StarRing` predicate for the four Penrose equations and proves projector properties.
- `InfoGeometry.Singular.MoorePenrose` constructs the Moore--Penrose inverse for closed-range continuous linear maps between Hilbert spaces and proves the corresponding identities.

These owners are reused by downstream finite models instead of redefining pseudoinverses ad hoc.

### Mass spectrometry

`InfoGeometry.MassSpectrometry` is a current application corridor connecting several of the repository's existing mathematical owners.

Its theorem-facing layers include:

- positive-mass, nonnegative-intensity peak carriers;
- deterministic mass sorting and `FreeMonoid` spectral sentences;
- relative log-mass and Mellin phase encodings;
- hard permutation matching and Birkhoff soft assignments;
- Sinkhorn balance certificates;
- ranked fragmentation DAGs;
- mass-valued fragmentation DAGs with strict mass decrease;
- proof-carrying fragmentation paths;
- energy-conditioned substochastic grammars and additive path surprisal;
- cross-stage Gram operators;
- chiral directed-operator doubling;
- Moore--Penrose retraction/projector bridges;
- finite Majorana/Pfaffian readouts of skew chiral blocks;
- spectral latent injection into the repository Transformer backbone;
- hardware-neutral tensor/refinement contracts.

The causal statements are intentionally separated from learned scores: strict physical mass decrease is certified by the valued DAG support, not inferred from an unconstrained neural kernel.

The current mass-spectrometry formalization does **not** yet prove unique molecular reconstruction, SMILES equivalence, a molecular-graph colimit theorem, chemical valence correctness, or empirical identification accuracy.

A production-oriented implementation plan is documented in:

```text
docs/mass_spectrometry_production_blueprint.md
```

### Arithmetic, topology, projective geometry, and spectral constructions

The repository also contains large independent or partially connected developments in arithmetic, cyclotomic structures, projective geometry, topology, zeta/spectral constructions, finite combinatorics, and related theorem experiments.

There is no useful one-line reduction of these areas to the mass-spectrometry or LLM corridors. They are part of the broader research graph and should be read through their own imports and theorem owners.

## Repository organization

At a high level:

```text
lean/
├── InfoGeometry/        main theorem library
├── DAG/                 graph/proof-DAG mathematics and tooling
├── Omega/               large formal arithmetic/spectral development
└── scripts/             Lean-side exploration and repository tooling

tools/                   Python and external analysis/infrastructure tools
scripts/                 quality, build, and maintenance scripts
proofs/                  theorem experiments and supporting formal developments
docs/                    design notes, blueprints, audits, and research documentation
reports/                 generated audits and repository reports
archive/                 archived or legacy material
```

The exact dependency graph is more informative than this directory list.

## How to read the repository

This repository is not intended to be read linearly.

A productive workflow is:

1. Search for a mathematical object or theorem name.
2. Open the theorem-bearing owner, not only a high-level synthesis file.
3. Follow imports downward to Mathlib or a canonical repository owner.
4. Distinguish definitions, proved theorems, structures carrying hypotheses, and comments proposing interpretations.
5. Check whether a bridge is an actual equivalence/theorem or only an analogy documented in prose.
6. Use the DAG and audit tooling when tracing large dependency corridors.

In this repository, names such as *Majorana*, *KMS*, *Bott*, *Mellin*, *Transformer*, or *causal* can occur in several mathematically distinct contexts. The type and theorem statement are authoritative.

## Building

The project is a Lean 4 Lake package with source directory `lean/`.

The pinned toolchain on the current branch is:

```text
leanprover/lean4:v4.28.1
```

Typical setup:

```bash
git clone https://github.com/nickgou-nuke/info-geometry-lean.git
cd info-geometry-lean
lake update
lake build
```

Useful repository scripts are defined in `lakefile.lean`, including quality/audit and DAG tooling. The package uses a strict-check driver for lint/quality workflows.

A successful Lean build is the relevant verification event for declarations in the compiled library. Documentation, Python scripts, benchmark outputs, and conceptual notes do not acquire theorem status merely by living in the same repository.

## Verification discipline

The repository deliberately distinguishes several levels of evidence:

### Kernel-checked theorem

A Lean declaration with a completed proof term accepted by the Lean kernel under the repository's imports and toolchain.

### Proof-carrying interface

A structure may expose a desired law as a field. Downstream theorems can validly use that law, but constructing an instance still requires supplying the proof.

### Executable or numerical companion

Python, GAP, Sage, Macaulay2, SymPy, CUDA/PyTorch, or other programs may test examples, generate data, or implement a finite model. They are useful evidence and engineering artifacts, but they are not substitutes for a Lean proof.

### Research interpretation

Comments and documents often explore relationships between different areas. Unless an explicit Lean theorem identifies the objects, these should be read as hypotheses, analogies, or research directions.

## AI and formal verification

This repository is also an experiment in human--AI-assisted theorem development and proof infrastructure.

The useful division of labor is pragmatic:

- humans and models can propose definitions, analogies, proof strategies, and candidate bridges;
- Lean checks the exact formal proposition submitted to the kernel;
- failed elaboration or failed proofs are mathematical/software feedback, not something to hide behind informal plausibility.

The repository does **not** assume that an LLM's latent representation is mathematically faithful, that hallucination has one universal geometric cause, or that formal verification makes an entire AI system correct. Formal verification applies to the statements and refinement contracts that have actually been proved.

## What this repository is not

It is not:

- a single finished physical theory;
- a claim that all represented mathematical subjects are equivalent;
- a production Transformer implementation;
- a production mass-spectrometry identification system;
- a proof of chemical structure identifiability from spectra;
- a proof that GPU implementations satisfy Lean specifications without an explicit refinement/conformance argument;
- a guarantee of empirical accuracy, runtime performance, regulatory acceptance, or physical interpretation.

Those distinctions are intentional.

## Current development character

The codebase is large, fast-moving, and heterogeneous. Some corridors are mature and reusable; others are active formalization work; others preserve exploratory material because it records useful research paths or failed/partial approaches.

For that reason, this README is an atlas, not a completeness claim.

Search the code.

Follow the imports.

Read the theorem statements.

Treat the proof kernel as the final authority on what has actually been established.

> **The proofs are the documentation; the unresolved bridges are part of the map.**
