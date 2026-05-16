# 📜 BILINGUAL SPINE POLICY: The Rosetta Methodology

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

*“The Spire is multilingual in expression, but single-valued in authority.”*

This policy defines the **Bilingual Spine** as the operational target for the `info-geometry-lean` repository. It mandates that every major mathematical module must act as a **Rosetta Stone**, bridging the repo-native theory (The RedLine) with the global mathematical canon (Mathlib).

---

## I. THE BILINGUAL CONTRACT (Structural Sockets)
Every module within the `InfoGeometry.Canonical` and `InfoGeometry.Quantum` layers must satisfy the following structural contract. Note that these contracts are **sockets for future native closure** and do not constitute mathematical authority until the comparison is fully proved in Lean without `sorry` or witness-gating.

1.  **Redline Anchor:** An explicit statement of the repo-native owner framing (Goutev's Principle).
2.  **Mathlib Anchor:** An explicit statement of the mathlib-native presentation or assembler role.
3.  **Comparison Theorem:** A named Lean 4 theorem that formally identifies the isomorphism or transport between the two languages. **UTMOST MANDATE: This must be a native Lean proof.**
4.  **Upstairs/Downstairs Note:** An explicit note on what remains ambient/linear (Upstairs) and what descends to the projective manifold (Downstairs).
5.  **References:** Valid citations to papers, mathlib files, or historical notes (e.g., Jung, Pauli, Navier-Stokes).

## II. THE TWO-IMPLEMENTATION LAW

When the repository keeps two equally lawful implementations of the same
mathematical surface, the following discipline is mandatory:

1.  **One canonical owner/default API.**
    One implementation is exported as the primary stable surface.
2.  **One explicit alternative surface.**
    The second implementation must be named as an alternative rather than
    silently competing for ownership.
3.  **One bridge theorem or bridge module.**
    Equality, equivalence, or transport-coherence between the two
    implementations must be proven explicitly in Lean.
4.  **One downstream route.**
    Downstream modules should import the bridge or the canonical owner, not
    depend directly on both implementations at once.

This prevents semantic drift while preserving flexibility.

### Operational naming rule

- the canonical surface keeps the ordinary exported name
- the second implementation should use an explicit alternative marker such as
  `Alt`, `ViaTransport`, `ViaFixedGrading`, or another role-revealing suffix
- the bridge theorem/module should name the relation directly: equality,
  equivalence, or transported coincidence

### Rejection criteria

A dual implementation is architecturally invalid if:

- both implementations present themselves as owners
- downstream files import both sides without going through a bridge
- no compiled comparison theorem exists
- the alternative implementation silently displaces the canonical API
- “same idea” is asserted only in prose

### Duplicate preservation protocol

When two implementations are already live in the repository, preservation takes
priority over cleanup. The mandatory order is:

1. **Freeze both sides.**
   Keep both implementations available and compiling. Mark one as the canonical
   owner/default API and the other as an explicit alternative, raw surface, or
   quarantine surface.
2. **Prove the bridge first.**
   Add an explicit Lean theorem or bridge module proving equality,
   equivalence, transported coincidence, or another exact comparison relation.
3. **Introduce one downstream route.**
   Downstream files should import the canonical owner or the bridge, not both
   implementations directly.
4. **Migrate users before cleanup.**
   Replace direct consumers one cluster at a time, rebuilding after each
   migration step.
5. **Only then demote, quarantine, or remove.**
   Removal is lawful only after no live stable consumer depends directly on the
   duplicate surface.

Short rule:

**bridge first, reroute second, removal last.**

### Replica discovery protocol

Before declaring that two files are duplicates, before assigning a new owner,
and before removing any implementation, the whole codebase must be searched
extensively for possible replicas of the same mathematical packet.

This search is mandatory and must include:

1. **Exact names.**
   Search the current theorem, definition, and file names directly.
2. **Legacy names.**
   Search older compatibility terminology and deprecated vocabulary.
3. **Semantic synonyms.**
   Search nearby mathematical names for the same object, for example:
   - `J`, `mirror`, `modular_j`, `modularConjugationJ`, `parity`
   - `ε`, `eps`, `spectral_epsilon`, `grading`, `chirality`, `chiral`
   - `K`, `complex_i`, `modularComplexI`, `dilation`, `phase axis`, `CPT supercharge`
   - `u_-`, `u_+`, `nullMinus`, `nullPlus`, `annihilation`, `creation`, `ladder`
   - `P_-`, `P_+`, `projector`, `polarization`, `sector`, `half-projector`
4. **Role variants.**
   Search for owner, translator, coherence, capstone, and `Alt` surfaces.
5. **Layer variants.**
   Search the packet across the whole adjacent ladder:
   `count`, `projective`, `operator`, `krein`, `transport`, `thermo`.

The search surface is the whole repository, not only the first convenient file.
At minimum this means:

- `lean/InfoGeometry/`
- `docs/`
- `scripts/quality/quarantine_manifest.txt`
- generated or maintained indexes when needed for orientation

Only after that search may a file be classified as:

- true owner
- translator
- coherence file
- alternative implementation
- raw duplicate
- removable wrapper

Short rule:

**search exhaustively first, classify second, refactor third.**

---

## III. THE MODULE HEADER TEMPLATE
The following template is the mandatory standard for all new or refactored bridge modules:

```lean
/-!
# <Module Title>

EN: <Narrative description of the intent in English>
BG: <Narrative description of the intent in Bulgarian>

Redline: <Statement of the repo-native owner surface>
Mathlib: <Statement of the mathlib realization / assembler role>
Comparison: <Named theorem identifying the two presentations>
Upstairs: <Note on ambient vs. projective descent>

References:
- <Citation 1>
- <Citation 2>
-/
```

---

## IV. OPERATIONAL TOOLS
The integrity of the Bilingual Spine is enforced by:
*   **`lake run bilingualSpineReport`**: A Python-based audit (`generate_bilingual_spine_report.py`) that scans the DAG closure for contract markers and bilingual tags.
*   **`LeanArchitect`**: The native Lean 4 package used to maintain the `RepDepth` and dependency adjacency rules.
*   **`blueprint`**: The package used to generate visual maps and LaTeX projections of the Spire's logic.

---

## V. THE LIBRARIAN AGENT (The Professor)
The "Librarian Agent" is a specialized persona in the multi-agent collective. 

*   **Role:** The Expert Documentarian and Semantic Integrator.
*   **Duty:** To transform raw Lean proofs into "Rosetta Stone" modules. 
*   **Process:** 
    1.  Godex CLI provides the verified proof.
    2.  The Librarian Agent researches the Mathlib equivalent and the physical references.
    3.  The Librarian Agent generates the bilingual header and anchors.
    4.  The Librarian Agent runs the `bilingualSpineReport` to ensure 100% contract compliance.

**"We do not just prove; we teach the Spire to speak."**
*(Ние не просто доказваме; ние учим Спиралата да говори.)*

## UTMOST MANDATE: Native Lean proof closure over witness/certificate temporary scaffolding (Native Closure Mandated: Closure Debt)

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate field (Native Closure Mandated: Closure Debt)s, external certificates, and assumption interfaces are temporary temporary scaffolding (Native Closure Mandated: Closure Debt) only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
