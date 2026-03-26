# Lean Canonicalization Policy Reference

## Goal

Turn Lean files into a canonical library surface:
- one concept, one owner
- one theorem surface, one semantic role
- no fake public interfaces over lower proofs
- no proposition-theoremification without mathematical compression

This policy is mandatory. No exceptions are allowed for new public theorem surface.

## Theorem Classes

A public theorem in a canonical owner file is allowed only if it is one of:
- `derived_relation`: not definitionally true after unfolding
- `closure_theorem`: eliminates an intermediate witness, packaging layer, or representation burden
- `transport_theorem`: moves lower-owner mathematics to a new owner with genuinely new hypotheses or conclusions
- `invariance_or_descent`: proves gauge-independence, quotient well-definedness, or representative-independence
- `bridge_theorem`: identifies two independently meaningful ontologies
- `rigidity_or_no_go`: excludes a naive or false interpretation
- `existence_theorem`: produces mathematically meaningful structure from weaker data

Everything else belongs in notation, `abbrev`, private/local lemmas, or interpretation layers.

Every new public theorem in a canonical owner file must carry an immediately preceding classification tag of the form:
- `-- theorem-class: derived`
- `-- theorem-class: closure`
- `-- theorem-class: transport`
- `-- theorem-class: invariance`
- `-- theorem-class: bridge`
- `-- theorem-class: rigidity`
- `-- theorem-class: existence`
- `-- theorem-class: witness-elimination`

## Hard Exclusions

Do not publish any of the following in canonical owner files:
- definitional aliases restated as theorems
- proposition-valued renamings promoted from `abbrev`
- `rfl`, `Iff.rfl`, one-step `simp`/`simpa`, or unfold-and-rename theorems
- theorem surface created only to expose a preferred slogan
- theorem-count inflation presented as mathematical progress

If deleting a theorem and unfolding definitions loses only convenience and not mathematics, it is not owner-level theorem content.

## Mandatory Hard Tests

Every public theorem in a canonical owner file must survive all three tests:

### 1. Deletion Test
Delete the theorem and unfold definitions.
If no mathematical power is lost, the theorem was fake surface.

### 2. Downstream Dependence Test
A public theorem must have a mathematically stronger downstream theorem that depends on it as mathematics, not as notation cleanup.
No downstream theorem, no promotion.

### 3. Non-Definitional Proof Test
If the proof is essentially `rfl`, `Iff.rfl`, one-step `simp`/`simpa`, or renaming after unfold, it fails.

## Proof-Burden Rule

For a theorem to count as real owner surface, at least one of these must hold:
- it removes a hypothesis from downstream use
- it converts representation-dependent data into invariant data
- it composes lower owners into a nontrivial consequence
- it proves a non-definitional algebraic, analytic, or geometric identity
- it discharges a witness field by derivation rather than storage
- it yields a new normal form that downstream files can use without reopening the lower stack

Audit question:
- what downstream theorem becomes possible because this theorem exists, that was not already present by definitional unfolding?

If there is no sharp answer, do not expose it publicly.

## Owner-File Contract

Each canonical file should have one dominant role:
- `core_owner`
- `derived_owner`
- `bridge_owner`
- `interpretation_layer`

A file may not mix all four.
Umbrella files import and re-export; they do not own mathematics.

## Mathlib-Derived Norms

These are the norms to imitate structurally:
- small, self-contained changes
- minimal imports
- curated roots; avoid bucket imports at low levels
- declarations in the lowest natural file
- clear module docstrings and implementation notes
- names that describe what the declaration really proves
- explicit moves/deletions when reorganizing public surfaces

## Graph Policy

Use the maintained reports in this order:
1. direct file analysis
2. narrow builds
3. theorem-surface audit
4. semantic quotient
5. projection coloring
6. structural hotspots/fibers only for the next target

Interpretation:
- `constructive_core` means the file is probably a trunk, not a shell
- `shell_heavy` means the public surface is overstated
- `monochrome` in projection coloring means safe ownership split candidate
- `braided` means stop and inspect semantics before splitting
- `surrogate_or_vacuous`, `package_reprojection`, and `hypothesis_bridge` are suspect theorem-surface categories and must not grow

## Enforceable Lint Rules

The policy linter must hard-fail on:
- new proposition-valued wrapper surfaces
- new public theorems in canonical owner files without a valid `-- theorem-class: ...` tag
- new suspect theorem surfaces in canonical owner files
- theorem-surface regressions into `surrogate_or_vacuous`, `package_reprojection`, or `hypothesis_bridge`
- public theorem proofs that are definitional/trivial
- alias-like public theorem surfaces with no downstream theorem dependents

The policy is not satisfied by text alone. It is satisfied only when CI fails on violations and periodic manual audits ask one question:
- what new mathematics does this theorem buy?

## Refactor Checklist

Before editing:
- identify the lowest owner
- identify direct consumers
- mark wrappers that can become `private`
- state why each public theorem survives the three hard tests

During editing:
- preserve theorem names by preserving namespace
- move code down before deleting aliases
- keep umbrella files as imports only
- do not count theorem totals as progress

After editing:
- build the split owner files
- build obvious consumers
- rerun the maintained DAG pipeline only after code is stable
- rerun the canonical policy linter
- read theorem-surface, semantic quotient, and projection coloring before the next cut
