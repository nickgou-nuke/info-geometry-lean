# Epistemic Compiler Field Protocol

This is the practical companion to
[`skills/epistemic-compilation/SKILL.md`](../skills/epistemic-compilation/SKILL.md)
and `docs/ALCHEMICAL_QMS_SOP.md`. It gives a repeatable working format for
turning mixed prose and mathematics into repository-grounded Lean work. It does
not replace the canonical agent pipeline, QMS gates, or owner-file authority.

## The four work stages

| Stage | Work product | Completion test |
| --- | --- | --- |
| **Solve** | Source-linked atomic claim ledger | Every equation has a carrier, definitions, hypotheses, and status; narrative interpretation is marked separately. |
| **Coniunctio** | Ground-truth theorem contract | The proposed objects are tied to actual owner declarations, and every bridge between carriers is explicit. |
| **Causal poset** | Dependency DAG | Every edge represents a real proof dependency; no edge is justified by metaphor or name similarity. |
| **Coagula** | Small owner-aligned Lean change and verification record | The exact Lean proposition compiles, passes applicable gates, and is reported at that scope. |

These labels organize a workflow. They do not imply that a candidate claim is
true or that the stages themselves establish a mathematical theorem.

## 1. Solve: make an atomic claim ledger

Preserve the original prompt or source and identify its location. Split it into
claims small enough to check independently. Keep interpretations in a separate
column rather than silently translating them into theorems.

| ID | Source reference | Candidate statement | Required hypotheses | Kind | Status / next action |
| --- | --- | --- | --- | --- | --- |
| C1 | `source.md:12` | `P * P = P` | `P : B` | definition / assumption | Find owner or state as input |
| C2 | `source.md:18` | `δ(P + X) = ...` | associative ring; definitions of `δ` | theorem candidate | Expand and check signs/order |
| C3 | `source.md:21` | “measures awareness” | interpretation | narrative | Do not include in Lean theorem type |

Use one status per claim: `owner-backed`, `candidate`, `conditional`,
`counterexample`, `open debt`, or `interpretation-only`. A failed identity is a
useful result: record the smallest counterexample or corrected formula and
update dependent claims before proceeding.

## 2. Coniunctio: write the theorem contract

Before editing Lean, fill in this short contract. Use the repository’s fuller
ground-truth contract or formal-intent envelope when the task requires it.

```text
Claim ID(s):
Source and exact passage:
Carrier and typeclass assumptions:
Operations and conventions (including multiplication/composition order):
Exact candidate Lean proposition:
Existing owner declarations and their exact statements:
Required hypotheses not supplied by the source:
Smallest owner-aligned gap:
Interpretations or stronger claims explicitly excluded:
Verification target (file/module and applicable gates):
```

Search the actual repository before creating definitions. Trace owner imports,
theorem bodies, instances, and relevant dependents. Distinguish “not found in
this file/search” from “does not exist in the repository.” When two structures
are connected by an analogy, specify a map and prove the required compatibility
laws before treating them as one carrier.

## 3. Causal poset: order only proof dependencies

Build the dependency order from the statements Lean will use, not from the
story’s chronology. A compact format is enough:

```text
N1: ring bracket/defect identities
N2: idempotent and complementary-idempotent laws       depends on N1
N3: Peirce corner support and annihilation              depends on N2
N4: composite operator identity                        depends on N1, N3
N5: interpretation or external-system comparison       requires a separate bridge
```

An edge `Ni → Nj` means a proof of `Nj` invokes or derives a theorem from
`Ni`. Mark conjectural and interpretation-only nodes outside the proved DAG.
Do not infer a topology, Hodge theory, probability model, physical law, or
repository fact from an algebraic resemblance alone.

## 4. Coagula: implement the smallest useful Lean slice

- Prefer an existing owner module and reusable helper lemmas over a parallel
  namespace or monolithic synthesis theorem.
- Keep the actual carrier and assumptions visible in theorem signatures.
  `[Ring B]` is not interchangeable with `[StarRing B]`, a matrix algebra, a
  topological algebra, or a concrete operator representation.
- Keep multiplication order explicit. In noncommutative proofs, check signs
  and factor order before choosing tactics.
- Use `abel` only for the additive normalization remaining after valid
  multiplicative rewrites. It does not prove noncommutative product identities.
- Do not encode prose meanings in theorem names or docstrings as if Lean had
  verified those interpretations.
- Keep proofs complete: no `sorry`, `admit`, custom axioms, vacuous hypotheses,
  or proxy structures that merely store the desired result.

## 5. Verification and preservation

Follow `AGENTS.md` and `docs/CANONICAL_AGENT_PIPELINE.md` for repository
commands. In particular, inspect for active compiler work before verification,
never run `lake clean`, and use the shared locked build wrapper for Lake builds.
Run the narrowest relevant kernel/build check, then applicable placeholder,
axiom, semantic-vacuity, and staged-proof gates. Stage edits immediately as
required by repository policy. Do not claim a subsystem or full-repository
build passed when only a narrow module was checked.

Record results in this form:

```text
Disposition: [kernel_verified | accepted_limited_scope | bucket_2_conditional |
              bucket_3_open_debt | countermodel_found]
Lean proposition proved:
Owner file and declaration:
Kernel/build command and result:
Gate results:
Assumptions and axiom footprint:
Interpretations not established:
Remaining debt:
```

## Copy-ready task prompt

```text
Apply the repository's epistemic-compilation skill to the supplied material.
Preserve its provenance. Produce an atomic claim ledger, classify theorem
candidates separately from interpretations, search and read the actual Lean
owners, and write a ground-truth theorem contract. Correct false signs or
overstrong claims before coding. Order only genuine proof dependencies in a
causal DAG. Reuse the smallest existing owner surface and formalize complete
Lean proofs with the actual carrier and hypotheses. Do not substitute scalar,
diagonal, or commuting models for a requested noncommutative result. Verify
with the repository's required kernel/build and quality gates, then report the
exact proved scope and remaining debt. Give an auditable summary, not hidden
chain-of-thought.
```

## Worked miniature: Peirce observation

For a prompt proposing an idempotent cut, the ledger can separate:

1. `P * P = P`: an explicit hypothesis or an owner theorem.
2. `P * X * P + P * X * (1-P) + (1-P) * X * P + (1-P) * X * (1-P) = X`:
   an algebraic theorem candidate over a ring.
3. “This is awareness”: an interpretation, not a consequence of the Lean
   equation.

The causal order is ring operations → complementary idempotent laws → four
Peirce blocks → any composite measurement or defect statement. If the repo
already owns those facts, the practical task is to reuse and cite them rather
than add duplicate definitions.
