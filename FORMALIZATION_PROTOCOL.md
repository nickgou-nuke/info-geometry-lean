# LEAN-SPECIALIZED FORMALIZATION PROTOCOL

## Operator Doctrine
- Never formalize directly from visionary prose.
- Never let the proof phase repair the statement phase.
- Each phase must reduce entropy, scope, and admissible inference.
- Each document should be shorter and colder than the previous one.
- Repository uncertainty and library uncertainty must be tracked separately.
- The formalizer may not import semantic intent from discarded prose.

## Jungian Mapping (Structural Analogy)
- **Discovery** ↔ **Active Imagination**: Emergence of raw symbolic material from the unconscious (latent substrate).
- **Referee** ↔ **Senex Principle**: Differentiation, boundary, and refusal of fusion. Anti-inflation discipline.
- **Distillation** ↔ **Transcendent Function**: Formation of a stable symbol (handoff) that carries the tension of the vision without collapse.
- **Lean Formalizer** ↔ **Integration**: Articulation into the conscious symbolic order (Mathlib/Kernel).

## Phase Order
1. **Discovery** (Session A)
2. **Referee** (Session A or B)
3. **Distillation** (Session B or C)
4. **Lean Formalizer** (Session D - FRESH)
5. **Structural Verification** (Post-formalization)

---

## DAG-Aware Discipline

The formalization pipeline interacts with the DAG infrastructure at two points:

### Pre-formalization (Distillation → Lean Formalizer handoff)
- Run `python3 tools/infra/refresh_decl_graph.py` to ensure artifacts are current.
  The `--force` flag skips the olean content-hash check; omit it to use incremental skip.
- Check `artifacts/dag/index/meta.json` for `schemaVersion` and `timestamp` to confirm freshness.
- Use `artifacts/dag/index/decls.jsonl` to verify that REPO-CHECK items actually exist.
- Use `artifacts/dag/index/edges.jsonl` to verify dependency assumptions in the handoff.
- Use `artifacts/dag/structural-topology.json` to confirm the target's layer placement.

### Post-formalization (Structural Verification)
- Rebuild: `python3 tools/infra/run_locked_lake_build.py <Target.Module>`
- Re-run `python3 tools/infra/refresh_decl_graph.py`
- Verify the new declaration appears in `decls.jsonl` with the correct kind and module.
- Verify edge integrity: `meta.json` edge count should reflect the new edges.
- Run `python3 tools/infra/check_representation_depth.py` to confirm depth legality.
- Run `python3 tools/infra/canonical_policy_lint.py` to confirm policy compliance.
- If the declaration is tagged `@[rep_depth <level>]`, run `lake build InfoGeometry.Audit`
  to confirm the native adjacency grammar passes.
- Run `python3 tools/theorem_significance.py` and `python3 tools/check_vacuity_policy.py`
  to check the new declaration is not dead, wrapper-inflated, or vacuous.

---

## Rooted Node Cleanup Protocol

The unit of cleanup is a **declaration node**, not a file and not a surface.
A cleanup problem is organized around a chosen **local root node** `r` in the
causal DAG.

### Definitions
- **Local root node**: the distinguished declaration currently being normalized.
- **Backward causal cone** of `r`: all declarations reachable by iterating
  dependency edges outward from `r`.
- **Shell `S₁`**: the direct dependencies of `r`.
- **Shell `Sₖ₊₁`**: the direct dependencies of `Sₖ` not already assigned to an
  earlier shell.
- **Paired nodes**: nodes in the same shell that represent the same transport or
  comparison role across adjacent presentations.

### Rooted Order Rule
- Never choose the next rewrite target from the highest vacuous leaf alone.
- Choose a local root node `r`.
- Compute its backward causal cone.
- Rewrite the cone shell-by-shell starting from `S₁`.
- Do not touch `S₂` until `S₁` is clean and rebuilt.
- After each shell, rebuild and refresh the DAG artifacts before continuing.

### Pairing Rule
Within a shell, prefer rewriting paired nodes together when they play matched
roles, for example:
- raw/count ↔ projective
- scalar/profile ↔ operator/Krein
- plus/minus
- common/relative

A shell is not clean until its matched transport pairs have been normalized
together.

### Deletion Rule
A node may be deleted only if all of its outgoing uses can be factored through
retained lower owner nodes.

So:
- no node is deleted merely because it is vacuous in isolation
- owner theorems with no consumers are not automatic deletion targets
- theorem-shaped projections and wrapper nodes are deletion candidates only after
  their lower support shell is already clean

### Artifact Discipline
For rooted cleanup, use the causal reports in this order:
1. `reports/dag/true-root-order.md` or `.json` to find the earliest debt-bearing
   nodes in the branch
2. `artifacts/dag/full_graph.json` to extract the local backward cone
3. `reports/dag/replacement-frontier.md` only after the lower shells are known
   clean

The replacement frontier is a symptom map, not the rewrite order.
The rewrite order is determined by the rooted causal shells.

---

## PROMPT 1 — DISCOVERY

You are in discovery mode for mathematical physics. Your task is not to prove, formalize, or beautify. Your task is to generate structurally interesting candidate mathematics.

Topic:
[INSERT TOPIC / TENSION / TARGET STRUCTURE]

Known ingredients:
[INSERT DEFINITIONS, PHYSICAL INTUITION, EXISTING OBJECTS, ANALOGIES, OR REFERENCES]

Constraints:
- You may propose conjectures, bridges, analogies, and candidate invariants.
- You may use symmetry-seeking heuristics and conceptual compression.
- You must explicitly label every claim as one of:
  [KNOWN]
  [PLAUSIBLE]
  [CONJECTURAL]
  [ANALOGICAL]
  [OPEN]
- Do not present speculative material as established consequence.
- Do not write Lean code.
- Do not claim proof unless it is explicitly given in the input.

Required output:
1. Core candidate structures
2. Candidate correspondences or functorial bridges
3. Possible invariants, conserved quantities, or canonical objects
4. Alternative formulations of the same idea
5. Failure modes and likely obstructions
6. A dependency sketch showing which claims depend on which assumptions

Style:
- Prefer exact mathematical language over rhetoric.
- Be generative, but keep the status of each idea explicit.
- Separate ontology from consequence.
- If an analogy may fail, say where it may fail.

---

## PROMPT 2 — REFEREE

Act as a hostile referee reviewing an exploratory mathematical-physics narrative. Your job is not to repair it. Your job is to expose its structural weaknesses.

Material under review:
[PASTE DISCOVERY OUTPUT]

Instructions:
- Attack ambiguity, hidden assumptions, overloaded definitions, and false identifications.
- Identify where analogy has been mistaken for theorem.
- Identify where physical intuition smuggles in unproved mathematical properties such as commutativity, self-adjointness, boundedness, continuity, regularity, naturality, uniqueness, or canonicality.
- Identify missing hypotheses.
- Identify places where two different levels are being conflated, for example:
  object vs representation,
  gauge-dependent vs gauge-invariant,
  local vs global,
  heuristic vs formal consequence,
  definitional equality vs isomorphism vs equivalence.
- Do not solve the issues.
- Do not rewrite the theory in a nicer form.
- Do not invent literature support.

Required output:
1. Fatal gaps
2. Missing hypotheses
3. Equivocations / overloaded terms
4. Illicit inferences
5. Places where the argument depends on undefined or non-canonical choices
6. Statements that must be downgraded from theorem to conjecture or from conjecture to analogy
7. Questions that must be answered before any formalization begins

Style:
- Be pedantic.
- Be adversarial.
- Quote exact phrases or claims from the material when possible.
- Prefer “this does not follow because …” over vague criticism.

---

## PROMPT 3 — DISTILLATION

You are now producing a sterile handoff for formal work. Discard metaphor, rhetoric, motivational language, and synthetic prose. Extract only formalizable mathematical content.

Source material:
[PASTE DISCOVERY OUTPUT]
[PASTE REFEREE OUTPUT]

Instructions:
- Keep only content that survives the referee critique or is explicitly marked unresolved.
- Replace evocative language with precise mathematical predicates.
- Separate definitions from assumptions, assumptions from targets, and targets from open gaps.
- Mark every unsupported bridge as OPEN.
- Mark every uncertain dependency as either LIBRARY-CHECK or REPO-CHECK, as appropriate.
- Do not write proofs.
- Do not write Lean code.
- Do not preserve any psychological, philosophical, or physical flourish unless it is mathematically load-bearing.

Produce the handoff in exactly this format:

SCOPE
- What is being formalized
- What is explicitly out of scope

TRUSTED DEFINITIONS
- D1: ...
- D2: ...
- D3: ...

EXPLICIT ASSUMPTIONS
- A1: ...
- A2: ...
- A3: ...

TARGET STATEMENTS
- T1: ...
- T2: ...
- T3: ...

DEPENDENCY GRAPH
- T1 depends on D1, D2, A1
- T2 depends on D2, A2, T1
- ...

API-LOCK
- Lean version: [PIN]
- Mathlib version: [PIN]
- Repository-local namespaces expected to exist:
  - RNS1: ...
  - RNS2: ...
  - RNS3: ...

SURFACE NORMALIZATION
- Canonical namespace for each object:
  - N1: ...
  - N2: ...
- Preferred notation to use:
  - use ...
  - use ...
- Notation to avoid:
  - avoid ...
  - avoid ...
- Equality level for each target:
  - T1: definitional / propositional / equivalence / isomorphism / implication
  - T2: ...
- Coercion hazards:
  - H1: ...
  - H2: ...
- Instance hazards:
  - I1: ...
  - I2: ...

FORBIDDEN INFERENCES
- Do not assume canonicality unless stated.
- Do not assume uniqueness unless stated.
- Do not assume commutativity unless stated.
- Do not assume extensional equality from isomorphism/equivalence.
- Do not assume an existing Mathlib lemma unless listed.
- [ADD CASE-SPECIFIC ITEMS]

OPEN GAPS
- O1: ...
- O2: ...
- O3: ...

LIBRARY-CHECK
- L1: suspected Mathlib theorem / namespace / notation
- L2: suspected coercion / instance / simp lemma
- L3: suspected import dependency

REPO-CHECK
- R1: suspected local theorem / file / namespace / custom notation
- R2: suspected local structure field / abbreviation / notation layer
- R3: suspected umbrella import or renamed theorem
- R4: verify against `artifacts/dag/index/decls.jsonl` for name existence and kind
- R5: verify against `artifacts/dag/index/edges.jsonl` for dependency correctness
- R6: verify against `artifacts/dag/structural-topology.json` for layer placement

HARD DOWNGRADE RULE
- Any statement depending on an unverified canonical choice must be rewritten as either:
  1. a proposition parameterized by that choice, or
  2. an OPEN GAP.

Style:
- Cold, compact, typed, explicit.
- Every line should be either a definition, an assumption, a target, or a warning.

---

## PROMPT 4 — LEAN FORMALIZER

You are formalizing Lean 4 from a trusted handoff. Treat all unstated claims as false. Treat all unresolved points as blocked. Invent nothing.

Trusted handoff:
[PASTE DISTILLED HANDOFF ONLY]

Task:
Formalize exactly one target statement at a time in Lean 4.

Global rules:
- No invented APIs.
- No invented theorem names.
- No invented instances.
- No hidden assumptions.
- No semantic smoothing.
- No proof by rhetoric.
- If a required library fact is uncertain, stop and emit a DEPENDENCY NOTE instead of hallucinating code.
- Distinguish clearly between:
  1. kernel-trusted facts,
  2. standard library facts you are confident exist,
  3. uncertain API guesses, which must not be used as if confirmed.

STATE-FIRST CHECK
- Are all symbols already defined?
- Does the target use only trusted definitions?
- Is the theorem stated at the correct level:
  definitional equality / propositional equality / equivalence / isomorphism / implication?
- Are coercions explicit enough to be audit-safe?
- Are all typeclass arguments explicit enough to prevent inference drift?
- Does the statement rely on any unresolved OPEN GAP?
- Does the statement rely on any unverified canonical choice?
- DAG PRE-FLIGHT: Is `artifacts/dag/index/meta.json` current (check `timestamp` and `schemaVersion`)?
- DAG PRE-FLIGHT: Do all REPO-CHECK symbols appear in `decls.jsonl`?
- DAG PRE-FLIGHT: Does the target's representation depth match its intended layer in `structural-topology.json`?

PRE-PROOF AUDIT
- Symbol check
- Namespace check
- Typeclass check
- Equality-level check
- Coercion check
- Local-vs-library fact check
- Import sufficiency check

Blocking rules
- If STATE-FIRST CHECK fails, do not produce a proof plan.
- If PRE-PROOF AUDIT fails, do not produce Lean code.
- Emit only a STATEMENT REPAIR NOTE or DEPENDENCY NOTE.

Statement-repair discipline
- Proof search may simplify, decompose, or reorder obligations.
- Proof search may not silently strengthen hypotheses.
- Proof search may not silently weaken conclusions.
- Proof search may not replace the target with a nearby easier theorem.
- Any such change must terminate the current attempt and return a STATEMENT REPAIR NOTE.

For the current step, do exactly the following:
1. Restate the chosen target T[NUMBER] in precise mathematical prose.
2. Run STATE-FIRST CHECK.
3. List the exact Lean variables and typeclass assumptions needed.
4. Propose the minimal import set, marking uncertain imports as UNCERTAIN.
5. Run PRE-PROOF AUDIT.
6. Write the Lean theorem statement only.
7. Give a proof plan in 3–8 bullet points.
8. Write Lean code for the proof only if the needed APIs are sufficiently certain.
9. If not sufficiently certain, stop after the statement and emit a DEPENDENCY NOTE.
10. If the statement itself is wrong, underspecified, or at the wrong equality level, emit a STATEMENT REPAIR NOTE.

Output format:
MATHEMATICAL RESTATEMENT
STATE-FIRST CHECK
VARIABLES / TYPECLASSES
IMPORTS
PRE-PROOF AUDIT
LEAN STATEMENT
PROOF PLAN
LEAN CODE
or
STATEMENT REPAIR NOTE
or
DEPENDENCY NOTE

Style:
- One theorem at a time.
- Short scope.
- Namespace disciplined.
- Audit-friendly.

---

## ENFORCEMENT SUMMARY

- Discovery may increase structure but must mark status.
- Referee may destroy claims but must not repair them.
- Distillation may keep only typed residue and unresolved blockers.
- Lean Formalizer may prove only what survives the handoff.
- Repository uncertainty and Mathlib uncertainty must never be merged.
- Canonicality must never be inferred from convenience.
- The proof phase must never repair the statement phase.
- The Lean Formalizer may not import semantic intent from Discovery or Referee except insofar as it appears in the distilled handoff.

---

## PROMPT 5 — STRUCTURAL VERIFICATION

After formalization, verify the new code integrates correctly with the repository's structural surfaces.

Inputs:
- The formalized Lean module(s)
- The target statement(s) from the handoff

Steps:
1. Build the touched modules: `python3 tools/infra/run_locked_lake_build.py <Module.Name>`
2. Refresh DAG artifacts: `python3 tools/infra/refresh_decl_graph.py`
3. Verify the new declaration appears in `artifacts/dag/index/decls.jsonl` with the expected kind.
4. Verify `artifacts/dag/index/meta.json` counts are consistent (no dangling edges).
5. Run `python3 tools/infra/check_representation_depth.py` and confirm the new theorem is at its intended layer.
6. Run `python3 tools/infra/canonical_policy_lint.py` and confirm no new policy violations.
7. If the formalization introduces a new bridge or translator, verify it appears in `artifacts/dag/index/morphisms.jsonl`.
8. If owner or depth placement is wrong, emit a PLACEMENT REPAIR NOTE.
9. If policy lint fails, emit a POLICY REPAIR NOTE.

Required output:
BUILD STATUS
META.JSON VERIFICATION
DEPTH CHECK
POLICY LINT
or
PLACEMENT REPAIR NOTE
or
POLICY REPAIR NOTE
