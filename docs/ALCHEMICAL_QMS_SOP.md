# QMS-SOP-ALC-001 — Semantic Normalization and Kernel Validation QMS

Subtitle: Confabulation-to-Mathlib transmutation procedure.

Latent mathematical language is not refined into truth. It is refined into
typed claims. Only the Lean kernel upgrades typed claims into verified
mathematics.

Status: controlled SOP
Document ID: QMS-SOP-ALC-001
Version: 4.1
Effective date: 2026-07-04
Scope: `info-geometry-lean` informal/speculative mathematical intake, semantic
normalization, CAS evidence, Lean/mathlib translation, independent audit, and
acceptance.
Standard posture: ISO 9001:2015-inspired / ISO 9001-aligned internal
quality-management workflow, including awareness of ISO 9001:2015/Amd 1:2024
where present-day alignment language is used. This repository does not claim
external ISO certification, accreditation, registration, or third-party
compliance from this document.

Controlled-document metadata:

- Document owner: repository maintainers / QMS orchestrator role.
- Approval authority: repository owner or delegated theorem-QA lead.
- Review interval: quarterly or on major Lean/mathlib/toolchain/pipeline change.
- Supersedes: QMS-SOP-ALC-001 v4.0.
- Controlled location: `docs/ALCHEMICAL_QMS_SOP.md`.
- Record class: QMS procedure.
- Promotion status: controlled.
- Last QA disposition: qms_document_controlled.

Revision history:

| Version | Date | Change summary | Author role | Reviewer role | QA disposition |
|---|---|---|---|---|---|
| 4.0 | 2026-07-04 | Added role separation, colimit gates, CAPA, QA gates, and ISO-inspired alignment. | Orchestrator/G-A | A-A | ACCEPTED_WITH_LIMITED_SCOPE before tracking |
| 4.1 | 2026-07-04 | Renamed formal record to semantic normalization/kernel validation; added intent envelope, risk classes, disjoint status tags, toolchain fingerprint, theorem-name honesty, QA tool-existence checks, and quick operator gate. | Orchestrator/G-A | A-A PASS | QA-A ACCEPTED |

ISO 9001:2015 alignment map, internal only:

- 7.5 — documented information and controlled records;
- 8.1 — operational planning and control;
- 8.5.1 — controlled production and service provision;
- 8.6 — release of products and services;
- 8.7 — control of nonconforming outputs;
- 9.1 — monitoring, measurement, analysis, and evaluation;
- 10.2 — nonconformity and corrective action / CAPA.

## 0. Purpose

This SOP governs the controlled conversion of informal, speculative, latent, or
model-generated mathematical content into Lean 4 artifacts classified as
definition-backed, theorem-backed, model-assumption-backed, computational
witness, external-evidence, conjectural-scaffold, or documentation-only. No
artifact may be marked theorem-verified unless it passes sterile compilation,
placeholder scan, axiom audit, and style review in its stated scope.

The central control principle is independence:

- generation is not audit;
- audit is not acceptance;
- acceptance is not promotion authority unless it is backed by kernel/build/audit output;
- external CAS/proof-assistant evidence is evidence, not Lean closure;
- AST/AQL/hash/DAG artifacts are navigation and traceability evidence, not proof.

This SOP exists to prevent these recurrent nonconformities:

1. prose or symbolic resonance presented as theorem closure;
2. finite CAS evidence promoted to direct-limit, inverse-limit,
   filtered-colimit, topological, analytic, or category-level closure;
3. matrix-level evidence replacing existing categorical/colimit owner surfaces;
4. full Zorn/split-octonion element commutators incorrectly packaged as Lie algebra instances;
5. `sorry`, witness packets, `_True`, `_holds`, `_certificate`, `Prop := True`, quotient collapse, or `Classical.choice`-driven existential extraction disguised as constructive proof;
6. an authoring agent accepting its own output.

## 1. Authority hierarchy

For theorem-bearing claims, authority is ordered as follows:

1. Lean kernel-checked source in the current checkout.
2. `lake env lean <file>` and narrow `lake build <Module>` output.
3. Existing owner theorem surfaces imported by the target file.
4. Mathlib theorem roots explicitly named or discoverable through source imports.
5. AST/AQL/hash/DAG/Arango/LeanTrail navigation artifacts.
6. CAS or external proof-assistant evidence with explicit finite/conditional scope.
7. Literature, notes, black books, prompts, chat transcripts, and symbolic narratives.

Only levels 1–4 can promote a Lean theorem claim. Levels 5–7 can generate tasks, evidence, or hypotheses, but cannot close theorem debt.

## 2. Related controlled documents

Operators and agents must read the relevant documents before task execution:

- `docs/CANONICAL_AGENT_PIPELINE.md` — repo-level routing authority.
- `docs/HIVE_AGENT_COMMANDMENTS.md` — compact operational law.
- `docs/REPO_DEEP_SEARCH_PROTOCOL.md` — owner-first source search protocol.
- `docs/AUTONOMOUS_PROOF_SOP.md` — autonomous proof-chain authority and BUCKET classification.
- `docs/GOAL_LOOP_SOP.md` — standing-goal loop; judge separation.
- `docs/MISSION_LOOP_SOP.md` — native closure-debt mission loop.
- `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` — categorical/Grothendieck owner surfaces; matrix files are instances, not replacements.
- `docs/InductionSystematics.md` — finite-stage induction, algebraic direct limits, and the rule that categorical colimits require actual carriers and maps.
- `ASTAQLHASH-HOWTO.md` — AST/AQL/hash/DAG navigation and proof-boundary discipline.
- `docs/aubert-plymen-multisystem-sop.md` — worked multi-system formalization pattern.

If this SOP conflicts with a kernel-checked owner theorem, the owner theorem wins. If it conflicts with repo safety policy, the safety policy wins.

## 3. Terms and classifications

### 3.1 Latent bundle

A user-provided symbolic, speculative, or confabulated mathematical bundle. It may contain real theorem seeds, false analogies, overclaims, and poetic language.

### 3.2 Mathlogos translation

The process of extracting a theorem-safe statement from a latent bundle, grounding it in mathlib/repo owner surfaces, and translating it into Lean code or an explicit open debt.

### 3.3 BUCKET classification

Use the repo-wide buckets:

- BUCKET 1: kernel-checked native theorem in its honest scope.
- BUCKET 2: conditional theorem from explicit hypotheses or witnesses.
- BUCKET 3: open closure debt, external evidence only, or claim beyond current owner surfaces.

### 3.4 Nonconformance

Any mismatch between claimed scope and verified authority, including but not limited to:

- compile-green but theorem-strength false;
- finite evidence reported as direct-limit, inverse-limit, filtered-colimit,
  topological, analytic, or global result;
- topological/quotient/group classification claimed from coordinate matrix facts;
- proof debt hidden in structure fields or quotient relations;
- unrefreshed/stale DAG/hash artifact used as current evidence;
- same agent producing and accepting a deliverable.

### 3.5 Colimit and staged-system language control

The repository does not accept "infinite" as a standalone proof word. New
theorem-bearing work must use one of these exact scopes:

- finite stage;
- finite iteration indexed by `Nat`;
- staged theorem transported by explicit successor maps;
- algebraic direct limit with a `DirectedSystem`, `DirectLimit`, canonical
  injections, and compatibility laws;
- categorical colimit through `CategoryTheory.Limits.colimit` and a proved
  cocone/universal property;
- inverse limit through an owner file that actually builds the inverse system;
- analytic or topological completion only in a file that imports and proves the
  required topology/convergence structures.

Any generated text containing "infinite", "thermodynamic limit", "continuum
limit", "global colimit", or "completion" must be downgraded to BUCKET 3 unless
the candidate artifact names the exact owner theorem and import path carrying
that scope.

Mandatory owner search before such a claim:

1. read `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md`;
2. read `docs/InductionSystematics.md`;
3. search and read the relevant owner files, especially
   `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`,
   `lean/InfoGeometry/Canonical/TensorTowerColimit.lean`,
   `lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean`,
   `lean/InfoGeometry/Categorical/InductivePosetColimit.lean`, and the local
   categorical file for the domain under discussion;
4. cite the exact imported theorem names in the task packet and final report.

CAS, Coq, Isabelle, Sage, GAP, Singular, Macaulay2, D-modules, or SymPy may
support finite coordinate identities. They do not promote a finite coordinate
identity to a direct-limit, inverse-limit, filtered-colimit, topological, or
analytic theorem without the Lean owner layer above.

### 3.6 Formal intent envelope

The pipeline must not attempt to prove a latent or confabulated theorem directly.
The first QMS artifact is a formal intent envelope. Its purpose is to separate
conceptual payload, theorem candidate, model assumption, external evidence, and
documentation-only material before Lean generation begins.

Minimum schema:

```json
{
  "concept_id": "gamma-group-cl11-base",
  "source_text": "...",
  "intake_classification": "definition-only | theorem-bearing | computational-witness | narrative-documentation | external-system-verification | conjectural-scaffold",
  "classification": "representation-level theorem",
  "mathematical_domain": ["Clifford algebra", "matrix algebra"],
  "target_status": "definition-backed | theorem-backed | model-parameter | computational-witness | external-verified | conjectural-scaffold | documentation-only",
  "risk_level": "R0 | R1 | R2 | R3 | R4 | R5",
  "allowed_imports": [
    "Mathlib.Data.Matrix.Basic",
    "Mathlib.LinearAlgebra.Matrix.Notation",
    "Mathlib.Tactic"
  ],
  "non_theorem_claims": [],
  "formal_objects": ["Mat", "gammaPos", "gammaNeg", "GammaSystem"],
  "acceptance_theorems": [
    "gammaPos_sq",
    "gammaNeg_sq",
    "gammaPos_gammaNeg_anticomm",
    "cl11GammaSystem"
  ]
}
```

The envelope is a hard anti-smuggling control: claims such as D4 triality,
Bost-Connes closure, Mersenne numerology, thermodynamic completion, or physics
bridge completion may not enter the theorem contract unless the envelope names
the exact formal object, owner import, and acceptance theorem carrying that
structure.

### 3.7 Deconfabulation buckets

Every generated claim must be split into one of four buckets before theorem
generation:

- A. Already theorem-backed in mathlib or current repo owner files.
- B. Prove locally from existing hypotheses and imports.
- C. Store as a structure field / model assumption with honest naming and no
  theorem-promotion claim.
- D. Reject or downgrade to comment/conjectural scaffold.

If a theorem statement is found false, the correction loop must not attempt
proof repair. It must rewrite the theorem contract, weaken the conclusion,
strengthen the hypotheses, or downgrade the artifact to conjectural scaffold.

### 3.8 Risk classes

Risk controls scale with artifact type:

- R0: documentation-only, no theorem implications.
- R1: finite computational theorem, local imports only.
- R2: theorem using existing owner surfaces.
- R3: new structure/class/API with downstream imports.
- R4: colimit, quotient, topology, analysis, nonassociative algebra, or physics
  bridge.
- R5: claim touching external standards, publication claims, or repository-wide
  release status.

R4 and R5 tasks require owner search, independent A-A, QA-A acceptance, build or
tooling evidence appropriate to the artifact, placeholder scan, and axiom/scope
audit where theorem-bearing Lean declarations are involved.

## 4. Role separation

Every theorem-bearing task must be split into at least three independent roles.

### 4.1 G-A — Generation agent

Allowed:

- ingest latent bundle;
- search literature/mathlib/repo owner surfaces;
- formulate candidate theorem statements;
- write candidate code or task packets;
- run local smoke tests.

Forbidden:

- declaring acceptance;
- weakening theorem statements silently;
- treating external evidence as Lean closure;
- reviewing its own work as final authority.

Required output:

- candidate artifact or task packet;
- exact source paths read;
- exact theorem names used;
- scope classification: finite stage, finite iteration, algebraic direct
  limit, categorical colimit, inverse limit, topological/analytic completion,
  external evidence, or open debt;
- verification commands attempted and raw status.

### 4.2 A-A — Audit agent

Allowed:

- independently read the generated artifact and relevant owner files;
- search for stronger existing theorem surfaces;
- classify gaps, vacuity, noncomputability, quotient collapse,
  stage/colimit overclaim, and circular proof shape;
- recommend CAPA.

Forbidden:

- authoring the artifact under audit;
- accepting delivery;
- relying on the generation agent’s summary without source/tool verification.

Required output:

- PASS/REQUEST_CHANGES;
- nonconformance table;
- exact file:line evidence;
- required corrective actions.

### 4.3 QA-A — Acceptance quality agent

Allowed:

- run final compile/build/audit gates;
- run `#check` and `#print axioms` probes;
- run vacuity/placeholder scans;
- verify DAG/hash freshness when cited;
- accept or reject delivery.

Forbidden:

- writing new theorem content for the artifact under acceptance;
- changing scope labels to force acceptance;
- accepting from summaries without rerunning decisive checks.

Required output:

- ACCEPTED/REJECTED/ACCEPTED_WITH_LIMITED_SCOPE;
- commands run;
- exact output summary;
- remaining open debts.

### 4.4 Orchestrator

The orchestrator routes work and records status. It may author coordination documents, but cannot use its own coordination notes as proof authority. If the orchestrator writes theorem-bearing code, independent A-A and QA-A review is mandatory before reporting delivery.

## 5. Process map

```text
Latent bundle / symbolic claim
        |
        v
[Stage 0] Intake classification and formal intent envelope
        |
        v
[Stage 1] Semantic normalization to Lean objects and owner surfaces
        |
        v
[Stage 2] Theorem contract with honest hypotheses and names
        |
        v
[Stage 3] Sterile compile with narrow imports
        |
        v
[Stage 4] Independent gap audit and countermodel attempt
        |
        v
[Stage 5] Bounded repair loop with monotonicity controls
        |
        v
[Stage 6] Kernel acceptance, axiom audit, placeholder/style checks
        |
        v
[Stage 7] Release classification and append-only record
```

## 5A. Standard operating procedures

These SOPs instantiate the process map as executable role procedures. They are
mandatory for theorem-bearing tasks and recommended for documentation-only
tasks that influence theorem policy.

### SOP-001-A — Task formulation and generation dispatch

Purpose: ingest a latent bundle and emit a bounded candidate task packet for
audit. G-A output is never accepted by construction.

Responsible party: G-A, Generation Agent.

Mandatory operational steps:

1. Extract the core structural nouns, carriers, operations, relations, and scope
   words from the formal intent envelope.
2. Convert the extracted nouns into valid Lean 4 universe, variable, namespace,
   and import declarations only after repo/mathlib lookup.
3. Map non-associative, quotient, or higher-categorical structures to existing
   mathlib classes when present. If no existing class is appropriate, define a
   custom structure only after constructive-definition audit, with explicit
   coherence laws and non-vacuity obligations.
4. Construct the target `theorem` or `def` statement with precise type
   signatures and explicit implicit arguments where they prevent typeclass
   ambiguity or universe deadlocks.
5. Use structured tactic blocks (`by` with named intermediate steps) for
   candidate proofs unless a short term proof is clearer and fully local.
6. Emit one bounded theorem-contract packet containing the candidate Lean
   payload, required imports, auxiliary lemmas, theorem target, expected scope
   label, release classification, and exact verification commands. Do not emit
   sprawling multi-file rewrites as a single uncontrolled payload.
7. Append status tag `[payload_ready]` only when the packet is ready for A-A.

Generation stop conditions:

- if the owner theorem already exists, stop and report the existing theorem;
- if the claim is false in an existing owner file, stop and emit
  `[rejected_false_surface]`;
- if the claim requires a missing colimit, inverse-limit, topology, or analytic
  owner theorem, stop and emit `[bucket_3_open_debt]` with the missing owner
  obligation.

### SOP-001-B — Independent audit and gap synthesis

Purpose: verify the generated packet without modifying it, classify gaps, and
trigger CAPA when needed.

Responsible party: A-A, Audit Agent.

Mandatory operational steps:

1. Isolation verification: load the G-A payload into a sterile sandbox or
   temporary probe file with only the imports declared by the packet plus the
   minimal repo owner imports needed for checking. Record any namespace bleeding
   or undeclared dependency.
2. Syntactic scan: inspect for malformed declarations, undeclared variables,
   invalid notation overrides, accidental global instances, universe leaks, or
   local edits outside the packet scope.
3. Tactic-state decomposition: for failed, nontrivial, or high-risk proofs,
   step through tactic boundaries using the repo-approved Lean interaction
   wrapper or Lean server interface where available. Record the exact goal state
   at the first failing boundary. If the interface is unavailable, record the
   direct `lake env lean` or `lake build` diagnostic instead.
4. Gap taxonomy logging: classify each unresolved goal under one of:
   - `G1`: syntax, parser, or elaboration failure;
   - `G2`: type mismatch, missing typeclass instance, universe problem, or
     import/API mismatch;
   - `G3`: missing algebraic lemma, unproved side condition, or missing rewrite
     theorem;
   - `G4`: false target, vacuous target, quotient collapse, countermodel found,
     or theorem strength beyond owner authority;
   - `G5`: scope pollution or import-dependent success, where the payload only
     checks because of undeclared broad imports, namespace leakage, or accidental
     instance availability.
5. Counterexample generation: attempt bounded counterexample/model search when
   the goal is finite, algebraic, first-order, or otherwise model-searchable.
   If not model-searchable, record `counterexample_status: not_applicable`.
6. Dispatch report: write or return audit telemetry with verdict, gap taxonomy,
   file:line evidence, and CAPA recommendations. If gaps remain, trigger a
   correction loop back to G-A. If clean, forward to QA-A with `[audit_pass]`.

Audit telemetry schema, minimum fields:

```json
{
  "task_id": "...",
  "artifact": "...",
  "verdict": "PASS | REQUEST_CHANGES | REJECT",
  "files_read": [],
  "commands_run": [],
  "gaps": [],
  "capa": [],
  "scope_label": "finite-stage | finite-iteration | direct-limit | categorical-colimit | inverse-limit | topological | analytic | external-evidence | open-debt"
}
```

Recommended audit record path: `artifacts/qms/<task-id>-audit_report.json`.

### SOP-001-C — Final acceptance and kernel validation

Purpose: act as the final independent quality gate by executing kernel/build,
axiom, placeholder, style, and traceability checks.

Responsible party: QA-A, Acceptance Quality Agent.

Mandatory operational steps:

1. Compilation test: execute a clean narrow build of the audited Lean file or
   module using the exact toolchain specified in `lean-toolchain`.
2. Axiom auditing: run `#print axioms <theorem_name>` or the repo axiom-index
   tool on final symbols.
3. Axiom classification: classify any occurrence of `propext`,
   `Classical.choice`, or `Quot.sound` by origin and semantic role. These are
   neither automatic rejection nor automatic acceptance. Unauthorized new
   axioms, local `axiom` declarations, or unapproved nonconstructive additions
   trigger `[needs_capa]` or rejection.
4. Placeholder scan: scan touched theorem-bearing files, generated probe files,
   and dependency-closure files introduced by the task for `sorry`, `admit`,
   `axiom`, `Prop := True`, fake certificate fields, and equivalent macros.
   Repo-wide scans are release audits, not mandatory for every local task.
5. Style conformance: validate names against neighboring file conventions and
   mathlib style. Types/classes/structures normally use `UpperCamelCase`;
   theorem/lemma names normally use `snake_case`; definitions follow existing
   namespace conventions unless mathlib APIs dictate otherwise.
6. AST/AQL/hash/DAG traceability: if hash or DAG evidence is cited, verify the
   artifact path, import root, declaration presence, and freshness. Record that
   hashes are traceability/navigation evidence, not proof.
7. Formal sign-off: append or produce an append-only checksummed acceptance
   record containing source checksum, theorem names, commands, verdict, and
   status tag. Do not claim immutable storage unless backed by an actual signed
   or WORM ledger.

Acceptance status tags are disjoint by artifact class.

Theorem/code status:

- `[payload_ready]` — candidate payload ready for independent audit;
- `[intent_captured]` — formal intent envelope recorded;
- `[formal_contract_ready]` — theorem contract ready for sterile compile;
- `[sterile_compile_failed]` — narrow-import compile failed;
- `[gap_report_ready]` — A-A gap report exists;
- `[countermodel_found]` — bounded search or owner theorem refutes the target;
- `[repair_split_required]` — loop monotonicity failed; auxiliary lemma split is required;
- `[kernel_verified]` — Lean kernel build passed in the stated module scope;
- `[axiom_audited]` — final theorem symbols have classified axiom output;
- `[release_ready]` — QA-A accepted release classification;
- `[verified_logos]` — theorem-bearing Lean declarations are accepted in the
  stated native Lean scope after build, placeholder scan, axiom audit, and style
  review.

Documentation/QMS status:

- `[qms_document_draft]` — reviewed draft, not controlled;
- `[qms_document_accepted]` — accepted documentation/control artifact;
- `[qms_document_controlled]` — tracked controlled document in the repository;
- `[qms_document_retired]` — superseded or retired controlled document.

Process status:

- `[accepted_limited_scope]` — useful artifact accepted only in a narrower
  finite/conditional/evidence scope;
- `[needs_capa]` — correctable nonconformance;
- `[audit_blocked]` — audit lacked required evidence or tooling;
- `[qa_blocked]` — acceptance lacked required evidence or tooling;
- `[bucket_3_open_debt]` — honest open theorem debt;
- `[rejected_false_surface]` — target refuted or structurally dishonest.

Do not apply `[verified_logos]` to this SOP document itself. The correct status
for this file is `[qms_document_controlled]` once tracked and pushed.

Recommended acceptance record path: `artifacts/qms/<task-id>-qa.json`.

## 6. Gate 0 — Intake and claim inventory

Before code generation, the orchestrator or G-A must produce a claim inventory.

Required fields:

- source text or prompt excerpt;
- mathematical nouns and operations;
- proposed carrier(s);
- proposed theorem(s);
- existing repo owner candidates;
- expected proof authority: mathlib, repo theorem, finite CAS, external proof assistant, or open debt;
- risk flags: nonassociativity, quotienting, noncomputability,
  direct-limit/colimit/inverse-limit language, topological language,
  analytic language.

Hard rule: do not write a grand theorem surface before extracting the smallest explicit mathematical claim.

## 7. Gate 1 — Owner-first search

The G-A must search before writing theorem-bearing code.

Minimum search lanes:

1. repo-wide filename search;
2. repo-wide content search;
3. mathlib/local dependency search for exact theorem names;
4. AST/AQL/hash/DAG or `ask_repo.py`/local-preflight navigation when graph evidence is relevant;
5. read exact owner files, not only docs or search snippets.

For this repository, matrix-level claims must check `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` and the relevant colimit/category owner files before adding matrix packets.

## 8. Gate 2 — Generation controls

Candidate Lean code must obey these controls:

- no `axiom` in owner files;
- no hidden theorem debt in structure fields unless the field is genuinely a primitive law of an explicitly axiomatized object;
- no `Prop := True`, `_True`, `_holds`, `_valid`, `_certificate`, or wrapper-field replacement for proof debt;
- no theorem name stronger than the type signature. Names must be
  content-descriptive, not ambition-descriptive;
- no broad `import Mathlib` or `InfoGeometry.All` in sterile candidate modules
  unless the theorem contract explicitly justifies that import footprint;
- no full `LieRing` instance for full Zorn/split-octonion element commutator; use existing obstruction theorems or derivation algebra instead;
- no direct-limit, inverse-limit, filtered-colimit, topological, or analytic
  theorem from finite matrix or CAS evidence unless the corresponding Lean owner
  theorem is actually imported and used;
- no quotient relation whose breadth collapses the intended degrees of freedom without a separate nontriviality theorem.

Generation deliverables are candidates, not accepted artifacts.

Theorem-name honesty examples:

Good names:

```lean
gammaNeg_sq
trialityAction_apply_det
rationalZornMatrix_det_quark_add_antiquark
modularDerivation_eq_zero_iff_commutes
concreteBridgeKlein_traceZero_of_stored_zeroDefect
```

Nonconforming names unless the type signature truly proves the stated scope:

```lean
anomalyResolution_complete
cathedral_sealed
physicsBridge_proves_RH
bott_periodicity_iso : Bool := true
pAdicValuation_Implies_TraceZero_AnomalyResolution
```

## 9. Gate 3 — Independent semantic audit

A-A must check these items:

| Check | Required evidence |
|---|---|
| Source traceability | exact owner/mathlib file paths and theorem names |
| Non-vacuity | nontrivial instance or explicit counterexample search; no empty hypothesis trick |
| Constructivity | no local `Classical.choice`, `choose`, existential extraction for claimed computable data unless scope is explicitly noncomputable |
| Quotient honesty | equivalence relation preserves intended distinctions; no over-collapse |
| Stage/colimit boundary | finite CAS or matrix evidence not promoted past proved direct-limit, inverse-limit, filtered-colimit, or categorical-colimit theorem |
| Existing owner reuse | stronger existing theorem checked before new surface proposed |
| Zorn/Lie honesty | full Zorn element commutator obstruction respected |
| Comments/docstrings | narrative matches theorem strength |
| Name honesty | theorem names describe proved content rather than desired interpretation |
| Import honesty | sterile candidate does not depend on undeclared broad imports or namespace leakage |

Audit verdicts:

- PASS: no required changes.
- REQUEST_CHANGES: correctable nonconformities.
- REJECT: theorem surface is false, vacuous, or structurally dishonest.

## 10. Gate 4 — CAPA loop

For every REQUEST_CHANGES or REJECT finding, record a corrective and preventive action.

CAPA record fields:

- nonconformance ID;
- finding;
- root cause;
- corrective action;
- preventive action;
- verification command;
- closure status.

Examples:

- Root cause: matrix packet was treated as colimit theorem.
  - Corrective action: downgrade claim to finite stage.
  - Preventive action: require colimit owner search and direct-limit theorem before future promotion.

- Root cause: full Zorn commutator treated as Lie bracket.
  - Corrective action: cite `commutator_jacobi_U_zero_U_one_U_two_ne_zero` and redirect to derivation algebra.
  - Preventive action: require nonassociative obstruction search before any `LieRing` instance.

### 10.1 Divergence and loop controls

Generation/audit loops must be bounded. If G-A and A-A alternate on the same
gap for more than five cycles without decreasing the remaining unresolved goal
count, the orchestrator must halt the loop and perform a structural split:

1. isolate the first failing subgoal into an auxiliary lemma task;
2. downgrade the parent theorem to `[needs_capa]` or `[bucket_3_open_debt]`;
3. dispatch a fresh G-A packet for the auxiliary lemma;
4. dispatch independent A-A and QA-A checks for the auxiliary lemma before
   resuming the parent theorem.

Kernel divergence rule: if tactic-state telemetry suggests success but the Lean
kernel rejects the final artifact, the kernel wins. The allowed response is to
invalidate stale build artifacts, rerun from the checked-in `lean-toolchain`,
record environment/toolchain differences, and retry the narrow build. Agents may
not wipe caches, reset environment variables, or delete build directories unless
the operator explicitly approves the exact command.

## 11. Gate 5 — Acceptance testing

QA-A must run the relevant subset of these gates.

### 11.0 Toolchain and environment fingerprint

Every QA-A acceptance record must capture the exact execution fingerprint:

```bash
git rev-parse HEAD
git status --short
cat lean-toolchain
lake --version
lean --version
sha256sum <artifact>
```

Minimum QA JSON fields:

```json
{
  "git_head": "...",
  "working_tree_scope": "clean | dirty-with-excluded-artifacts | dirty",
  "lean_toolchain": "...",
  "lean_version": "...",
  "lake_version": "...",
  "artifact_sha256": "..."
}
```

If a required QA tool path does not exist in the current checkout, QA-A must
record `tool_missing` and either use an approved fallback or return
`[audit_blocked]` / `[qa_blocked]`. A missing QA tool may not be silently
skipped.

### 11.1 Lean gates

```bash
lake env lean path/to/File.lean
lake build Module.Name
```

When a new module or changed import surface exists, prefer the narrow module build after file check.

### 11.2 Axiom and vacuity gates

```bash
python3 tools/scripts/vacuity-linter.py path/to/File.lean --json
python3 tools/infra/axiom_index.py --json Module.Name
```

For local probes:

```lean
#print axioms Namespace.theorem_name
#check Namespace.theorem_name
```

Canonical axioms `[propext, Classical.choice, Quot.sound]` are not automatic rejection, but must be classified:

- inherited from mathlib infrastructure;
- locally introduced by noncomputable/existential construction;
- quotient-induced and semantically acceptable;
- suspicious and requiring CAPA.

### 11.3 Placeholder scan

At minimum scan touched theorem-bearing files for:

```text
sorry
admit
Admitted
axiom
Axiom
Parameter
Conjecture
axiomatization
oops
Prop := True
:= True
_True
_holds
_valid
_certificate
_sorryProof
```

Findings are classified, not blindly mass-renamed: theorem-shaped legacy names may be acceptable if their bodies are real.

### 11.4 CAS/external lanes

CAS lanes must assert, not merely print. Acceptance must label them as one of:

- finite exact evidence;
- symbolic polynomial evidence;
- smoke test;
- unsupported draft;
- failed/blocked.

External proof assistants are parity evidence unless their theorem statements and build outputs are read and matched to the Lean target.

### 11.5 AST/AQL/hash/DAG gates

If hash/DAG evidence is cited, QA-A must verify freshness:

- artifact path;
- import root;
- source hash / olean hash where available;
- declaration present in current artifact;
- edge endpoint validity if used;
- explicit statement that hashes are navigation evidence, not proof.

Do not cite stale repo-wide DAG artifacts for newly changed declarations. Use a narrow refresh artifact if needed.

## 12. Disposition rules

Release classification tags:

- `[definition_backed]` — definitions or structures checked, no theorem claim
  beyond definitional well-formedness;
- `[theorem_backed]` — theorem-bearing Lean declarations passed acceptance;
- `[model_parameter]` — stored assumption/field/parameter, not derived theorem;
- `[computational_witness]` — finite or executable evidence with explicit scope;
- `[external_verified]` — external proof assistant/CAS artifact accepted only in
  its external scope;
- `[conjectural_scaffold]` — useful scaffold or target, not theorem-backed;
- `[documentation_only]` — narrative/control/process document with no theorem
  promotion authority.

### ACCEPTED

All of these hold:

- theorem/file builds in claimed scope;
- audit PASS or all CAPA closed;
- no unclassified placeholder/vacuity findings;
- scope label matches theorem strength;
- acceptance agent did not author the accepted theorem content.

### ACCEPTED_WITH_LIMITED_SCOPE

The artifact is useful but narrower than the initiating claim. Example:

- finite `O(5,5)` matrix preservation accepted, but no direct-limit,
  filtered-colimit, or categorical-colimit theorem claimed.

### REJECTED

Any of these hold:

- false theorem target, such as full Zorn element-commutator Lie instance over characteristic not dividing 6;
- compile failure in claimed artifact;
- hidden proof debt;
- direct-limit, inverse-limit, filtered-colimit, topological, or analytic claim with only finite evidence;
- audit and acceptance performed by same non-isolated authoring context without independent verification.

### BUCKET 3 / OPEN DEBT

The correct disposition when a claim is mathematically plausible but lacks native owner proof.

## 13. Task packet templates

### 13.1 G-A packet

```text
Role: Generation Agent
Task ID: <ID>
Target claim: <exact claim>
Required inputs:
- source prompt/literature:
- repo files to read:
- mathlib files to read:
- AST/AQL/hash/DAG query terms:
Constraints:
- no acceptance verdict
- no theorem weakening without explicit note
Deliverable:
- candidate theorem/task map
- exact theorem names and paths
- scope labels
- commands attempted
```

### 13.2 A-A packet

```text
Role: Independent Audit Agent
Task ID: <ID>-AUDIT
Artifact under audit: <path or theorem list>
Do not edit.
Checks:
- source traceability
- non-vacuity
- noncomputability
- quotient collapse
- stage/colimit boundary
- existing owner theorem reuse
- placeholder scan
Deliverable:
- PASS / REQUEST_CHANGES / REJECT
- nonconformance table with file:line evidence
- CAPA recommendations
```

### 13.3 QA-A packet

```text
Role: Acceptance Quality Agent
Task ID: <ID>-QA
Artifact under acceptance: <path or theorem list>
Do not author theorem content.
Commands:
- lake env lean <file>
- lake build <Module>
- vacuity-linter
- axiom_index
- #check/#print axioms probe if applicable
- CAS/external scripts if cited
Deliverable:
- ACCEPTED / ACCEPTED_WITH_LIMITED_SCOPE / REJECTED
- exact commands and outputs
- remaining debt list
```

## 14. Standard theorem-lane dispatch board

Use these standard lanes for confabulation-to-proof work:

1. Mathlib theorem scout: exact theorem-name map and import path.
2. Repo owner scout: existing owner/translator/coherence/capstone surfaces.
3. CAS finite evidence runner: exact symbolic assertions and output logs.
4. External proof-assistant parity scout: Coq/Isabelle theorem inventory and build status.
5. Categorical/colimit scout: direct/inverse/filtered colimit owner theorem search.
6. Semantic auditor: theorem strength, vacuity, stage/colimit boundary.
7. Acceptance QA: build, axiom, vacuity, hash/DAG freshness.

No lane may replace QA-A acceptance.

## 15. Current instantiated lessons

### 15.1 Full Zorn commutator is not a Lie bracket

Existing owner obstruction:

- `InfoGeometry.Algebra.ZornVectorMatrix.commutatorJacobiator_eq_associator_alternating`
- `InfoGeometry.Algebra.ZornVectorMatrix.commutator_jacobi_U_zero_U_one_U_two`
- `InfoGeometry.Algebra.ZornVectorMatrix.commutator_jacobi_U_zero_U_one_U_two_ne_zero`

Any future `LieRing` or `LieAlgebra` task over Zorn data must either:

- use derivations with commutator from associative endomorphism composition;
- restrict to a proved Lie-admissible/associative subcarrier;
- or remain BUCKET 3/open debt.

### 15.2 Finite `O(5,5)` matrix packets are not colimit theorems

Finite Buscher or Pin matrix identities are accepted only in finite scope unless a direct/inverse/filtered colimit theorem transports them. Current missing layer for Buscher/O(5,5) promotion is a `SplitCharge` directed-system/direct-colimit owner surface with transition maps and swap-commutation theorem.

### 15.3 Categorical owner surfaces precede matrix expansion

Before writing matrix-level code, check whether the categorical theorem already exists. In this repo, relevant surfaces include:

- `InfoGeometry.Categorical.InductivePosetColimit`
- `InfoGeometry.Canonical.CategoryTheoryConeUniqueness`
- `InfoGeometry.Canonical.SplitCliffordDirectLimit`
- `InfoGeometry.Canonical.CliffordO55ProjectiveReconciliation`
- `InfoGeometry.Canonical.ProperCarrierInductiveColimit`

## 16. Records

For each QMS run, produce or update a record containing:

- task ID;
- role assignments;
- files read;
- files changed;
- commands run;
- audit findings;
- CAPA records;
- final disposition;
- remaining debt;
- source checksum, usually `sha256sum <artifact>`;
- status tag from SOP-001-C.

Records should be append-only/checksummed where practical. Do not describe a log
as immutable unless the repository actually stores it in a signed, WORM, or
otherwise tamper-evident ledger.

Recommended paths:

- task packet: `handover/injections/<task-id>.md`
- audit report: `artifacts/qms/<task-id>-audit.md`
- acceptance report: `artifacts/qms/<task-id>-qa.md`
- machine-readable audit telemetry: `artifacts/qms/<task-id>-audit_report.json`
- machine-readable QA telemetry: `artifacts/qms/<task-id>-qa.json`
- refreshed narrow DAG: `artifacts/dag/index_<task-id>/`

## 17. Minimal compliance checklist

Before any theorem-bearing claim is delivered, answer yes/no:

1. Did a non-authoring audit agent inspect the artifact?
2. Did a non-authoring QA agent or parent session rerun decisive commands?
3. Are all claims labeled finite-stage/conditional/direct-limit/categorical-colimit/inverse-limit/topological/analytic/open?
4. Are exact owner theorem names and file paths cited?
5. Are AST/AQL/hash/DAG artifacts fresh if cited?
6. Are external CAS/proof-assistant results scoped as evidence only?
7. Does the artifact avoid known fake-closure patterns?
8. Is every remaining gap recorded as BUCKET 3/open debt?

If any answer is no, delivery is not accepted.

## 18. Operator quick gate

Before accepting a theorem-bearing artifact, execute or explicitly record why the
following gate is not applicable:

1. `git status --short` checked.
2. Exact owner files read.
3. Formal intent envelope captured.
4. Scope and risk labels assigned.
5. Narrow build or file check run.
6. Placeholder scan run.
7. Axiom audit run or explicitly not applicable.
8. CAS/external evidence labeled finite/external only.
9. A-A and QA-A are not the authoring context.
10. CAPA closed or BUCKET 3/open debt recorded.
11. Theorem names checked for content-descriptive honesty.
12. Final checksum and toolchain fingerprint recorded.

## 19. First recommended pipeline test case

The first theorem-bearing test case should be small and theorem-honest. Prefer
Split `Cl(1,1)` gamma matrices over Bost-Connes, D4 triality, or arbitrary
dimension gamma groups:

```text
gammaPos_sq
gammaNeg_sq
gammaPos_gammaNeg_anticomm
cl11GammaSystem
```

Acceptance criteria:

- no `sorry`;
- no `axiom`;
- no broad `import Mathlib` unless justified in the theorem contract;
- no physical overclaim in theorem names;
- declarations compile in a sterile module;
- axiom audit clean or limited to approved/classified Lean foundations.
