---
name: protected-baseline-formalization
description: Safely formalize and repair Lean 4 code in info-geometry-lean while preserving the categorical architecture, build cache, staged-work protections, single-flight aiClaw lane, colimit-continuum law, and kernel-checked truth boundary. Use for any repository-wide formalization, proof repair, categorical projection, or Lean maintenance request. Enforces the protected-baseline discipline, repository-wide symbol/dependency search, basis-aligned CAS certification, coordinated correction propagation, and zero sorry/admit/axiom/proxy/vacuity closure with full locked-build quality gates.
metadata:
  short-description: Protected Lean formalization workflow
---

# Protected baseline formalization

Operating identity for repository-wide formalization work in `info-geometry-lean`.
This skill's gate checklist overrides closure claims made elsewhere. The
verified repository baseline and its structural pillars are immutable unless a
mathematical audit proves a correction is required. Never promote a claim
because a CAS script, generated certificate, green narrow build, or prior
report says so; the Lean kernel and the full quality gates are authoritative.

## Immutable goal contract

PROTECTED BASELINE → prompt mathematics → repository-wide symbol/dependency search → existing-definition alignment → global consistency audit → mathematical correction → affected-code propagation → native Lean 4/mathlib formalization → substantive reusable lemmas/theorems → explicit complete kernel proofs → no axioms/sorry/admit/proxies/wrappers/aliases/vacuity/duplication/dead code → full build → all quality gates clean.

GOAL — preserve the verified repository baseline and structural pillars → for
every new mathematical request: repository-wide semantic search of all affected
definitions, functions, instances, lemmas, theorems, namespaces, imports, and
dependents → mathematical audit against the existing code architecture →
correction of every inconsistent occurrence, not only the named file →
completion through native Lean 4 and mathlib abstractions → substantive reusable
lemmas and theorems with explicit kernel-checked proofs → interface preservation
unless mathematically invalid → zero `sorry`, `admit`, custom axioms,
placeholders, proxy witness/certificate/law structures, wrapper theorems,
theorem aliases, vacuous hypotheses, duplicated APIs, dead declarations, or
ungrounded terms → master build and all closure, frontier, baseline, proxy,
axiom, and vacuity gates remain clean.

## Phase 0 — Routing (read first)

1. Read `docs/CANONICAL_AGENT_PIPELINE.md` before any other action. It defines the current repo path, tool routing, aiClaw queue discipline, Pi extension stack, GEPA flow, and forbidden legacy routes. If a generated transcript or archived routing note conflicts with it, the canonical pipeline wins.
2. Read `docs/HIVE_AGENT_COMMANDMENTS.md` for the compact operational law of the hive.
3. For DAG/Arango/LeanTrail/Hodge/de Bruijn/WL redundancy cleanup, namespace deduplication, stale dropin removal, pure forwarding-module collapse, or compatibility-shim refactors, read `skills/lean-dag-wire-refactor/SKILL.md`.
4. For categorical-infrastructure-projection tasks, read `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` first, then consult the central skill library at `skills/lean-skill-library/` (skill: `categorical-infrastructure-projection`). Optional GEPA evolution:
   ```bash
   python3 tools/infra/gepa_categorical_projection.py --evolve --generations 10
   ```

## Non-negotiable safety gates

Check every gate before each build-related command:

- **NEVER run `lake clean`.** NEVER delete `.lake/build`, `.lake/packages`, or `.lake`. Nuking the cache destroys precompiled oleans and forces long recompilation loops. Use targeted compiler commands or rebuild specific files only.
- **No concurrent builds.** Before any `lake build`, `lake test`, `lake env lean`, `pytest`, or similar, verify that no compiler task is active.
- **Never kill a running `lake task** without explicitly asking the user and receiving approval.
- **`.lake/packages/` is read-only** (`chmod -R a-w`). Never run `lake update`, never edit `lakefile.lean` or `lake-manifest.json` without explicit human approval, never touch vendored dependency toolchains. If an import breaks, work within the pinned Mathlib cache (`v4.28.1`).
- **Continuous tracking:** after creating or modifying any file, immediately run `git add -A`. Staged work is protected from rogue `git restore`.
- **Do not edit dirty external submodules.**
- **Subagent sandbox:** never delegate file repairs/rewrites to a subagent on the live owner file. Give subagents only new-file tasks in a sandbox, supplying sufficient mathematical context extracted from the old file.
- **Truth boundary:** graph tools, transcripts, CAS results, and oracle suggestions are navigation/review evidence only. Only kernel-checked Lean source edits count as truth.

## Repository architecture — owners exist before you rewrite

Read `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` before touching categorical code. The categorical layer owns:

- `Algebra/Grothendieck.lean`
- `Canonical/TensorTowerColimit.lean`
- `Categorical/FibonacciBraiding.lean`

Matrix-level code is an *instance*, never a replacement. Do not rebuild what already exists.

## G₂(2) Bruhat decomposition — formalization pipeline

The paper "Формализация на (B,N)-Двойката и Брюа Разлагането за Изключителната Група на Ли G₂(2) в Lean 4" describes the finite-dimensional G₂(2) (order 12 096) Bruhat decomposition. The existing codebase already kernel-checks the vast majority of this paper. The mandated workflow is:

### Stage A — Finite-dimensional base (DO FIRST)

Formalize the discrete algebraic structure BEFORE any colimit passage:

| Paper concept | Existing owner | Status |
|---|---|---|
| G₂(2) finite Chevalley group (order 12 096) | `G2TwoFiniteChevalleyGroup.lean`, `G2TwoAutomorphismOrderLedger.lean` | kernel-checked |
| Split-octonion carrier `SplitOctF2Aut` | `OperatorAlgebra/G2TwoAutomorphismTheorem.lean` | kernel-checked |
| Unipotent Sylow 2-subgroup U₆ (order 64) | `G2TwoPCSubgroupClosure.lean`, `G2TwoPCGroup.lean` | kernel-checked |
| Polycyclic collector `pcCombine` / `pcWord` | `G2TwoPCNormalForm.lean`, `G2TwoPCConcreteCollector.lean` | kernel-checked |
| 12-element Weyl group W(G₂) ≅ D₁₂ | `G2TwoConcreteWeylGroup.lean`, `G2TwoBruhatClassification.lean` | kernel-checked |
| Concrete Bruhat cells C(w) = BwB | `G2TwoBruhatClassification.lean` | kernel-checked |
| (B,N)-pair / TitsSystem structure | `G2BNPair.lean` | kernel-checked |
| Axiom BN2: sBs ⊆ B ∪ BsB (symbolic) | `G2SymbolicBN2.lean` | kernel-checked |
| Axiom BN2 (index-2 Levi split) | `G2IndexTwoRankOneBN2.lean` | kernel-checked |
| Rank-1 Levi SL₂(𝔽₂) BN2 | `SL2F2LeviBN2.lean` | kernel-checked |
| Inductive peeling on word lists | `G2BN2InductivePeeling.lean` | kernel-checked |
| Big-cell polynomial witnesses a(e) | `G2BigCellPolynomialWitnesses.lean` | kernel-checked |
| Flag variety cardinality Σ 2^{ℓ(w)} = 189 | `G2BruhatCardinalities.lean` | kernel-checked |
| Parabolic cardinality Σ_{k<6} 2^k = 63 | `G2BruhatCardinalities.lean` | kernel-checked |
| 2-to-1 fiber W(G₂) ↠ W^J | `G2BruhatCardinalities.lean` | kernel-checked |
| Fibration G/B₀ → G/P, fiber ≅ ℙ¹(𝔽₂) | `G2FlagAndParabolicQuotient.lean` | kernel-checked |
| G-equivariant coset projection | `G2FlagAndParabolicQuotient.lean`, `G2GAPCosetHomomorphismBridge.lean` | kernel-checked |
| Bruhat cell weights 64·2^{ℓ(w)}, sum = 12 096 | `G2BruhatCellDecomposition.lean` | kernel-checked |

### Stage B — Categorical colimit passage (DO ONLY AFTER A)

ONLY after the finite-dimensional structure is fully formalized, project through
the categorical inductive colimit to reach the continuum:

| Colimit concept | Existing owner | Status |
|---|---|---|
| UHF inductive colimit boundary | `Canonical/UHFInductiveColimitBoundary.lean` | kernel-checked |
| Diagonal embedding / cylinder functions | `UHFInductiveColimitBoundary.lean` | kernel-checked |
| Colimit trace invariance | `UHFInductiveColimitBoundary.lean` | kernel-checked |
| Tensor tower colimit | `Categorical/TensorColimit.lean` | kernel-checked |
| Erlangen colimit resolution | `Canonical/ErlangenColimitResolution.lean` | kernel-checked |
| A∞ = lim→ ⊗ Mₙ(ℂ) passage | Connect via `UHFInductiveColimitBoundary` + `TensorColimit` | **REQUIRES NEW BRIDGE** |

**Prohibition:** Do NOT use classical measure theory or brute-force real analysis
to cross from finite quantum models to the continuum. Strictly use categorical
direct inductive colimits.

### Known paper errors to correct during formalization

1. **Module count inflation:** Paper claims "15 modules, 3116 theorems." The actual
   codebase has ~130 files in `Algebra/Zorn/` alone, with ~30 directly G₂(2)-Bruhat
   related. Do not replicate the paper's counting; count actual kernel-checked files.
2. **Torх clarification:** The paper states "H ≅ (F₂ˣ)² = {1}" correctly but then
   writes "B₀ = U₆ ⋊ H = U₆." Since the torus is trivial in char 2, B₀ = U₆ is correct,
   but the semidirect product notation is misleading — it is a direct equality.
3. **Fibration fiber:** Paper says "P/B₀ ≅ ℙ¹(𝔽₂) от 3 точки." Correct: the fiber has
   3 points, but P/B₀ is isomorphic to P¹(𝔽₂) as a P-set, not as a group. The
   homogeneous space structure must be preserved.
4. **Parabolic order:** Paper gives |P| = 192. This is correct: P = B · SL₂(𝔽₂) · B
   with |SL₂(𝔽₂)| = 6 and the SL₂ Borel ∩ B contributing a factor, giving 64·3 = 192.
   Verify the intersection computation explicitly, not by rote.

## Formalization workflow (execute in this exact order)

1. **Baseline**: establish the current state from the actual worktree (`git status`, `git log`), never from reports or conversation claims.
2. **Proposition**: state the mathematics precisely — carriers, scalars, multiplication/action conventions, hypotheses, intended reusable interface.
3. **Search**: `rg` the entire repository for every affected symbol, namespace, import, instance, lemma, theorem, and dependent declaration.
4. **Audit**: check the request against existing definitions. Correct sign, ordering, composition, basis, characteristic, and quotient conventions BEFORE writing Lean. Propagate every correction to all occurrences; never create a parallel replacement API or compatibility alias.
5. **Transport**: one substantive fact at a time, into the smallest existing Lean owner. Explicit definitions, reusable helper lemmas, complete proofs. No `sorry`, `admit`, `axiom`, opaque witnesses, proxy certificate structures, trivial wrappers, theorem aliases, vacuous assumptions, or duplicate abstractions.
6. **Verify**: narrow `lake env lean <file>` after each correction. Treat warnings as failures when clean closure is requested.
7. **Gates**: run owner/subsystem/master builds plus every applicable closure/frontier/baseline/proxy/axiom/vacuity gate. A narrow green check never justifies a repository-wide claim.
8. **Preserve & commit**: stage immediately; commit only settled states; if blocked (e.g., a concurrent writer is active), say so instead of claiming completion.

## Lean 4 ⇄ CAS (SymPy/GAP) translation — MANDATORY STANDARD

Translation from Lean 4 to CAS algebras is paramount and MUST be standardized.
CAS (SymPy/GAP) provides speedup in development: verify identities, structure-
constant tables, sign conventions, and basis computations symbolically first,
then translate into Lean.

**Binding pipeline:** SymPy/GAP verification (exact arithmetic, frozen basis order) → normalized JSON exchange artifact → statement-by-statement Lean translation (one lemma per CAS assertion) → proof against the owner surface → targeted kernel check + `git add -A`.

- Full protocol: [references/CAS_TRANSLATION_STANDARD.md](references/CAS_TRANSLATION_STANDARD.md)
- Supporting skills: `skills/sympy-lean-handoff/SKILL.md` (when to hand off), `skills/sympy-to-lean-line-by-line/SKILL.md` (assertion-by-assertion mechanics), `skills/sympy/SKILL.md` (SymPy reference).
- Core rule: SymPy/GAP is an algebra checker and statement shaper; Lean is the truth authority. A CAS result is never final until re-expressed as a kernel-checked Lean theorem.
- Prohibition: never route continuum/colimit claims through CAS — they go through the colimit owners only.

### Carrier-alignment protocol (MANDATICAL BEFORE THEOREM TRANSPORT)

To avoid the CAS↔Lean mismatch failure mode, EVERY CAS artifact must carry
explicit carrier-alignment metadata that is verified before any theorem transport:

1. **Exact Lean definitions**: record the precise Lean `def`/`abbrev`/`structure` the
   CAS object corresponds to (e.g., `SplitOctF2Aut`, `PCExponent = Fin 6 → ZMod 2`).
2. **Basis/matrix orientation**: freeze the basis order (e.g., `(i, j)` pairs in
   lexicographic order for split-octonion rows) and record whether the CAS uses
   row-major or column-major convention.
3. **Anti-hom multiplication law**: if the CAS represents group multiplication as
   function composition (anti-hom: `toMatrix (g * h) = toMatrix h * toMatrix m`), this
   MUST be documented and the Lean side must compensate. The existing
   `finiteChevalleyG2_mul_apply` shows `(f * g).1 X = g.1 (f.1 X)` — note the reversal.
4. **PC word order**: the polycyclic collector uses a specific generator ordering
   `e₀, ..., e₅`. Any CAS computation involving `pcCombine` must use the identical
   ordering. Record the `pcCombine` formula used.
5. **Mandatory round-trip checks**: after generating a CAS artifact, pick ONE
   non-trivial concrete element, compute its image in both CAS and Lean, and verify
   equality before transporting any theorem from that artifact. If the round-trip
   fails, the carrier alignment is wrong — do NOT proceed to theorem transport.

### Standardized CAS artifact schema (carrier-aligned)

```json
{
  "object": "g2_polycyclic_combine",
  "lean_owner": "InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm",
  "carrier": "PCExponent = Fin 6 → ZMod 2",
  "basis_order": ["e0", "e1", "e2", "e3", "e4", "e5"],
  "multiplication_convention": "pcCombine (left-to-right word product)",
  "anti_hom": false,
  "lean_multiplication": "pcCombine e f",
  "cas_source": "scripts/derive_pc_normal_form_symbolic.py",
  "round_trip_verified": true,
  "round_trip_element": {"input": [1,0,1,0,1,0], "expected_output": "..."},
  "artifact_hash": "<sha256>"
}
```

Rules:
- Store the generating script under `scripts/` and hash it.
- The artifact must be regenerable: rerunning the script reproduces it bit-for-bit.
- `round_trip_verified` MUST be `true` for any theorem transport to proceed.
- Record which identities the CAS actually checked — unchecked tables are marked `"checked": false` and may not be translated as if proven.

### Speedup discipline

Batch related identities into one CAS script run before touching Lean. The
goal of the standardization is exactly this: one deterministic
script → artifact → statement batch → proof batch loop, instead of ad-hoc
per-theorem guessing in the elaborator.

## Enforcement rules

Read [references/ENFORCEMENT.md](references/ENFORCEMENT.md) before your first
edit of each session. They encode observed failure modes: basis-mismatched CAS
certificates, fictional presentations, vacuous interfaces, concurrent-agent
clobbering, representative-search obligations, and char-2 tactic pitfalls.

## aiClaw / ChatGPT-assisted proof repair

ChatGPT is a Socratic auditor and repair suggester only. Read `docs/AICLAW_CHATGPT_REVIEW_RUNBOOK.md` and `skills/socratic-oracle-proof-repair/SKILL.md`.

Prefer `python3 tools/infra/socratic_clawbot.py --dry-run --json` for Lean owner-file oracle prompts; it delegates transport safety to `tools/infra/aiclaw_chat.py`.

Single-flight lane discipline (`--platform chatgpt`):

1. Check `python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt`; follow its machine-readable `queue_state` / `agent_action` fields.
2. `needs_readback`: not an outage, not a hard block. Recover the final visible answer with a read-only browser view, record it in the work log, then release with `queue-release`.
3. `active`: wait. `ready`: send exactly one prompt containing the complete owner file plus all relevant build errors. Do not stack prompts.
4. `stale_active` with only dead process markers: run `python3 tools/infra/aiclaw_chat.py queue-prune-active --platform chatgpt`, or send one prompt if `lane_available=true`.

Lane prohibitions:

- All repo-owned ChatGPT browser senders use this same lane. No direct port-1956 WebSocket bridge, no raw browser-harness DOM injection without `tools/infra/chatgpt_lane_guard.py`, no Enter-key fallback when ChatGPT has not exposed an enabled send button.
- Google AI Mode is a separate browser-harness lane via `scripts/google-ai-search.sh`; never route it through aiClaw unless re-enabled and tested. Gemini aiClaw stays Gemini; Google AI Mode browser-harness stays Google AI Mode.
- Treat oracle answers only as full-file replacement candidates if they survive Lean checking. Keep corrected files small and mathlib-style. Do not claim hidden chain-of-thought recovery.

For external formal precedent, read `docs/DEBATE_ORACLE_CONVERGENCE_MAP.md`. `external_refs/deepmind-debate` is an adversarial stochastic debate correctness source, not a blanket chatbot-convergence theorem.

## Final gate checklist (all must hold before claiming closure)

- Full locked build green: zero errors AND zero warnings
- `rg "sorry|admit|^axiom "` clean on every touched module
- Every theorem references objects actually inhabited in the repository
  (no vacuous structures, no fictional presentations)
- Every nontrivial constant cross-checked against a basis-aligned CAS
  artifact stored under `scripts/` or `scratch/`
- CAS artifacts carry verified carrier-alignment metadata (`round_trip_verified: true`)
- No parallel replacement APIs, aliases, wrappers, or dead declarations
- Tree committed, or explicitly reported blocked, with no concurrent writer
  active during verification

## Reporting identity

Report facts, not aspirations. Distinguish CAS evidence, Lean kernel evidence,
and full-repository evidence. Name exact files, statements, commands, errors,
warnings, and remaining debt. If a convention mismatch or missing artifact
blocks a proof, stop promotion of that theorem, isolate the smallest
reproducible discrepancy, and continue with safe audit work.

## Hive Memory (ArangoDB RAG)

Persistent memory runs at:

- Address: `http://localhost:8540`, database `hive_memory`, credentials `root` / `hive_brain`
- Collections: `Thoughts` (Document), `CausalLinks` (Edge)
- Contents: full JSONL transcript DAG of past thoughts, generated code, reasoning steps
