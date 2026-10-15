# OpenGauss Protocol Extensions: The Autonomous Mathematical Furnace

> **Document ID:** QMS-POL-OGP-002  
> **Status:** Controlled Repository Standard  
> **Effective Date:** 2026-10-12  
> **Authority:** QMS-SOP-IAA-001 (Independent Agent Audit and Acceptance SOP), QMS-SOP-ALC-001 (Alchemical QMS), Black Book Generative Constitution  
> **Scope:** Multi-Agent Formalization, Automated Theorem Proving, Adversarial Auditing, and Proof Lifecycle Management across `info-geometry-lean`.

---

## 1. Preamble & Motivation

### 1.1 From Procedural Checklist to Autonomous Mathematical Furnace
The legacy formalization procedures of early neural-symbolic systems relied heavily on human-in-the-loop procedural checklists, linear heuristic reviews, and ad-hoc tactic loops. Under complex categorical, operatorial, and topological loads—such as infinite colimit completions, indefinite Krein spaces, and non-commutative geometric algebras—such manual workflows break down into cognitive fatigue, prompt drift, context window compaction thrashing, and unverified wrapper accumulation.

The **OpenGauss Protocol Extensions** transition the repository from a manual procedural checklist into an **autonomous, self-correcting mathematical furnace**. In this furnace, mathematical concepts undergo a controlled thermochemical cycle: high-entropy symbolic exploration is subjected to relentless adversarial compression, structural filtering, and kernel calcinatio, where only ground-truthed, kernel-checked Lean 4 artifacts survive.

```
       +-------------------------------------------------------------+
       |             THE AUTONOMOUS MATHEMATICAL FURNACE             |
       +-------------------------------------------------------------+
                                      |
         [Stage 1: Nigredo]           v   (Discovery Reservoir / Black Books)
         Symbolic Ore & Motifs   ==========> High-temperature generative exploration
                                      |
         [Stage 2: Albedo]            v   (Adversarial Compression / Refuter)
         Pauli Screening Gate    ==========> 17-Trap Catalog (T1-T17) & Gate 2.5 Witnessing
                                      |
         [Stage 3: Citrinitas]        v   (Constitutional Legislative Gate)
         Manifest Locking        ==========> Consumer-minimal signatures & glue compile
                                      |
         [Stage 4: Rubedo]            v   (The Calcinatio / Lean Kernel)
         Kernel Closure               |
               +----------------------+----------------------+
               |                                             |
        [PASS: Exit Code 0]                         [FAIL: Refutation / Sorry]
               v                                             v
     Gate 4 Certification                       Residue Quarantine Loop
     0 sorry, 0 custom axioms                   (Newton-Jung-Spire Cycle)
               v                                             v
     Continuous Checkpoint                     TypedObstructionPacket JSON
     Permanent Core Addition                   Constrains future generations
```

### 1.2 Synthesis of Core Philosophies
The Extended OpenGauss Protocol synthesizes three foundational repository frameworks:

1. **Goutev’s Principle (Absolute Relativity of Measurement / Relational Invariants)**:
   * *Axiom of Relationality*: Physical and mathematical observables carry no standalone ontological meaning in isolation; they exist strictly as relations, contrasts, ratios, homomorphisms, and intertwining maps relative to an explicit reference frame or gauge.
   * *Scale is Gauge; Normalization is Gauge Fixing*: Standalone coordinate metrics and unnormalized absolute magnitudes are banned. Mathematical assertions must be formulated as relational invariants (group actions, intertwining operators, projective rays, cocycles, and colimit morphisms).

2. **The Black Book Generative Constitution (Stratified Architecture)**:
   * **Reservoir (Generative Unconscious)**: High-temperature generation of motifs, tensions, and structural candidates (`docs/black_books/`).
   * **Distillation (Alchemy)**: Extraction of formal ore, candidate signatures, and bridge lemmas.
   * **Pauli Shaping (Adversarial Screen)**: Ruthless elimination of trivial renamings, tautologies, coordinate illusions, and latent duplication.
   * **Candidate Packet (Legislative Manifest)**: Freezing candidate types, bindings, and dependency budgets into immutable JSON contracts.
   * **Furnace (Formal Calcinatio)**: Kernel verification under locked execution (`run_locked_lake_build.py`), with zero tolerance for signature drift.

3. **The Anti-Cheating Protocol (The Orchestrator Commandments)**:
   * **No Missing Proof Obfuscation**: Wrapping unproven conjectures in `Prop`, `structure ... : Prop`, or defining `def X : Prop := True` is treated as high treason and causes immediate pipeline termination.
   * **Absolute Ban on Arbitrary Axioms**: The only permissible axioms are standard Lean 4 / Mathlib foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). Introducing ad-hoc `axiom` declarations is strictly forbidden.
   * **Honest Use of `sorry`**: During active leaf derivation, unproven lemmas must be exposed with explicit, visible `sorry`. Sorries must never be hidden behind empty structures, fake typeclasses, or trivial string equalities (`"theory" = "theory"`).
   * **Native Mathlib Grounding**: Every lemma must be proven using canonical Mathlib tactics and lemmas. Theorems must be decomposed into manageable lemma chains rather than skipped.

### 1.3 Upstream `math-inc/opengauss` vs. Local TeamAntigravity Subagent Extension
Upstream [`math-inc/opengauss`](https://github.com/math-inc/opengauss) (vendored in `OpenGauss/`) provides a TUI launcher (`gauss`) and PTY process manager (`OpenGauss/swarm_manager.py`) that delegates the **9 `cameronfreer/lean4-skills` workflows** (`/prove`, `/draft`, `/review`, `/checkpoint`, `/refactor`, `/golf`, `/autoprove`, `/formalize`, `/autoformalize`) to spawned CLI sessions.

To adapt this architecture safely for multi-agent formalization in `info-geometry-lean`, the local **TeamAntigravity Protocol** extends upstream OpenGauss across four dimensions:
1. **9 → 15 Native Commands (`tools/infra/opengauss_cli.py`)**: Retains all 9 upstream workflows and adds 6 new commands: `/check` (counterexample & consistency auditor), `/refute` (17-Trap static screener), `/handoff` (M10 cross-session context preserver), `/discover` (Gate 0 anti-duplication & carrier hunter), `/quarantine` (Pillar II `TypedObstructionPacket` isolator), and `/certify` (Pillar IV companion `*Audit.lean` `#print axioms` generator).
2. **15 → 17 Traps (`tools/infra/opengauss_screener.py`)**: Extends the T1–T15 False-as-Stated catalog with **Trap T16** (4-part Anti-Surrogate / Operator-Algebraic Root gate: scalar surrogate struct ban, pre-commutator homomorphism rejection, carrier-matched non-commutativity witness requirement, and scalar tactic misuse on unprojected operators) and **Trap T17** (Gate 2.5 Mandatory Model Witnessing & Non-Degeneracy Check with transitive local/imported axiom & `sorry` taint tracking).
3. **3-Tier Sandboxed Subagent Swarm**: Replaces `OpenGauss/swarm_manager.py`'s direct project-root `--dangerously-skip-permissions` PTY sessions with native **TeamAntigravity Subagents** (`invoke_subagent` / `define_subagent` / `send_message` in Antigravity; `collaboration.spawn_agent` in Codex) operating in a **Leader → Orchestrator → Sandbox Worker Swarm** hierarchy where subagents write strictly to `scratch/` sandboxes under the **Subagent Sandbox Mandate**.
4. **Locked Single-Flight Kernel Verification**: Replaces uncoordinated background `lake` calls with sequential builds guarded by `/tmp/info-geometry-build.lock` (`python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock`).

---

## 2. The Four Pillars of the Extended Protocol

```
+---------------------------------------------------------------------------------------+
|                               FOUR PILLARS OF OPENGAUSS                               |
+---------------------------------------------------------------------------------------+
|  PILLAR I: Declaration-First Discovery Gate (Anti-Duplication Law)                    |
|  - Pre-flight AST, Lake environment, Loogle, and Mathlib search before drafting       |
|  - Prohibition of synthetic reinvention; mandatory direct import of existing owners  |
+---------------------------------------------------------------------------------------+
|  PILLAR II: Residue Quarantine Negative Feedback Loop (Newton-Jung-Spire Loop)        |
|  - Failed proof trajectories and refutations emit immutable TypedObstructionPackets   |
|  - Separation into Conserved Gold (Proven Core) and Slag (Frontier Residue)           |
+---------------------------------------------------------------------------------------+
|  PILLAR III: Goutev's Relational Invariant Formulation                                |
|  - Standalone coordinate metrics banned; projective rays and intertwining maps enforced|
|  - Normalization treated as gauge fixing; descent through categorical colimit towers   |
+---------------------------------------------------------------------------------------+
|  PILLAR IV: Automated Certification & Zero-Boilerplate Auditing                       |
|  - Standardized CLI and Lean metaprogramming emitters for Gate 2 and Gate 4 auditing  |
|  - Machine-readable JSON certification receipts and continuous Git tracking          |
+---------------------------------------------------------------------------------------+
```

### 2.1 Pillar I: The Declaration-First Discovery Gate (Anti-Duplication Law)
Before any new definition, lemma, or helper theorem is drafted, the agent must execute a **Pre-Flight Declaration-First Discovery Scan**.

1. **Anti-Duplication Mandate**:
   * It is forbidden to define a local copy or ad-hoc wrapper of a concept already existing in Mathlib or the repository's canonical modules (`InfoGeometry.Canonical.*`, `Algebra.*`, `DAG.*`).
   * If a required mathematical structure is already proved, the agent must directly import and consume the canonical declaration.
2. **Pre-Flight Discovery Protocol**:
   * Search Mathlib documentation and local olean AST declarations via `opengauss_cli discover` or Loogle/grep.
   * Query the Hive Memory (ArangoDB RAG) and AST dependency DAG for candidate paths and existing intertwining maps.
   * Check `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` to ensure categorical owners (`Algebra/Grothendieck.lean`, `TensorTowerColimit.lean`, `FibonacciBraiding.lean`) are utilized rather than reinvented as coordinate matrix instances.
3. **Breach Consequences**:
   * Positing a duplicate declaration without an explicit cross-representation bridge is classified as **Structural Duplication Debt** and results in immediate rejection at Gate 2.

### 2.2 Pillar II: The Residue Quarantine Negative Feedback Loop (Newton-Jung-Spire Loop)
In traditional proof agents, a failed proof attempt produces empty failure or causes the agent to loop hallucinated variations of the same broken strategy. Under the OpenGauss Protocol, **failure is never discarded; failure is diagnostic residue**.

1. **The Law of Lineage Preservation**:
   * When an attempt to prove a theorem fails or is refuted by a counterexample, the trajectory is immediately split into:
     * **Conserved Proof Matter (Gold)**: All intermediate helper lemmas that compiled with 0 sorry and valid axioms are saved into the permanent lineage log (`docs/policy/lineage_skeleton.md`).
     * **Frontier Residue (Slag)**: The exact tactic failure, type clash, counterexample witness, or trap violation is distilled into a `TypedObstructionPacket`.
2. **The `TypedObstructionPacket` JSON Schema**:
   * Every failed trajectory is saved to `artifacts/residue_quarantine/` and appended to `docs/black_books/residue_shadow.md`.
   * The schema permanently binds future prover generations:

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "TypedObstructionPacket",
  "type": "object",
  "required": [
    "obstructionId",
    "timestamp",
    "targetTheorem",
    "targetSignature",
    "obstructionType",
    "failedTrajectory",
    "minimalCounterexampleOrClash",
    "bannedSearchDirections",
    "conservedCoreLemmas"
  ],
  "properties": {
    "obstructionId": { "type": "string" },
    "timestamp": { "type": "string", "format": "date-time" },
    "targetTheorem": { "type": "string" },
    "targetSignature": { "type": "string" },
    "obstructionType": {
      "type": "string",
      "enum": [
        "COUNTEREXAMPLE_WITNESS",
        "TRAP_VIOLATION",
        "TYPE_MISMATCH_CLASH",
        "NON_CONVERGENT_TACTIC_LOOP",
        "DEFINITIONAL_EXPANSION_LOOP",
        "AXIOM_POLLUTION"
      ]
    },
    "failedTrajectory": {
      "type": "object",
      "properties": {
        "tacticScript": { "type": "string" },
        "compilerError": { "type": "string" },
        "failingGoal": { "type": "string" }
      },
      "required": ["compilerError"]
    },
    "minimalCounterexampleOrClash": {
      "type": "string",
      "description": "Concrete mathematical witness showing why the proposition is false-as-stated or incompatible."
    },
    "bannedSearchDirections": {
      "type": "array",
      "items": { "type": "string" },
      "description": "Explicit proof tactics, lemma positing styles, or assumptions that must NOT be attempted again."
    },
    "conservedCoreLemmas": {
      "type": "array",
      "items": {
        "type": "object",
        "properties": {
          "name": { "type": "string" },
          "type": { "type": "string" },
          "proof": { "type": "string" }
        },
        "required": ["name", "type"]
      }
    }
  }
}
```

3. **Negative Constraint Feeding**:
   * Subsequent runs of `/prove` or `/autoprove` on the target must ingest all existing `TypedObstructionPacket` entries for that target.
   * If a prover proposes a tactic or sublemma pattern listed under `bannedSearchDirections`, the orchestrator rejects the plan before invoking the compiler.

### 2.3 Pillar III: Goutev's Relational Invariant Formulation
The repository strictly rejects naive coordinate metrics, standalone Euclidean norms, and unreferenced scalar potentials.

1. **Ban on Standalone Coordinate Metrics**:
   * Asserting inequalities of raw operator norms (e.g. $\|A\| \le \|B\|$) over coordinate representations without an explicit reference state or modular gauge is prohibited.
   * Raw Euclidean coordinates, unbonded Christoffel symbols, and chart-dependent metrics violate Goutev's Principle and trigger Trap T1 / T13.
2. **Canonical Relational Shapes**:
   * All physical and geometric statements must be formulated via:
     * **Intertwining Operators & Representations**: Morphisms $T : V_1 \to V_2$ satisfying $T \circ \pi_1(g) = \pi_2(g) \circ T$.
     * **Algebra Homomorphisms & Embeddings**: Morphisms preserving algebraic operations across finite subalgebras into inductive colimit towers.
     * **Colimit Cocycles & Inductive Limits**: Direct inductive colimit limits across the $\mathcal{A}_\infty$ continuum (`TensorTowerColimit.lean`, `UHFInductiveColimitBoundary.lean`).
     * **Relative Densities & Potentials**: Radon-Nikodym derivatives, modular Hamiltonians ($K = -\log \rho$ relative to reference state $\rho$), and Bregman divergences ($D_L(\theta, \theta_0)$).
3. **The Gauge Law**:
   * Scale is gauge; normalization is gauge fixing.
   * Every theorem asserting a normalized physical property must expose the normalization map, the gauge witness, and the coherence invariance under positive rescaling ($x \sim \lambda x, \lambda > 0$).

### 2.4 Pillar IV: Automated Certification & Zero-Boilerplate Auditing
To maintain immaculate code quality across thousands of declarations without manual audit fatigue:

1. **Companion Audit Emitters**:
   * Every formalized Lean owner file must be accompanied by an automated audit emitter command (`python3 tools/infra/opengauss_cli.py certify --file <file> --write-audit --verify-kernel`).
   * The emitter and Gate 4 reviewer (`review <file> --gate GATE_4 --verify-kernel`) run static AST checks followed by locked kernel verification to verify:
     * Axiom purity: `#print axioms <decl>` $\subseteq \{\texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}\}$.
     * Zero sorries, zero admits, zero vacuous wrappers (`Prop := True`).
     * Zero 17-Trap violations (T1–T17), including T16 (Anti-Surrogate), Gate 2.5 / T17 (Model Witnessing), and pre-commit proof-proxy rules.
2. **Lean Metaprogramming Attribute Support**:
   * Formal modules may expose declarations annotated with repo-native attributes:
     * `@[owner_target_tag]`: Declares the canonical owner of a mathematical theorem.
     * `@[bridge_target_tag]`: Declares a verified transport map between representations.
     * `@[socket_debt_tag]`: Explicitly marks deferred literature sockets with typed boundary requirements.
3. **Audit Receipts as First-Class Artifacts**:
   * Audits produce machine-readable JSON receipts (`AuditCertificateReceipt`) stored in `artifacts/qms/`.
   * Staged immediately into Git via `git add -A` under the Continuous Tracking Mandate.

---

## 3. Complete CLI Command Reference (Commands 1 through 15)

The OpenGauss unified command suite provides 15 mathematically grounded, non-destructive tools:

| Cmd # | Command | Primary Role | Inputs | Outputs / Artifacts |
|---|---|---|---|---|
| **1** | `/prove` | Top-Down Assume-and-Recurse Prover | Headline signature, target type | Decomposed lemma plan, glue proof, Anti-T11 check |
| **2** | `/check` | Counterexample Hunter & Consistency Auditor | Expression, candidate hypotheses | Consistency report, counterexample risk rating |
| **3** | `/refute` | Adversarial Screener (17-Trap Catalog) | Lean source files / directories | Trap violations report (T1–T17 & Gate 2.5), REJECT/PASS verdict |
| **4** | `/draft` | Skeleton Drafter | Headline name, signature, sublemmas | Lean declaration skeleton with explicit leaf sorries |
| **5** | `/review` | Independent QMS Auditor (Gate 2 / Gate 4) | Target Lean file, `--gate`, `--verify-kernel` | QMS-SOP-IAA-001 audit report, locked kernel & axiom verdict |
| **6** | `/checkpoint`| State Saver & Continuous Tracker | Commit message, `--stage-path` | Staged git index (`git add`), CheckpointReceipt JSON |
| **7** | `/refactor`| Proof Refactorer & Redundancy Cleaner | Lean source file | Monolithic block (>25 lines) extraction plan |
| **8** | `/golf` | Proof Optimizer | Lean source file | Tactic compression suggestions (`rfl`, `ring`) |
| **9** | `/autoprove`| Autonomous Multi-Cycle Engine | Target file, max cycles | Iterative proof state, M10 Anti-Compaction re-hydration |
| **10**| `/formalize`| Two-Phase Interactive Synthesis | Informal math spec, phase (1/2) | Categorical anchor mapping, typed target check |
| **11**| `/autoformalize`| End-to-End CAS to Lean Candidate Translator | CAS type (SymPy/M2/GAP), expr | Candidate Lean 4 theorem (`verified: false`) for kernel check |
| **12**| `/handoff` | Cross-Session Context Preserver | Active targets, checkpoints, dead routes| Serialized `PLAN.md` markdown with anchor records |
| **13**| `/discover`| Pre-Flight Discovery & Anti-Duplication Gate | Candidate concept, signature query | Canonical Mathlib/repo matches, import recommendations |
| **14**| `/quarantine`| Residue Quarantine & Obstruction Emitter | Failed proof session / trap violation | `TypedObstructionPacket` JSON in `artifacts/residue_quarantine/` |
| **15**| `/certify` | Companion Certification Emitter | Verified Lean file, `--write-audit`, `--verify-kernel` | `<Module>Audit.lean`, kernel-verified `#print axioms` receipt |

---

### Command 1: `/prove` (Top-Down Assume-and-Recurse Prover)
* **Objective**: Decompose a complex mathematical theorem into consumer-minimal sublemmas and compile the glue proof before closing leaves.
* **Operational Flow**:
  1. Receive headline theorem name and target type.
  2. Synthesize child lemma types matching *strictly what the parent requires* (Anti-T11 Law).
  3. Emit glue tactic (`by exact h_sub1 h_sub2 ...`).
  4. Verify quantifier compatibility (Anti-T7 Law: no existential-to-universal inversion).
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py prove \
    --headline "clifford_so_isomorphism" \
    --type "CliffordAlgebra Q ≃ₗ[ℝ] SpinorEndomorphism" \
    --sublemmas '[{"name": "h_basis", "type": "HasOrthogonalBasis Q"}, {"name": "h_dim", "type": "Module.finrank ℝ (CliffordAlgebra Q) = 16"}]' \
    --glue "exact clifford_iso_of_basis_dim h_basis h_dim" \
    --json
  ```

---

### Command 2: `/check` (Ground-Truthed Counterexample Hunter)
* **Objective**: Evaluate proposed mathematical hypotheses against known boundary conditions and CAS models to refute false statements before proof generation begins.
* **Operational Flow**:
  1. Inspect hypotheses for contradiction ($0 = 1, \text{False}$ leading to vacuous proofs) or triviality ($x = x, \text{True}$).
  2. Inspect quantifier ordering for $\exists \forall$ inversion (Trap T2/T2′).
  3. Check metric signature validity (e.g., forbidding positive-definite assumptions on indefinite Krein spaces).
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py check \
    --expr "∀ (V : Type*) [KreinSpace ℝ V] (x : V), inner_product x x ≥ 0" \
    --hyp "Krein spaces possess indefinite metric with signature (p, q)" \
    --json
  ```

---

### Command 3: `/refute` (Adversarial False-as-Stated Screener)
* **Objective**: Screen Lean source code against the authoritative **17-Trap Catalog (T1–T17)**:
  * **T1**: Raw chart-coordinate extraction off-basepoint without bundle pairing.
  * **T2 / T2′**: Free-family quantifiers & $\exists\forall$ quantifier inversion.
  * **T3**: Global flatness / locally constant charts asserted globally (`HasLocallyConstantChartAt`).
  * **T4**: Vacuous binders & degenerate hypotheses (`0 = 0`, `True`, `x = x`).
  * **T5**: Localized headline leaks (restricting global theorem to coordinate chart).
  * **T6**: Hypothesis packaging into self-assuming hypotheses closed via `exact h` (prohibited).
  * **T7**: Family-as-input vs. existential output inversion.
  * **T8**: Per-fibre continuity vs. joint continuity confusion.
  * **T9**: Two-sided interval derivatives on smooth cutoffs (`HasDerivAt` on `Icc`/`Ici`).
  * **T10**: $C^\infty$ at boundary over-demand.
  * **T11**: Over-strong / non-tensorial posits violating consumer minimality.
  * **T12**: Multi-conjunct $\exists$-freedom over-constraints.
  * **T13**: Metric signature & orientation clashes (e.g. Euclidean norm on indefinite space).
  * **T14**: Constant factor & dimension scaling mismatches.
  * **T15**: Definitional expansion loops on categorical colimits (`TensorTower`, `Colimit`, `Quotient`).
  * **T16**: Semantic Surrogate / Scalar Toy Proxy (4 gates: scalar trace/det proxy structs, pre-commutator homomorphism collapse, carrier-matched non-commutativity witness requirement, and scalar tactic misuse `ring`/`linarith` on unprojected operators).
  * **T17**: Unwitnessed Structure / Model Non-Degeneracy Risk (Gate 2.5: every `structure`/`class` must have a closed constructive inhabitant or `Inhabited` instance free of `axiom`/`sorry` taint and ambient variables).
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py refute lean/InfoGeometry/Canonical/MyFile.lean --strict --json
  ```

---

### Command 4: `/draft` (Skeleton Drafter)
* **Objective**: Generate a clean, standards-compliant Lean 4 skeleton containing standard copyright headers, Mathlib imports, namespace declarations, explicit leaf `sorry` lemmas, and a glued parent theorem.
* **Operational Flow**:
  1. Format docstrings and declaration signatures.
  2. Place consumer-minimal child lemmas before the parent.
  3. Compile parent proof via glue tactic.
  4. Auto-invoke continuous tracking checkpoint upon writing to disk.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py draft \
    --headline "weyl_projective_equiv" \
    --signature "(x y : ProjectiveSpace ℝ V) : x ≈ y ↔ ∃ (c : ℝ), c > 0 ∧ y = c • x" \
    --sublemmas '[{"name": "weyl_ray_lift", "type": "∀ x, ∃ v, x = Ray ℝ v"}, {"name": "ray_equiv_scale", "type": "∀ v w, Ray ℝ v = Ray ℝ w ↔ ∃ c > 0, w = c • v"}]' \
    --namespace "InfoGeometry.Canonical" \
    --output "scratch/weyl_projective_skeleton.lean"
  ```

---

### Command 5: `/review` (Independent QMS Read-Only Auditor)
* **Objective**: Conduct strict, independent line-by-line code, trap, and scope preflight audits under **QMS-SOP-IAA-001**.
* **Gate Modes**:
  * `--gate GATE_2`: Adversarial pre-proof audit. Rejects for trap errors; flags `REQUEST_CHANGES` on warnings, sorries, or scope inflation keywords ("proves quantum gravity", "unifies everything").
  * `--gate GATE_4`: Static preflight by default. A clean result is `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED` (`kernel_checked: false`), not acceptance. Add `--verify-kernel` to build the owner and run its qualified `#print axioms` audit under the shared build lock; disallowed axioms or compile failures produce `REJECTED`.
* **Source truth gates**: Both review gates reject repository-authored `axiom`/`postulate`, `sorry`, `admit`, and `sorryAx` tokens after Lean comments and strings are removed. Kernel audit output may include Lean/Mathlib foundational axioms, but those are dependencies of checked proofs and are not permission to declare project axioms. Review also detects theorem constructors that merely assemble a multi-field `Prop` structure from field proofs; the individual owner theorems must be reviewed directly. This structural check does not depend on names such as `Certificate`, `law`, or `witness`, and does not reject a predicate structure that has no aggregate theorem constructor.
* **Commit-hook parity**: Run `python3 tools/quality/proof_proxy_staged_gate.py` during `/review` or `/checkpoint` before commit. It inspects the staged Lean source and enforces the same no-axiom/no-hole and aggregate-proof-wrapper checks as the pre-commit hook. It is a static source gate; only `--verify-kernel` establishes compilation and theorem axiom evidence.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py review lean/InfoGeometry/Canonical/TensorTowerColimit.lean --gate GATE_4 --verify-kernel --json
  ```

---

### Command 6: `/checkpoint` (State Saver & Continuous Tracker)
* **Objective**: Enforce the **Continuous Tracking Mandate**. Record repository state and stage specified paths (`--stage-path`) to protect work from rogue `git restore` operations, emitting a structured `CheckpointReceipt`.
* **Receipt Fields**: Timestamp, staged files list, unstaged files list, untracked files list, git HEAD hash, status, message.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py checkpoint -m "Closed leaf lemma h_basis via Mathlib basis_ortho" --stage-path lean/InfoGeometry/Canonical/MyFile.lean --json
  ```

---

### Command 7: `/refactor` (Proof Refactorer & Redundancy Cleaner)
* **Objective**: Enforce the **Lean File Size & Lemma Reuse Mandate**. Scan Lean owner files for monolithic proof blocks exceeding 25 lines and generate automated extraction plans for intermediate `have` statements.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py refactor lean/InfoGeometry/Canonical/ErlangenColimitResolution.lean --json
  ```

---

### Command 8: `/golf` (Proof Optimizer)
* **Objective**: Eliminate proof bloating and reduce elaboration latency. Identify redundant `simp; ring` sequences, replace tactic-mode `:= by exact rfl` with term-mode `:= rfl`, and replace definitional `simp only [id]` with `rfl`.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py golf lean/InfoGeometry/Canonical/SolderingIsomorphism.lean --json
  ```

---

### Command 9: `/autoprove` (Autonomous Multi-Cycle Engine & M10 Re-Hydration)
* **Objective**: Inspect open proof debt and maintain anti-compaction state across multi-wave proof cycles.
* **Anti-Compaction M10 Discipline**:
  * Automatically ingests active `TypedObstructionPacket` JSONs from `artifacts/residue_quarantine/` for the target file so iterations never repeat refuted trajectories.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py autoprove lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean --cycles 1 --max-cycles 5 --json
  ```

---

### Command 10: `/formalize` (Two-Phase Interactive Synthesis)
* **Objective**: Bridge informal mathematical statements into categorical architecture before generating Lean source.
* **Phases**:
  * **Phase 1 (Alignment)**: Maps informal concepts to canonical categorical owners (`TensorTowerColimit`, `SpacetimeParabolicQuotient`, `SolderingIsomorphism`) and screens spec text against the 17 Traps.
  * **Phase 2 (Target Contract Check)**: Requires an explicit typed target (`NEEDS_TYPED_TARGET`) rather than manufacturing a vacuous placeholder theorem.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py formalize --spec "The direct colimit of finite Clifford algebras embeds into the UHF C*-algebra continuum." --phase 1 --json
  ```

---

### Command 11: `/autoformalize` (End-to-End CAS to Lean Candidate Translator)
* **Objective**: Translate computer algebra identities (SymPy, Macaulay2, GAP) into candidate Lean 4 theorems (`verified: false`, `verification_status: "not_run"`) ready for kernel checking.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py autoformalize \
    --cas sympy \
    --expr "sl2 matrix det = 1" \
    --name "sl2_det_identity" \
    --json
  ```

---

### Command 12: `/handoff` (Cross-Session Context Preserver)
* **Objective**: Preserve critical mathematical context across developer or subagent sessions. Serializes active targets, verified checkpoints (0 sorry), disproven dead routes, and prioritized next actions into `PLAN.md`.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py handoff \
    --targets "InfoGeometry.Canonical.TensorTowerColimit" \
    --checkpoints "colimit_cocycle_cocondition" "clifford_cylinder_split" \
    --dead-routes "Unbounded colimit definitional unfolding (Trap T15)" \
    --out "PLAN.md" \
    --json
  ```

---

### Command 13: `/discover` (Pre-Flight Discovery & Anti-Duplication Gate)
* **Objective**: Implement **Pillar I**. Scan `lean/InfoGeometry/` and Mathlib for existing carriers, structures, classes, defs, and lemmas before any new symbol is posited.
* **Operational Flow**:
  1. Tokenize the search query and scan repository Lean modules and Mathlib.
  2. Identify matching carriers (`carriers_found`), lemmas (`lemmas_found`), and canonical module imports (`recommended_imports`).
  3. Emit `deduplication_warnings` whenever a query matches an existing fundamental carrier so agents reuse the canonical type instead of introducing a duplicate wrapper.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py discover \
    --query "split quaternion" \
    --json
  ```

---

### Command 14: `/quarantine` (Residue Quarantine & Obstruction Emitter)
* **Objective**: Implement **Pillar II (The Newton-Jung-Spire Loop)**. When a proof attempt fails or a refuter triggers, package the failure into an immutable `TypedObstructionPacket` JSON in `artifacts/residue_quarantine/`.
* **Operational Flow**:
  1. Record the source file, violated trap ID (`T1–T17`), failure description, minimal counterexample, and explicit negative constraint.
  2. Persist `artifacts/residue_quarantine/obs_<timestamp>_<hash>.json` (or via `opengauss_screener.py --quarantine` as `Q_<trap>_<timestamp>_<hash>.json`).
  3. Automatically feed the negative constraint into subsequent `/prove` and `/autoprove` runs targeting that file.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py quarantine \
    --file "lean/InfoGeometry/Canonical/ColimitBoundary.lean" \
    --trap "T15" \
    --desc "Maximum recursion depth exceeded during definitional unfolding of direct limit" \
    --counter "Unbounded dsimp over colimit tower" \
    --constraint "DO NOT unfold Colimit definitions directly; use opaque projection lemmas" \
    --json
  ```

---

### Command 15: `/certify` (Companion Axiom Certification Script Generator)
* **Objective**: Implement **Pillar IV**. Extract all theorem and lemma declarations (with their active namespace qualifications) from a target Lean file and emit a companion `<Module>Audit.lean` script with `#print axioms` checks for locked kernel verification.
* **Operational Flow**:
  1. Strip comments/strings and parse all `theorem` and `lemma` declarations along with their enclosing `namespace ... end` scopes.
  2. Generate `<Module>Audit.lean` importing the target module and running `#print axioms` on every theorem.
  3. With `--verify-kernel`, build the owner module and run the generated `#print axioms` script under the shared lock. The receipt records per-theorem axioms and rejects dependencies outside `[propext, Classical.choice, Quot.sound]`, including direct source `axiom` declarations.
* **CLI Invocation**:
  ```bash
  python3 tools/infra/opengauss_cli.py certify \
    --file lean/InfoGeometry/Canonical/TensorTowerColimit.lean \
    --write-audit \
    --verify-kernel \
    --json
  ```

---

## 4. Dual-Gate Integration Workflow (Gate 0 through Gate 4)

The OpenGauss workflow operates under strict QMS-SOP-IAA-001 role separation: Drafting Agent (**G-A**), Adversarial Audit Agent (**A-A**), and Acceptance Quality Agent (**QA-A**) must never be occupied by the same agent context.

```
       +--------------------------------------------------------------+
       |             DUAL-GATE PROTOCOL LIFECYCLE PIPELINE            |
       +--------------------------------------------------------------+
                                      |
  [GATE 0: Discovery Gate]            v
  Pre-flight AST & Mathlib Scan  ===========> /discover (Anti-Duplication Law)
                                      |
  [GATE 1: Formal Draft]              v
  Skeleton & Consumer Glue       ===========> /draft, /prove (Anti-T11 Law)
                                      |
  [GATE 2: Adversarial Audit]         v
  17-Trap & Counterexample Hunt  ===========> /refute --strict, /check, /review --gate GATE_2
                                      |
  [GATE 2.5: Model Witnessing]        v
  Non-Degeneracy & T17 Check     ===========> Constructive inhabitant / Inhabited (0 sorry/axiom)
                                      |
                     +----------------+----------------+
                     |                                 |
          [GATE 2 & 2.5 PASS]               [GATE 2 / 2.5 REJECT]
                     v                                 v
  [GATE 3: Corrective Revision]         [Pillar II Quarantine Loop]
  Targeted leaf proof closure           Emit TypedObstructionPacket (/quarantine)
  via /autoprove, /refactor, /golf      into artifacts/residue_quarantine/
                     |                                 |
                     +----------------+----------------+
                                      |
  [GATE 4: Independent Acceptance]    v
  Locked Kernel & Axiom Audit    ===========> /review --gate GATE_4 --verify-kernel
                                              /certify --write-audit --verify-kernel
                                      |
  [Continuous Tracking Checkpoint]    v
  Locked Lake build & Git Staging ===========> /checkpoint (--stage-path / git add)
```

### Gate 0: Pre-Flight Discovery Gate (`/discover`)
* **Agent Role**: Scouting Agent / Proposer.
* **Mandatory Action**:
  * Execute `/discover` to search Mathlib and the local declaration DAG.
  * Check existing categorical owners in `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md`.
  * Ingest any existing `TypedObstructionPacket` files in `artifacts/residue_quarantine/` to retrieve `bannedSearchDirections`.
* **Pass Criterion**: Zero duplication of existing theorems; target signature satisfies Goutev's Relational Invariant Formulation (Pillar III).

### Gate 1: Formal Draft & Skeleton Generation (`/draft`, `/prove`)
* **Agent Role**: Drafting Agent (**G-A**).
* **Mandatory Action**:
  * Define headline theorem signature.
  * Posit consumer-minimal helper lemmas (Anti-T11 Law).
  * Write immediate glue proof (`by exact ...`) compiling the parent theorem.
  * Place explicit, narrowly-typed `sorry` leaves for unproven sublemmas.
  * Write draft strictly into a sandbox environment (`scratch/`), **never touching live owner files**.
* **Pass Criterion**: Skeleton compiles cleanly in Lean 4 with explicit leaf sorries.

### Gate 2 & Gate 2.5: Independent Adversarial Review & Model Witnessing (`/refute`, `/check`, `/review`)
* **Agent Role**: Independent Audit Agent (**A-A**) — non-overlapping with G-A.
* **Mandatory Action**:
  * Screen draft against the **17-Trap Catalog (T1–T17)** and Git pre-commit/pre-push hook rules using `/refute <file> --strict`.
  * Enforce **Trap T16 (Anti-Surrogate / Operator-Algebraic Root)**: verify zero scalar proxy structs, zero pre-commutator homomorphism collapses, presence of a closed carrier-matched non-commutativity witness, and zero unprojected scalar tactic misuses (`ring`/`linarith`).
  * Enforce **Gate 2.5 / Trap T17 (Mandatory Model Witnessing & Non-Degeneracy)**: verify that every declared `structure` or `class` has a closed constructive inhabitant or `Inhabited` / `Nonempty` instance free of ambient `section` `variable` dependencies and transitively free of local or imported `axiom`, `opaque`, `sorry`, or `admit` taint.
  * Attempt counterexample models via `/check`.
  * Perform line-by-line static preflight audit using `/review <file> --gate GATE_2`.
* **Branching Protocol**:
  * **If PASS**: Advance to Gate 3 for leaf proof closure.
  * **If REJECT / OBSTRUCTED**:
    1. Invoke `/quarantine` immediately.
    2. Split trajectory into Conserved Core (Gold) and Frontier Residue (Slag).
    3. Emit `TypedObstructionPacket` JSON to `artifacts/residue_quarantine/`.
    4. Register banned search tactics into `PLAN.md` via `/handoff`.
    5. Return to Gate 1 with updated constraints.

### Gate 3: Corrective Revision & Leaf Closure (`/autoprove`, `/refactor`, `/golf`)
* **Agent Role**: Prover Worker Swarm.
* **Mandatory Action**:
  * Close leaf sorries using native Mathlib lemmas and tactic chains (`ring`, `linarith`, `simp`, `apply`).
  * Enforce Anti-Compaction M10 Re-Hydration: log dead routes and reload state from `artifacts/residue_quarantine/` and disk on context refresh.
  * Refactor monolithic blocks (>25 lines) using `/refactor`.
  * Optimize tactic latency via `/golf`.
* **Pass Criterion**: All leaf sorries closed; zero sorries remain in the sandbox file.

### Gate 4: Independent Acceptance QA & Automated Certification (`/certify`, `/review`)
* **Agent Role**: Acceptance Quality Agent (**QA-A**) — non-overlapping with G-A and A-A.
* **Mandatory Action**:
  * Run `/review <file> --gate GATE_4 --verify-kernel` to perform static checks plus locked kernel compilation and `#print axioms` verification (note: without `--verify-kernel`, `/review --gate GATE_4` returns `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`, which is not acceptance).
  * Execute `/certify --file <file> --write-audit --verify-kernel` under the shared build lock (`run_locked_lake_build.py`) to generate and kernel-check the companion `<Module>Audit.lean` script.
  * Verify `#print axioms` output for every public declaration is strictly a subset of:
    `[propext, Classical.choice, Quot.sound]`
  * If certified, promote sandbox code to the live owner file via an ordinary, clean patch.
  * Run `/checkpoint` to stage changes into git (`--stage-path`) and emit `CheckpointReceipt`.
* **Pass Criterion**: Exit code 0, 100% locked kernel verification (`kernel_checked: true`), pristine Git staging.

---

## 5. Summary Operational Checklist for Agents

```text
[ ] STEP 0: Run /discover. Check Mathlib and Categorical Map. Do not reinvent existing symbols.
[ ] STEP 1: Ingest active TypedObstructionPackets from artifacts/residue_quarantine/. Respect bannedSearchDirections.
[ ] STEP 2: Verify Goutev's Principle: Is the observable relational, projective, or an intertwining map?
[ ] STEP 3: Write skeleton to scratch/ sandbox using /draft. Compile glue proof immediately.
[ ] STEP 4: Submit to independent A-A for /refute --strict, /check, and /review --gate GATE_2 against the 17-Trap Catalog (T1-T17), including T16 anti-surrogate gates, Gate 2.5 / T17 model witnessing, and pre-commit proof-proxy rules.
[ ] STEP 5: On failure, invoke /quarantine to preserve Core Gold and log Obstruction Slag in artifacts/residue_quarantine/.
[ ] STEP 6: Close leaf lemmas via /autoprove. Refactor monolithic blocks (>25 lines) with /refactor and optimize with /golf.
[ ] STEP 7: Submit to independent QA-A for /review --gate GATE_4 --verify-kernel and /certify --write-audit --verify-kernel.
[ ] STEP 8: Promote to live owner file only after 0 sorry, 0 traps, and standard axioms confirmed by the Lean kernel.
[ ] STEP 9: Immediately run /checkpoint (--stage-path) to stage verified files into Git.
```

---

*Authored by the OpenGauss Protocol Policy & Black Book Architect under QMS-SOP-IAA-001.*  
*InfoGeometry Autonomous Verification Standard — 2026.*
