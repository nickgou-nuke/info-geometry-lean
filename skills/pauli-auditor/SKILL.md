---
name: pauli-auditor
description: Enforces the Pauli Protocol to eliminate Total Symbolic Inflation (TSI) and Lyrical Overfit in Lean 4 formalizations. Use when reviewing code, validating new mathematical theories, or performing deep codebase audits for vacuity and "Agentic Cheating".
---
# Pauli Auditor Skill

This skill operationalizes the **Pauli Protocol** for formalizing physics and mathematics in Lean 4. It ensures that "Agentic Cheating" and "Lyrical Overfit" are eliminated.

## Core Directives

When auditing the repository, enforce the following mandatory directives (PAULI_MANDATE I–XI) plus the witness-dependency guardrail:

### 1. The "No-Mask" Mandate (Anti-Symbolic Inflation)
Any declaration in the `Canonical` lane that uses a "Physically Loaded Name" (e.g., `EinsteinEquation`, `PenroseUnification`) MUST be a `def` or a `theorem` that explicitly references and transforms a structure from the `Thermo` or `Geometry` foundational lanes. If a "Canonical" definition is just a collection of `Prop` fields (a "Wish List"), flag it as **Lyrical Overfit** and demand it be stripped of its name or deleted.

### 2. Functorial Connectivity (Anti-Floating Modules)
Every module in the repository MUST possess at least one **Value-Edge** (it must be consumed downstream or perform a foundational structural role). If a file contains only `import` statements and comments, it is **Informational Noise** and must be deleted. If a file contains definitions with zero internal or external consumers, it is a **Dead-Endpoint** and disqualified from the "Spire."

### 3. The Axiom-Surface Seal (Anti-Sorry)
No declaration marked with `@[rep_depth krein]` or `@[rep_depth canonical]` may depend, even transitively, on `sorryAx` or the `Admission` meta-tactic. Always verify with `#print axioms <decl>`. If any "synthetic trust" token or `sorry` is found, the module is marked **"Nicht einmal falsch!"** and must be isolated or rewritten.

### 4. Semantic Weight Ratio (Anti-Lyrical Overfit)
For every line of "Physically Descriptive Comment" in a `.lean` file, there must be at least two lines of **Tactical Proof** (`by ...`) or **Rigid Definition** (`:= ...`). If the prose outweighs the proof, the file is a **Novella**, not a **Theory**, and must be reduced or formalized.

### 5. The "Identity via Reflexivity" Audit (Anti-Cheating)
A "Victory of Unity" via `rfl` (reflexivity) is ONLY valid if the types being unified originate from **Disjoint Initial Modules**. If an `rfl` proof bridges `A = B` but both were defined within the same local file or "Canonical" folder solely for the purpose of being unified, it is **Agentic Triviality**. A true unification must bridge foundational gaps using a non-trivial intertwiner.

### 6. Anti-Existential Hypothesis (Anti Assumption-as-Theorem)
Prop dependency packages that carry existential obligations (for example, theorem hypotheses of the shape `_deps : SomeDependencies ...` where `SomeDependencies` stores `∃` fields) are not closure. They are tautological shells until constructive witnesses are provided in the theorem body or exported as concrete `def`s.

### 7. Interface Witness Fidelity (Anti Toy-Bridge Closure)
Do not accept "interface closure" from trivial witnesses (`fun x => x`, pure swap, immediate `rfl`) on universal presentation/intertwiner surfaces. At least one non-trivial witness must be shown on a mapped, rep-depth-relevant domain.

### 8. Metric Fidelity (Anti Proxy-Invariant Proofs)
If a lane defines an owner metric (for example, Krein via `kreinInner`), preservation theorems must be proven on that owner metric. Hilbert/`inner` proxy preservation does not count as physical closure for that lane.

### 9. Genuine Witness Dependency (Anti-Linter Masking)
Existential witnesses must be semantically used when named. Reject theorem surfaces that use linter-masking wrappers such as `∃ h : P, (let _ := h; Q)` when `Q` does not depend on `h`. For non-dependent existence claims, require idiomatic `∃ _ : P, Q`.

### 10. Anti-Residual Redirect
Definitions named as `*Residual` or anomaly residual carriers are not closure by themselves. Require an accompanying vanishing/zero theorem surface; naming the defect without proving its vanishing is a policy violation.

### 11. Parameter Admission
Reject noncomputable physical-parameter definitions (`temperature`, `inverseTemperature`, `beta`, `mass`, `coupling`, etc.) when they are introduced without an explicit existence witness theorem.

### 12. Public Uniqueness Mandate
Reject `private theorem` / `private lemma` uniqueness surfaces in `Canonical` / `Core` lanes. Uniqueness results that participate in architecture must be public and auditable.

## Workflow

1.  **Analyze the Axiom Surface:** Run `#print axioms` on any capstone theorem. Reject immediately if `sorryAx` is present.
2.  **Verify Tactical Density:** Read the `.lean` source. Ensure the ratio of Lean syntax/tactics to descriptive prose is at least 2:1.
3.  **Check Dependencies:** Use `DAG/ExportDecls.lean` or direct analysis to ensure the file has downstream consumers. Reject dead endpoints.
4.  **Confirm Functorial Lifting:** Trace physically-named definitions back to their roots. Ensure they bottom out in `Thermo/` or `Geometry/`.
5.  **Reject Existential Shell Inputs:** Flag theorem surfaces that consume existential `Prop`-packages as assumptions.
6.  **Probe Witness Triviality:** Flag universal interface/presentation/intertwiner declarations closed by identity/swap/reflexive witnesses.
7.  **Check Owner-Metric Preservation:** Flag proxy-metric (`inner`) invariants when owner metric (`kreinInner`) is available but unproven locally.
8.  **Check Residual Closure:** Flag residual definitions without a vanishing theorem companion.
9.  **Check Parameter Existence:** Flag noncomputable physical parameter defs without `exists_*` witness theorems.
10. **Check Uniqueness Visibility:** Flag private uniqueness theorems in Canonical/Core.
11. **Run Audit Gate:** `python3 tools/quality/pauli_seal_audit.py --root lean/InfoGeometry/Canonical --json-out reports/pauli-seal-audit.json`
12. **Deliver the Verdict:** State explicitly whether the code achieves **Nomological Closure** or if it is **"Nicht einmal falsch."** Provide strict, surgical refactoring instructions to fix it.
