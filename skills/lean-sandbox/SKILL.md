---
name: lean-sandbox
description: Use for implementing new Lean modules or complex refactors. Prevents repository corruption by using a temporary sandbox for development and verification before final integration.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# Lean Sandbox-First Workflow

This workflow is mandatory for all non-trivial code changes to ensure repository integrity and prevent build failures in the main tree.

## 1. Research & Dependency Mapping
- Identify the target file path and the required imports.
- Verify the existence and correct naming of all prerequisite symbols in the current `main` branch.
- Do NOT assume a symbol exists based on "synthesis notes" or "memory"; check the source file directly.

## 2. Sandbox Creation
- Create a temporary file: `lean/InfoGeometry/Canonical/Sandbox_<FeatureName>.lean`.
- Use a unique namespace: `namespace InfoGeometry.Canonical.Sandbox_<FeatureName>`.
- Copy all intended logic, imports, and definitions into this sandbox.

## 3. Iterative Development & Verification
- **Act**: Implement the logic in the sandbox.
- **Verify**: Run `lake build InfoGeometry.Canonical.Sandbox_<FeatureName>`.
- **Diagnose**: If the build fails, analyze the compiler output.
- **Fix**: Apply fixes ONLY to the sandbox file.
- **Repeat**: Continue the Act -> Verify cycle until the sandbox builds with **zero errors**.

## 4. Integration
- Once verified, move the sandbox to the final destination:
  ```bash
  mv lean/InfoGeometry/Canonical/Sandbox_<FeatureName>.lean lean/InfoGeometry/Canonical/<TargetName>.lean
  ```
- Update the namespace in the target file to match the directory structure:
  ```bash
  sed -i 's/Sandbox_<FeatureName>/<TargetName>/g' lean/InfoGeometry/Canonical/<TargetName>.lean
  ```

## 5. Final Validation
- Run a final build on the integrated module:
  ```bash
  lake build InfoGeometry.Canonical.<TargetName>
  ```
- Confirm the module is correctly linked in the canonical umbrella (`lean/InfoGeometry/Canonical/All.lean`) if required.

## 6. Cleanup
- Remove any temporary artifacts or log files generated during the process.
- Ensure no "Sandbox" namespaces remain in the codebase.

## 7. DAG Toolchain Order (when requested)
- Run only via:
  ```bash
  python3 tools/infra/run_full_dag_toolchain.py
  ```
- This enforces strict sequencing:
  1. `InfoGeometry.Audit`
  2. `InfoGeometry.AuditStrict`
  3. `refresh_decl_graph.py`
  4. `generate_theorem_surface_index.py`
  5. `generate_source_sink_compression.py`
  6. `generate_process_flow_report.py`
  7. `generate_semantic_flow_report.py`
  8. `check_semantic_flow_report.py --skip-generate`
  9. `generate_causal_report.py`
  10. `canonical_policy_lint.py`
- If a run is interrupted, rerun to completion before interpreting reports; partial reruns can leave mixed-generation artifacts that look like stale/deleted-file contamination.
- Do not push generated `artifacts/*` or derived DAG outputs unless explicitly requested.

**Safety Mandate:** Never overwrite an existing working file with untested code. Always prove the new code builds in isolation first.

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
- **Do not “resolve” debt with wording.** Progress must be structural, not just textual.
- **Do not remove debt labels** unless there is a native explicit Lean proof term checked by the kernel closing that specific debt.
- **Real progress** = replacing certificate/witness fields with theorem-backed native derivations.
