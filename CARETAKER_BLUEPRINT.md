# 🤖 NATIVE CARETAKER BLUEPRINT

**CRITICAL INSTRUCTIONS FOR THE CODING AGENT:**

**Do not build an external Lean evaluator.**
**Use the REPO-NATIVE compiler bridge (`compilerBridgeServer`).**

**The REPO-TOOLCHAIN is pinned to Lean v4.28.0.**
**Do not use generic CLI backends; use the established RPC interface.**

---

## Objective
Operationalize the existing `Agent` bridge and `Audit` infrastructure to serve as a strict Policy Gate for the `info-geometry-lean` Spire.

## Non-negotiable doctrine
1. **The Kernel is the Judge:** Truth is decided by `IG.Compiler.validateDecl`.
2. **Canonical Statement Anchoring:** The `theoremTypeExprFingerprint` is the unique identifier of a theorem. If your code changes the fingerprint, the proof is rejected for "Statement Tampering."
3. **Architecture is Law:** The `RepDepth` adjacency rules in `Meta/Architecture.lean` are enforced by `#audit_architecture`.
4. **Sovereign Runtime:** All actions must eventually migrate to the local `nemoclaw onboard` sandbox on the DGX Spark.

---

## Phase 1 — Native Bridge Integration
**A. Connect to the `compilerBridgeServer`.**
   - Use the existing RPC layer (`Agent.ProofServerRpc`).
   - Primary Truth Source: `IG.Compiler.validateDecl`.
   - Capture:
     * `ok`: Must be true (no errors, no `sorry`).
     * `declFound`: Must be true.
     * `hasSorry`: Must be false.
     * `theoremTypeExprFingerprint`: Must match the repository's canonical fingerprint.

**B. Implement Fingerprint Verification.**
   - Before attempting a proof, record the `theoremTypeExprFingerprint` of the `sorry`-labeled target.
   - After the proof, call `validateDecl` again.
   - If the fingerprint has changed, you have rewritten the theorem. Roll back and fail.

---

## Phase 2 — Native Audit Compliance
**A. Ingest the Architecture.**
   - Read `lean/InfoGeometry/Meta/Architecture.lean` to understand the `RepDepth` valences.
**B. Run the Native Auditor.**
   - Use `lake run auditArchitecture` (or equivalent `Audit.lean` entrypoint).
   - Any `REGRESSION` or `WORMHOLE` violation in your proposed patch results in immediate rejection.

---

## Phase 3 — Closed-Loop Execution
**A. The Agent Loop:**
   1. **Retrieve:** Use the DAG artifacts to find the local neighborhood.
   2. **Propose:** Patch the `.lean` file.
   3. **Verify:** Call `validateDecl` and `auditArchitecture`.
   4. **Anchor:** Ensure fingerprints match and `sorry` is gone.
   5. **Submit:** Only PR code that is both Kernel-Valid and Architecture-Valid.

---

## Phase 4 — NemoClaw Migration
**A. Move the runtime into NemoClaw.**
**B. Use `nemoclaw onboard` as the lifecycle entrypoint.**
**C. Ensure the local NIM (`localhost:8000`) is the only inference source.**

---

## Deliverables
1. `tools/caretaker/` - A thin wrapper around the native RPC server that enforces the fingerprint and audit gates.
2. `config/toolchain.json` - Hard-pinned to `v4.28.0`.
3. `docs/CARETAKER_REQUIREMENTS.md` - Formal operational spec using these native terms.

---

## Success criteria
- `IG.Compiler.validateDecl` returns `ok: true`.
- `theoremTypeExprFingerprint` remains invariant.
- `Audit.lean` reports 0 regressions.
- No telemetry leaves the local DGX Spark network.
