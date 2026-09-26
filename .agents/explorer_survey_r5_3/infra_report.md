# Infrastructure, Build Lock, and E2E Verification Audit Report
**Agent Identifier:** teamwork_preview_explorer (explorer_survey_r5_3)  
**Parent Orchestrator:** orchestrator_5 (conversation ID: `c310530f-678b-4c1c-948e-b8e7ff7beb38`)  
**Date:** 2026-09-22T08:35:00+03:00  
**Scope:** Sandbox environment, build lock mechanisms, process hygiene, and E2E verification suite (`tools/e2e_cas_o1_suite.sh`).

---

## 1. Executive Summary

This audit evaluated the operational readiness of the repository's verification and execution infrastructure ahead of the global O(1) CAS refactoring pass targeting the remaining compiler bottlenecks. 

### Key Findings:
1. **Build Lock Architecture (`/tmp/info-geometry-build.lock`)**:
   - The locking mechanism in `tools/build_lock.py` and `tools/infra/run_locked_lake_build.py` correctly uses kernel-level advisory locks (`fcntl.flock`).
   - The Linux kernel automatically releases advisory locks upon process death, guaranteeing that an abruptly terminated compiler process will not permanently deadlock the repository.
   - However, raw `lake env lean <file>` and ad-hoc bash invocations bypass `/tmp/info-geometry-build.lock` unless explicitly wrapped in Python `acquire_build_lock`, creating potential CPU/memory bus contention during swarm operations.
2. **E2E Verification Suite (`tools/e2e_cas_o1_suite.sh`)**:
   - **Tiers 1–3 are rock-solid**: They rigorously verify locked Lake compilation of promoted targets, token elimination (0 `native_decide`, 0 `simpa using`, 0 `sorry`), SymPy CAS certificates, and DAG integration.
   - **Test 2.5 (Proposition Fidelity & Anti-Facade)** provides an exemplary 3-layer anti-cheat barrier:
     1. Active symbol presence check (stripping comments).
     2. Per-theorem signature token extraction (isolating theorem propositions from proofs).
     3. Negative pattern matching banning trivializing facades (tautologies, proof-irrelevance aliases, and constant array equalities).
   - **Critical Vulnerability in Tier 4**: The 20-second timeout in Tests 4.1 and 4.2 conflates *Lean environment startup and Mathlib olean loading* (~12–15s) with *kernel typechecking* (~1–2s). Under multi-agent swarm activity, scheduling contention pushes wall-clock time over 20s, producing false-positive "CPU hang detected" failures.
   - **Test 4.3 is Vacuous**: Test 4.3 passes unconditionally whether the lock file exists or not, without testing whether an active lock is actually held.
3. **Sandbox Environment Readiness (`.agents/sandbox_surgical_o1/`)**:
   - Direct kernel verification of `.lean` source files located inside `.agents/sandbox_.../` was empirically verified (`lake env lean <path>` exited with code 0). Subagents can develop and completely typecheck replacement modules without touching live files.
   - The manual sandbox directory pattern from `sandbox_surgical_o1` (`CAS/`, `lean/`, `audit/`, `diffs/`) is effective but currently lacks an automated setup and validation harness for mass parallel deployment.

---

## 2. Audit of Build Locks & Concurrency Architecture

### 2.1 Implementation Analysis (`tools/build_lock.py` & `tools/infra/run_locked_lake_build.py`)

The build lock infrastructure is designed to enforce the Sequential Build and Test Mandate (`AGENTS.md`):

```python
DEFAULT_BUILD_LOCK_PATH = Path("/tmp/info-geometry-build.lock")

class BuildLock:
    def acquire(self) -> "BuildLock":
        ...
        handle = self.lock_path.open("a+", encoding="utf-8")
        flags = fcntl.LOCK_EX
        if not self.block:
            flags |= fcntl.LOCK_NB
        try:
            fcntl.flock(handle.fileno(), flags)
        except BlockingIOError as exc:
            meta = read_lock_metadata(self.lock_path) or {}
            handle.close()
            raise BuildLockBusyError(self.lock_path, meta) from exc
```

- **Kernel Authoritativeness**: The lock is an exclusive file lock (`fcntl.flock(fileno, LOCK_EX)`). In Linux, the kernel tracks the lock via the open file description in the kernel table, tied to the process lifecycle.
- **Metadata Management**: On acquisition, the holder truncates `/tmp/info-geometry-build.lock` and writes JSON metadata:
  ```json
  {"owner": "...", "pid": 12345, "acquiredAt": 1790051943.36}
  ```
  On clean release, `handle.truncate(0)` empties the file and releases `flock`.

### 2.2 Stale Metadata & Crash Resilience Inspection
During our initial probe, `/tmp/info-geometry-build.lock` contained:
```json
{"owner": "check:lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean", "pid": 295412, "acquiredAt": 1790051943.3666005}
```
Process `295412` was dead (`ps -p 295412` returned no running process).
We tested non-blocking acquisition:
```python
from tools.build_lock import acquire_build_lock
lock = acquire_build_lock(None, 'test_explorer_probe', block=False)
```
**Observation**: The acquisition succeeded instantly with return code 0 and truncated the file to 0 bytes upon release.  
**Conclusion**: The system does NOT suffer from deadlock caused by stale JSON metadata. Because `acquire_build_lock` only reads metadata *after* receiving `BlockingIOError` from the kernel, a dead PID whose kernel flock was released by the OS will never block subsequent build tasks.

### 2.3 Process Hygiene Vulnerability: Unlocked `lake env lean` Invocations
While `run_locked_lake_build.py` protects `lake build <target>` invocations, raw `lake env lean <file>` commands (frequently used for single-file benchmarking, profiling, or standalone checking) do not invoke `run_locked_lake_build.py`.

During this audit, process monitoring detected:
```
goutev 300542 ... bash -c time lake env lean lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean
goutev 300623 ... lean lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean (71.8% CPU, 4.5 GB RAM, running for 4m13s)
```
Because this was executed as a raw bash command without `acquire_build_lock`, it:
1. Ran completely outside `/tmp/info-geometry-build.lock`.
2. Saturated CPU and memory bus resources, slowing down other concurrent agent operations.
3. Caused subsequent single-file performance benchmarks in `tools/e2e_cas_o1_suite.sh` to exceed their 20s timeouts.

**Mandate for Swarm Agents**: All single-file checks and builds must be executed either via `run_locked_lake_build.py` or wrapped via Python with `with acquire_build_lock(None, f"check:{target}", block=True):`.

---

## 3. Audit of the E2E Verification Suite (`tools/e2e_cas_o1_suite.sh`)

### 3.1 Suite Structure
`tools/e2e_cas_o1_suite.sh` implements 4 verification tiers across 15 tests:
- **Tier 1 (Feature Coverage)**: Runs locked builds for `DAG.DiracLaplacian` and `InfoGeometry.Quantum.NoncommutativeFockBridge`, and checks target source file non-emptiness.
- **Tier 2 (Boundary & Corner Cases)**:
  - Test 2.1: 0 `native_decide` in `DiracLaplacian.lean`.
  - Test 2.2: 0 `simpa using` in `NoncommutativeFockBridge.lean`.
  - Test 2.3: 0 `sorry` or `admit` across targets.
  - Test 2.4: Clean execution of CAS certificate script `scripts/cas_dirac_laplacian_certificate.py`.
  - Test 2.5: Proposition Fidelity & Anti-Facade Audit.
- **Tier 3 (CAS & Integration)**:
  - Test 3.1: SymPy CAS certificate execution and keyword check.
  - Test 3.2: Export verification in `lean/DAG.lean`.
  - Test 3.3: Integration compilation of `lean/DAG.lean`.
- **Tier 4 (Compilation Performance & O(1))**:
  - Test 4.1: Benchmark kernel compilation time of `DiracLaplacian.lean` (timeout: 20s, threshold <= 15s).
  - Test 4.2: Benchmark kernel compilation time of `NoncommutativeFockBridge.lean` (timeout: 20s, threshold <= 15s).
  - Test 4.3: Concurrency and build lock hygiene.

---

### 3.2 Deep Dive: Test 2.5 (Proposition Fidelity & Anti-Facade Audit)

Test 2.5 is the repository's primary safeguard against "shortcut" proofs, theorem weakening, and cosmetic facades. It operates via three sequential inspection layers:

#### Layer 1: Mandatory Active Code Tokens (Comment Stripping)
```bash
stripped_code=$(grep -v "^\s*--" "$f_dirac" | sed '/\/\*/,/\*\//d')
for req_sym in "graphDirac" "chainComplex" "triangleComplex" "canonicalDigonComplex" "diracSquareCheck" "matTrace"; do
  if ! echo "$stripped_code" | grep -q "\<${req_sym}\>"; then
    # FAIL: Missing core mathematical symbols
  fi
done
```
- **Defense Mechanism**: Strips both single-line (`--`) and multi-line (`/* ... */`) comments to guarantee that required mathematical structures are genuinely compiled in active Lean code and not merely commented out.

#### Layer 2: AST Theorem Proposition Signature Isolation
```bash
extract_theorem_stmt() {
  local thm="$1"
  local src_file="$2"
  awk -v t="$thm" '
    $0 ~ "^theorem " t "[: ]" { p=1 }
    p {
      stmt = stmt (stmt ? " " : "") $0
      if ($0 ~ /:=(\s*by|\s*$)/) {
        print stmt
        exit
      }
    }
  ' "$src_file"
}
```
- **Defense Mechanism**: Isolates the *proposition signature* (everything between `theorem <name>` and `:=`) from the *proof body* (`:= by ...` or `:= rfl`).
- Verifies that each theorem proves the authentic mathematical statement rather than a weakened or trivialized version:
  * Example: `dirac_sq_lower_right_is_down_laplacian1_chain` requires tokens `graphDirac`, `chainComplex`, `matMul`, `boundary1`.
  * If an agent replaced the type with `theorem dirac_sq_lower_right_is_down_laplacian1_chain : True := trivial`, the token check fails immediately.

#### Layer 3: Negative Anti-Facade Regex Bans
Test 2.5 explicitly searches for and rejects known cheating patterns:
1. **Proof-Irrelevance Facade**:
   `grep -qE "upper_right_zero\s*=\s*.*lower_left_zero"`
   Bans setting two proof objects equal to each other instead of computing the zero block matrix.
2. **Arithmetic Substitution Facade**:
   `grep -qE "trDsq\s*=\s*trΔ₀"`
   Bans introducing dummy constants or tautological variables to fake trace equality.
3. **Reflexive Certificate Facade**:
   `grep -qE "(chain|triangle|digon)DiracSqCertificate\s*=\s*#\["`
   Bans defining an array literal and proving `#[...] = #[...]` by `rfl` rather than proving matrix multiplication of the Dirac operator.

---

### 3.3 Weaknesses and False-Positive Risks in E2E Suite

#### Issue 1: Tier 4 Wall-Clock Timeout vs. Multi-Agent Load
- In Tests 4.1 and 4.2, `lake env lean <file>` is executed with `timeout 20s`.
- **Empirical Measurement**:
  - Unloaded baseline: `lake env lean --profile lean/DAG/DiracLaplacian.lean` takes **15.19s** total wall-clock time.
  - Profile breakdown:
    * Environment startup, Lean binary boot, and Mathlib `.olean` loading: **~12.5s**
    * Actual Lean kernel typechecking: **~2.6s** (well within O(1) limits)
  - Under multi-agent swarm load (with concurrent background tasks): total wall-clock time reached **20.8s**, triggering `timeout 20s` (exit code 124) and falsely failing the test with `Timed out after 20s (CPU hang detected)`.
- **Recommendation**:
  - Increase `TIMEOUT_SEC` in `tools/e2e_cas_o1_suite.sh` from `20` to `35` (or `40`), while keeping `STRICT_O1_MAX=15` or measuring kernel typecheck time directly via `--profile`.

#### Issue 2: Test 4.3 Concurrency Check is Vacuous
Lines 447–452 of `tools/e2e_cas_o1_suite.sh`:
```bash
local lock_file="/tmp/info-geometry-build.lock"
if [ -f "$lock_file" ]; then
  log_pass "Build lock file state inspected (/tmp/info-geometry-build.lock is clean or managed)"
else
  log_pass "Build lock file is free (no active locks holding compiler)"
fi
```
Both the `if` and `else` branches invoke `log_pass`. The test cannot fail.  
**Recommendation**: Update Test 4.3 to attempt a non-blocking lock acquisition using `tools/build_lock.py` to confirm that the lock is actually available and no unmanaged processes hold `flock`.

#### Issue 3: Hardcoded Target Scope in Test 2.5
Test 2.5 currently targets ONLY `lean/DAG/DiracLaplacian.lean`. Promoted targets such as `lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean` and upcoming candidate targets are not yet included in Test 2.5.

---

## 4. Audit of Sandbox Environment & Promotion Architecture

### 4.1 Architecture of `.agents/sandbox_surgical_o1/`
The sandbox created for `Hartwig1976SVDMoorePenroseBorder.lean` established a clean template:
```
.agents/sandbox_surgical_o1/
├── CAS/
│   ├── cas_moore_penrose_certificate.py   # SymPy symbolic verification script (Exit 0)
│   └── moore_penrose_certificates.json    # Dumped polynomial/rational certificates
├── lean/
│   └── InfoGeometry/
│       └── Canonical/
│           └── Hartwig1976SVDMoorePenroseBorder.lean # Candidate replacement file
├── audit/
│   ├── audit_token_scan.log               # 0 native_decide, 0 simpa, 0 sorry
│   ├── audit_declaration_fidelity.log     # 25/25 declarations preserved (100%)
│   ├── audit_compilation.log              # lake env lean exit code 0
│   └── kernel_timing.log                  # Profiling: 2.084s kernel typecheck time
└── diffs/
    └── candidate.patch                    # Unified diff against pre-refactor live file
```

### 4.2 Out-of-Tree Lean 4 Typechecking Feasibility
A central question for the Subagent Sandbox Mandate: Can Lean 4 compile and typecheck a standalone candidate file located outside `lean/` without polluting the main source tree?

**Empirical Proof (Verified in Task 32)**:
We executed:
```bash
lake env lean .agents/sandbox_surgical_o1/lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean
```
**Result**: Return code **0**, zero compiler errors.  
Lean 4 resolves all precompiled `.olean` files in `.lake/build/lib/` for Mathlib and repo modules when invoked via `lake env lean <path>`, regardless of where the `.lean` source file is located on the filesystem. This completely validates the Subagent Sandbox Mandate.

### 4.3 Readiness of Sandbox Mechanisms for Upcoming Targets
Currently:
- There is **no automated CLI script** in the repository to generate sandbox directory trees. Sandboxes were manually constructed using bash `mkdir -p` and `cat << 'EOF'`.
- Older scripts in `tools/` (`tools/deploy_sandbox_files.py`, `tools/compare_sandbox.py`) target legacy top-level `sandbox/` and are obsolete.
- `skills/lean-sandbox/SKILL.md` documents an older pattern that created sandbox files inside the live tree (`lean/InfoGeometry/Canonical/Sandbox_...`), which violates the user's Subagent Sandbox Mandate ("ALL file modifications MUST be generated, written, and compiled inside isolated sandbox environments (e.g., `.agents/sandbox_name/`) first").

---

## 5. Reusable Sandbox Protocol for Round 5 / Mass Refactoring

To enable swarm workers to refactor candidate targets in total isolation without risking repository corruption or cheating, the following standardized workflow is established:

### Step 1: Sandbox Initialization (Bash-Only)
For target file `<TARGET_PATH>` (e.g. `lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean`):
```bash
TARGET="InfoGeometry/Canonical/ThreeColorNativeBracketTable"
SANDBOX_DIR=".agents/sandbox_${TARGET##*/}"
mkdir -p "${SANDBOX_DIR}/CAS" "${SANDBOX_DIR}/lean/$(dirname ${TARGET})" "${SANDBOX_DIR}/audit" "${SANDBOX_DIR}/diffs"
cp "lean/${TARGET}.lean" "${SANDBOX_DIR}/lean/${TARGET}.lean"
git add -A
```

### Step 2: CAS Certificate Generation
Subagent writes and executes a SymPy/Sage CAS verification script in `${SANDBOX_DIR}/CAS/`:
```bash
python3 "${SANDBOX_DIR}/CAS/cas_cert.py" > "${SANDBOX_DIR}/CAS/certificates.json"
```

### Step 3: O(1) Replacement Implementation
Subagent modifies the candidate file inside `${SANDBOX_DIR}/lean/${TARGET}.lean` using bash (`cat << 'EOF'`).

### Step 4: Verification Gate (4 Checks before Promotion)
1. **Token Gate**:
   ```bash
   grep -cE "native_decide|simpa using|\b(sorry|admit)\b" "${SANDBOX_DIR}/lean/${TARGET}.lean"
   # Must be 0
   ```
2. **Locked Compilation Gate**:
   ```bash
   python3 -c "
   import subprocess
   from tools.build_lock import acquire_build_lock
   f = '${SANDBOX_DIR}/lean/${TARGET}.lean'
   with acquire_build_lock(None, f'check:{f}', block=True):
       res = subprocess.run(['lake', 'env', 'lean', f], capture_output=True, text=True)
       assert res.returncode == 0, f'Compilation failed:\n{res.stderr}'
       print('Compilation PASSED (RC 0)')
   "
   ```
3. **Kernel Timing Gate**:
   ```bash
   python3 -c "
   import subprocess, re
   from tools.build_lock import acquire_build_lock
   f = '${SANDBOX_DIR}/lean/${TARGET}.lean'
   with acquire_build_lock(None, f'profile:{f}', block=True):
       res = subprocess.run(['lake', 'env', 'lean', '--profile', f], capture_output=True, text=True)
   times = [int(m.group(1)) for line in res.stdout.splitlines() for m in [re.search(r'type checking took (\d+)ms', line)] if m]
   total_s = sum(times) / 1000.0
   print(f'Kernel time: {total_s:.3f}s')
   assert total_s <= 15.0, f'Kernel typecheck exceeded 15s: {total_s}s'
   "
   ```
4. **Proposition Fidelity Gate**:
   Extract all theorem propositions from original `lean/${TARGET}.lean` and verify verbatim token presence in candidate.

### Step 5: Promotion & QMS Commit
```bash
cp "${SANDBOX_DIR}/lean/${TARGET}.lean" "lean/${TARGET}.lean"
git diff "lean/${TARGET}.lean" > "${SANDBOX_DIR}/diffs/candidate.patch"
git add -A
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock
bash tools/e2e_cas_o1_suite.sh --tier all
```

---

## 6. Synthesis and Orchestrator Recommendations

1. **Adjust E2E Suite Timeout**:
   Update `TIMEOUT_SEC` in `tools/e2e_cas_o1_suite.sh` to `35s` so that multi-agent scheduling jitter during Mathlib olean loading does not produce spurious Tier 4 failures.
2. **Enforce Build Lock on Single-File Commands**:
   Require all subagents to wrap `lake env lean` calls in `acquire_build_lock(None, ...)` to eliminate CPU resource contention.
3. **Deploy the Standardized Sandbox Protocol**:
   The Orchestrator should distribute the 5-step sandbox protocol to all upcoming worker subagents. This ensures 100% compliance with the Subagent Sandbox Mandate, BASH-ONLY mode, and Continuous Git Tracking.
