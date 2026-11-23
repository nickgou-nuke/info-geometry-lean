# Polarized Z/2-Graded Operator Algebra E2E Test Suite

Opaque-box, 4-tier requirement-driven Lean 4 E2E test suite and verification
harness for features **F1–F17** of the Real Polarized $\mathbb{Z}/2$-Graded
Operator Algebra Framework (`tests/polarized_z2_e2e/`).

## Directory Layout

- `run_e2e.py` — Pure Python 3 stdlib E2E runner (no `pytest` dependency).
- `AxiomAuditHelper.lean` — Standalone `lean --run` module/olean axiom auditor
  and canonical inline `section E2EAxiomAudit` reference.
- `README.md` — Usage, CLI modes, tier layout, and F17 hygiene conventions.
- `Tier1_R1.lean` (`F1–F5`), `Tier1_R2.lean` (`F6–F8`), `Tier1_R3.lean` (`F9–F12`), `Tier1_R4.lean` (`F13–F16`) — Tier 1 feature tests (`>= 5` `t1_f{N}_*` theorems per feature, `>= 80` total).
- `Tier2_R1.lean` (`F1–F5`), `Tier2_R2.lean` (`F6–F8`), `Tier2_R3.lean` (`F9–F12`), `Tier2_R4.lean` (`F13–F16`) — Tier 2 boundary, edge-case, and R5 separation tests (`>= 5` `t2_f{N}_*` theorems per feature, `>= 80` total).
- `Tier3_CrossFeature.lean` — Tier 3 pairwise cross-feature integration tests (`>= 16` `t3_*` theorems).
- `Tier4_Applications.lean` — Tier 4 realistic end-to-end application scenarios (`>= 8` `t4_*` theorems).

Total Lean theorem floor: **>= 184** (`80 + 80 + 16 + 8`), plus **F17** repo,
branch, quality-gate, and axiom-audit automation.

## CLI Usage

```bash
# Strict mode (M6 Phase 1): all 10 tier files must exist and pass all 4 checks
python3 tests/polarized_z2_e2e/run_e2e.py --tier all

# Pre-M6 concurrent development mode (missing tier files or pending M1-M5 symbols/oleans => PENDING_IMPL)
python3 tests/polarized_z2_e2e/run_e2e.py --tier all --allow-pending-impl

# Alias for --allow-pending-impl
python3 tests/polarized_z2_e2e/run_e2e.py --tier 1 --syntax-lint

# Machine-readable JSON output on stdout
python3 tests/polarized_z2_e2e/run_e2e.py --tier all --allow-pending-impl --json

# F17 repo/branch/stash/protected-file hygiene checks only
python3 tests/polarized_z2_e2e/run_e2e.py --check-hygiene-only --json

# Skip Lean elaboration & kernel axiom replay (runs headers, test counts, quality gates, hygiene)
python3 tests/polarized_z2_e2e/run_e2e.py --tier all --skip-lean
```

### Flags

| Flag | Default | Description |
|---|---|---|
| `--tier {1,2,3,4,all}` | `all` | Select which tier(s) to verify. |
| `--allow-pending-impl`, `--syntax-lint` | `False` | Report missing tier files or unbuilt/pending M1–M5 imports as `PENDING_IMPL` while still enforcing headers, quality gates, test counts, and hygiene on present files. |
| `--skip-lean` | `False` | Skip Lean elaboration and `.olean` kernel axiom replay. |
| `--check-hygiene-only` | `False` | Run only F17 repository, branch, stash, and baseline checks. |
| `--json` | `False` | Emit a single JSON report object on stdout. |
| `--wait-for-build-lock` / `--no-wait-for-build-lock` | `--wait-for-build-lock` | Whether `run_locked_lean.py` waits for `/tmp/info-geometry-build.lock`. |
| `--timeout <sec>` | `300` | Subprocess timeout per Lean or quality-tool invocation. |

## Verification Checks

1. **(a) Lean Elaboration**: Runs `python3 tools/infra/run_locked_lean.py` on
   every selected tier file and `AxiomAuditHelper.lean`, verifying zero errors
   and confirming `E2E_AXIOM_AUDIT_PASS` when `section E2EAxiomAudit` is present.
2. **(b) Kernel Axiom Audit**:
   - Audits all imported `InfoGeometry.*` owner modules via
     `python3 tools/infra/axiom_check.py --quiet --json <modules>` (without
     holding an outer build lock so `flock -x` inside `axiom_check.py` cannot deadlock).
   - Elaborates each `Tier*.lean` file to a temporary `.olean` inside a
     `tempfile.TemporaryDirectory` (`run_locked_lean.py <file> -o <tmp.olean>`),
     runs `flock -x /tmp/info-geometry-build.lock lake env lean --run tools/infra/axiom_check.lean <tmp.olean>`,
     checks `MODULE_RESULT:<tmp.olean>:PASS`, and removes the temporary directory.
   - Permitted foundational axioms only: `{propext, Classical.choice, Quot.sound}`.
3. **(c) Quality & Staged-Gate Checks**:
   - Byte-0 exact 5-line Apache 2.0 2026 InfoGeometry header.
   - `tools/infra/opengauss_screener.py --strict --json` (never `--quarantine`).
   - `aggregate_prop_constructors` check (no `Prop`-field bundling wrappers).
   - `tools/quality/placeholder_audit.py --strict --format json`.
   - `tools/infra/axiom_audit.py --fail-on-gaps --format json`.
   - `tools/quality/detect_hollow_theorems.py --strict`.
   - `tools/quality/semantic_vacuity_gate.py --fail-on error`.
   - Comment/string/backtick-stripped `native_decide` scan.
   - `tools/quality/proof_proxy_staged_gate.py --strict` plus accurate
     git staged/unstaged status reporting.
4. **(d) F17 Repository & Baseline Hygiene**:
   - Current branch is `main`, with `refs/heads` containing only `["main"]`.
   - No new git stashes beyond the 4 pre-existing baseline stashes anchored at
     `pre-fold-main-working-tree-20261123`.
   - `PR #426` (`lean/InfoGeometry/Canonical/ConnesSpectralTripleBridge.lean`),
     `lakefile.lean`, `lean-toolchain`, and `lake-manifest.json` are clean vs `HEAD`.
   - Pre-existing baseline worktree files (`PREREQUISITES.md`,
     `lean/InfoGeometry/Clifford/All.lean`,
     `lean/InfoGeometry/Canonical/RealDoubledChiralKreinBridge.lean`) retain
     their exact recorded blob hashes.

## Standalone `Tier*_*.lean` Requirements

Because `lakefile.lean` is frozen and `tests/` files are not compiled into
`.lake/build/lib/lean/` under `run_locked_lean.py`, tier files **must not**
import other files under `tests/polarized_z2_e2e/`. Each `Tier*_*.lean` file:
- Starts at byte 0 with the 5-line Apache 2.0 2026 InfoGeometry header.
- Uses `set_option autoImplicit false`.
- Imports only `InfoGeometry.*`, `Mathlib.*`, and `Lean.Util.CollectAxioms` /
  `Lean.Elab.Command`.
- Embeds the canonical `section E2EAxiomAudit` `run_cmd` block documented in
  `AxiomAuditHelper.lean` so elaboration itself verifies local declarations
  emit `E2E_AXIOM_AUDIT_PASS`.
