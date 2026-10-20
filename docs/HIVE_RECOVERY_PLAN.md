# Hive recovery and pilot plan

## Objective

Bring the repository-owned Hive queue to a demonstrably working state for one
bounded finite Lean task, while preserving OpenGauss evidence boundaries. The
pilot must prove queue ownership and evidence flow before enabling a full
multi-worker beehive.

## Current evidence

- Hive queue and worker implementations exist under `tools/infra/hive_*.py`.
- The configured local Arango environment is
  `configs/local/hive_arango.env`.
- The AST/AQL DAG endpoint is `http://127.0.0.1:8530`, database
  `infogeometry`, while the Hive queue defaults to
  `http://127.0.0.1:8540`, database `hive_live`.
- Agent memory is a separate logical lane (for example `hive_memory` or
  `aiclaw_auto_rag`) and must not be conflated with either queue or DAG.
- The maintained Hive launcher exports both the repository root and `src/` on
  `PYTHONPATH`, so direct queue execution uses the same import path as workers.
- Host-side connectivity evidence is environment-specific. Run the queue
  checks against the resolved `HIVE_ARANGO_*` endpoint/database; run AST/AQL
  checks against the resolved `ARANGO_*` endpoint/database. Do not infer one
  lane's reachability from the other.
- No Hive worker processes are currently running.
- The Archon queue is separate and currently reports one completed and one
  failed task.

These observations do not establish that the host-side Arango service is down;
host connectivity must be checked outside the restricted execution context.

## Phase 0 — preserve state

1. Record `git status --short`, current commit, and existing queue counts.
2. Do not delete `.lake`, `.runtime`, queue records, or artifacts.
3. Do not use `git restore`, `lake clean`, or cache-destructive commands.
4. Keep Hive, Archon, and native Codex schedulers separate for the pilot task.

## Phase 1 — repair the launcher boundary

1. Ensure the maintained Hive wrappers export the repository root in
   `PYTHONPATH`, or invoke Python with an equivalent module-safe entry point.
2. Preserve the existing environment-file and credential handling.
3. Validate without exposing credentials:

   ```bash
   PYTHONPATH=. python3 tools/infra/hive_arango_queue.py --help
   python3 -m py_compile tools/infra/hive_arango_queue.py
   ```

4. Re-run the repository-owned wrapper rather than bypassing it in normal use.

## Phase 2 — verify Arango on the host

Run on the host where ArangoDB is expected to listen:

```bash
bash tools/infra/hive_ping.sh
PYTHONPATH=. python3 tools/infra/hive_arango_queue.py status
```

Classify the result explicitly:

- **reachable and authenticated:** continue;
- **connection refused:** start or repair the Arango service;
- **HTTP 401/403:** repair credentials or database permissions;
- **HTTP 404:** repair endpoint/database selection;
- **schema missing:** run the repository-owned `init` operation;
- **sandbox-only failure:** repeat on the real host before changing code.

Do not print passwords or place them in tracked files.

## Phase 3 — initialize and inspect the queue

After successful host connectivity:

```bash
PYTHONPATH=. python3 tools/infra/hive_arango_queue.py init
PYTHONPATH=. python3 tools/infra/hive_arango_queue.py status
PYTHONPATH=. python3 tools/infra/hive_arango_queue.py queue-stats
```

Confirm that collections, indexes, packet validation, task leases, and worker
heartbeat records are present. Preserve any existing failed tasks; do not
silently delete or rewrite their history.

## Phase 4 — start one worker lane

Start only MotherBee and one specialist worker first. Use the repository's
systemd user-unit installer or an equivalent supervised process:

```bash
bash scripts/install_hive_beehive_systemd_units.sh
systemctl --user status hive-motherbee.service
systemctl --user status hive-bee@default.service
```

If systemd is unavailable, run the documented one-shot MotherBee loop under a
supervisor. Record worker IDs and heartbeat timestamps.

Do not enable build, audit, promotion, research, and swarm workers all at once;
that obscures the first failure.

## Phase 5 — bounded pilot task

Use one finite theorem whose owner and carrier are already known. The task
packet must include:

- exact owner file and declaration;
- theorem contract and hypotheses;
- explicit non-claims;
- source hash;
- sandbox path for any candidate;
- requested worker role;
- required Lean command.

The pilot sequence is:

```text
enqueue
→ claim
→ heartbeat/lease renewal
→ candidate or failure
→ Lean check
→ complete or requeue
```

The pilot passes only if a failed task can be requeued without losing its
original packet and a successful task stores the exact Lean output.

## Phase 6 — add build and audit lanes

After the pilot succeeds:

1. Start the build worker.
2. Start the semantic/audit worker.
3. Test a deliberate failed Lean candidate.
4. Verify that audit status remains separate from compilation status.
5. Test lease expiry and reaping.
6. Test promotion refusal when `sorry`, `admit`, a custom axiom, or a vacuous
   proposition is detected.

Builds must remain serial and use the repository build lock.

## OpenGauss acceptance gates

Hive is operationally recovered only when all of these are observed:

- packet validation succeeds;
- task claim is atomic;
- worker heartbeat is recorded;
- expired leases are requeued;
- candidate source remains sandbox-only;
- `lake env lean` evidence is captured;
- locked build evidence is captured where required;
- placeholder, vacuity, and axiom scans run;
- auditor and QA roles are distinct from the author;
- failed tasks remain inspectable and are not promoted;
- the final report distinguishes kernel proof from provider output.

## Failure handling

If Phase 2 fails, stop at connectivity diagnosis. If Phase 4 fails, stop at
worker supervision. If Phase 5 fails, keep the task in failed/requeue state and
repair the packet or launcher before adding more workers. Do not compensate for
an infrastructure failure by weakening theorem contracts or promoting model
responses as proof.

## Completion report

The recovery report should contain:

- commit and configuration fingerprints without secrets;
- Arango endpoint/database and host-side connectivity result;
- schema and index status;
- worker IDs and heartbeat evidence;
- pilot task ID and packet hash;
- claim, lease, requeue, Lean, build, audit, and QA results;
- remaining failed tasks and known limitations.

The target is a reproducible finite pilot. A working pilot is evidence that the
Hive infrastructure operates; it is not evidence that every theorem lane or
every model provider is operational.
