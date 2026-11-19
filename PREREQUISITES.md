# Prerequisites Check — Formal Math / Lean 4 (LEMMA)

**Verdict:** `MISSING`

## Summary

All machine-level tools and Lean 4 / Mathlib services required for the `Formal Math / Lean 4 (LEMMA)` execution path are installed and operational. However, the request does not specify the required LEMMA run inputs (`folder`, `problem`, `root`), so no `LEMMA run:` line could be produced.

## Checked Environment & Services (All Operational)

1. **Commands & GNU `timeout`**:
   - `leap`: found (`/home/goutev/.local/bin/leap`)
   - `state_manager_bin`: found (`/home/goutev/.local/bin/state_manager_bin`)
   - `lean_verifier_tool_bin`: found (`/home/goutev/.local/bin/lean_verifier_tool_bin`)
   - `lean_search_tool_bin`: found (`/home/goutev/.local/bin/lean_search_tool_bin`)
   - `timeout`: GNU-style `timeout 5s true` exited 0
2. **Pinned `leap-tools` Build**:
   - Verified `https://github.com/billkunghappy/LEAP-CLI` commit `f81ebec994884aba7dd78f903e403e3716b3787c` (`subdirectory: packaging/leap-tools`), no conflicting `leap-cli` distribution (`False`).
3. **`leap doctor`**:
   - Exited 0; local Lean backend at `/home/goutev/.leap/leap_lean` (`leanprover/lean4:v4.34.0`), probe theorem compiled with axioms `['propext', 'Classical.choice', 'Quot.sound']`, Mathlib search reachable.
4. **Verifier & Search Tool Probes**:
   - `lean_verifier_tool_bin`: exited 0 (`"is_valid": true`, `"is_infra_failure": false`, `"backend": "local"`).
   - `lean_search_tool_bin`: exited 0 (`"success": true`).

## Missing Items (User-Provided Request Inputs)

The `Formal Math / Lean 4 (LEMMA)` input check returned:

- `missing: folder: no text in its file` — A dedicated, writable LEMMA run folder (new, empty, or an earlier LEMMA run's folder containing `proof_graph.json` matching `problem` and `root`) is not specified in the request. The repository working directory (`/home/goutev/repos/info-geometry-lean`) holds project files and is not a LEMMA run folder.
- `missing: problem: no text in its file` — A single readable `.lean` problem file is not specified (the request lists multiple repository files/directories and new formalizations R1–R5).
- `missing: root: the theorem needs a plain name ([A-Za-z_][A-Za-z0-9_]*); ask the user to rename it` — A single plain theorem name (`[A-Za-z_][A-Za-z0-9_]*`) to prove is not specified in the request.

## Installation / Remediation Notes

- **Installed during this audit:** Nothing (outside install mode; all software prerequisites are already present and working).
- **What is needed to proceed on the `Formal Math / Lean 4 (LEMMA)` path:** The user must provide:
  1. A dedicated run `folder` path (absolute or `~/`, using only `A-Za-z0-9._+-/`, writable, new/empty or resuming the same problem/theorem run).
  2. A single readable `problem` `.lean` file path.
  3. A single plain `root` theorem name matching `[A-Za-z_][A-Za-z0-9_]*` declared in that problem file.
  (Optionally, a separate writable `solution` folder path not overlapping `folder`.)
- Note: Because this request targets multi-file repository formalization in `/home/goutev/repos/info-geometry-lean` rather than a single-theorem LEMMA proof run, the parent orchestrator may also note that the `Formal Math / Lean 4 (LEMMA)` path requires single-problem LEMMA inputs.
