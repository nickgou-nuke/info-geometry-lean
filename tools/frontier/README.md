# Frontier Tools

This directory contains the maintained semantic-block and frontier-discovery tooling.

For the exact operator methodology, including when to use `semanticSnapshot`,
`proofPrint`, and `proofSession`, see
[docs/ToolingMethodology.md](../../docs/ToolingMethodology.md).

## Maintained entrypoints

- `semantic_block_export.py`
- `semantic_snapshot.py`
- `proof_session.py`
- `proof_print.py`
- `socratic_cycle.py`
- `skynet_v2.py`
- `extract_module_patch.py`

## Purpose

Use this layer for:
- trusted semantic-block export of heavy Lean modules;
- server-backed elaboration snapshots that feel closer to the VS Code infoview;
- frontier exploration around a chosen seed theorem or module;
- extraction of prompt-ready local context for focused agent work.
- natural-language-first Socratic cycle packet scaffolding before Lean encoding.

## Current rule

For heavy files, prefer the external semantic export path instead of trying to infer structure from the raw declaration graph alone.

Outputs from this lane usually land under `reports/dag/`, but individual
entrypoints may also write to explicit caller-supplied paths.

## Snapshot Surface

Use `semantic_snapshot.py` when you want one packet that combines:
- semantic block structure for the whole file;
- the current environment fingerprint from the compiler bridge; and
- an optional extra bridge query such as `getProofState`, `checkSnippet`, or `validateDecl`.

For low-latency proof-state printouts, use `--proof-fast`. That switches to the
bridge-only path and skips the semantic-block and diagnostics-wait overhead.

For the cheapest one-shot printout, use `--print-fast`. That switches the bridge
query to `getGoalTargets`, which avoids building the full proof-state payload.

For finished declarations, `--bridge-method validateDecl --decl-name ... --proof-fast`
now auto-infers the declaration line when possible and avoids Lean pretty-printing
unless `--pretty-print-type` is requested.

In practice, `getGoalTargets` is the cheapest maintained proof-printout surface,
`getProofState` is the richer proof-state view, and `validateDecl` is the slower
structural check that confirms the declaration exists in the current snapshot and
is not backed by `sorry`.

For repeated queries on the same file, use `proof_session.py` through
`lake script run proofSession ...`. That keeps one bridge session open so the
first query pays the file elaboration cost and the following queries run on a
warm server state.

If you already know the target declaration or cursor location, prewarm the
session before `ready`:
- `lake script run proofSession <file> --prewarm-decl-name <fqdn> --prewarm-pretty-print-value`
- `lake script run proofSession <file> --prewarm-method getProofState --prewarm-line <n> --prewarm-character <c>`

The `ready` event includes a compact `prewarm` summary with timing and basic
status, but not the full proof payload.

For the fastest maintained cold one-shot proof-term printout, use
`proof_print.py` through `lake script run proofPrint ...`. It goes straight
through `getDeclValue` and prints the declaration value
instead of a larger snapshot packet.

The persistent session now also supports virtual buffer edits:
- `{"id": 1, "method": "didChange", "text": "...", "waitForDiagnostics": false}`
- `{"id": 2, "method": "reloadFromDisk", "waitForDiagnostics": false}`

For proof-term printout on the warm path, send:
- `{"id": 3, "method": "getDeclValue", "declName": "..."}`

This is the closest maintained operator surface to the “show me the compiled/elaborated view”
experience provided by the Lean VS Code plugin.

## Natural-Language Socratic Cycle

Use `socratic_cycle.py` to scaffold a full packet for:

1. Jungian generation,
2. repeated Socratic regeneration,
3. Pauli admission partition,
4. translator pass,
5. Lean batch handoff.

Example:

```bash
python3 tools/frontier/socratic_cycle.py \
  "DIII phase-flip anomaly to index bridge" \
  --out reports/frontier/socratic \
  --loops 3 \
  --lane InfoGeometry.Canonical \
  --owner-hint lean/InfoGeometry/Canonical/ProjectorEquivariance.lean \
  --owner-hint lean/InfoGeometry/Canonical/OperatorialCentralCharge.lean
```

Manual templates for team use:

- `tools/frontier/templates/socratic_cycle_packet.md`
- `tools/frontier/templates/pauli_admission_report.md`
