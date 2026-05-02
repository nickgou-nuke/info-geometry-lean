# Operator Quickstart

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This is the compressed operator surface for local Lean and DAG work.

Architecture reference:
- [LOCAL_TOOLCHAIN_ARCHITECTURE.md](LOCAL_TOOLCHAIN_ARCHITECTURE.md)

## 0. Opening Instruction (Name Equivalence Dictionary)

Before local patching, refresh the equivalence dictionary so nonstandard or legacy naming surfaces remain discoverable.

```bash
python3 tools/infra/generate_equivalence_dictionary.py \
  --curated-json docs/NameEquivalenceRegistry.json \
  --json-out reports/dag/equivalence-dictionary.json \
  --md-out reports/dag/equivalence-dictionary.md
```

Curated aliases live in `docs/NameEquivalenceRegistry.json` with notes in
`docs/NameEquivalenceRegistry.md`.

## 1. I Changed Lean Files

Use the changed-file verification lane first.

```bash
lake script run changedVerify
```

Useful variants:

```bash
lake script run changedVerify -- --dry-run
lake script run changedVerify -- --umbrella canonical
lake script run changedVerify -- --strict-check
```

What it does:
- runs `lake env lean` file gates on changed `.lean` files
- builds the corresponding owner modules with the locked build wrapper
- optionally runs a selected umbrella target

## 2. I Need A Full DAG Refresh

Use the managed DAG lane.

```bash
lake script run dagAll
```

Dry-run first if needed:

```bash
lake script run dagAll -- --dry-run
```

What it does:
1. `dagStatus`
2. `dagRefresh`
3. `dagReports`
4. `dagDoctor`

## 3. The DAG Lane Looks Stale Or Broken

Start with diagnosis, not ad hoc repair.

```bash
lake script run dagDoctor
```

If the doctor reports stale authoritative artifacts or stale reports, run:

```bash
lake script run dagAll
```

If you only need a status snapshot:

```bash
lake script run dagStatus
```

## 4. I Need Local Frontier Or Proof-State Work

Use the local theorem/proof tools instead of refreshing the whole DAG lane.

Examples:

```bash
lake script run proofSession
lake script run proofPrint -- InfoGeometry.Canonical.SomeModule
lake script run semanticSnapshot
```

Use this lane when you are debugging a proof, exploring theorem surfaces, or inspecting a small local packet.

## Default Rule

- opening step: refresh `reports/dag/equivalence-dictionary.{json,md}`
- changed Lean work: `lake script run changedVerify`
- whole-repo DAG maintenance: `lake script run dagAll`
- diagnosis first: `lake script run dagDoctor`

## Patch-Loop Rule (Fast Iteration)

Do not run full-chain builds after every small patch.

Use this order:

1. `lake env lean <changed-file>.lean`
2. If file-level check passes, continue patching related files only.
3. Run owner-module build (`lake build <Owner.Module>`) when the local patch set is coherent.
4. Run `changedVerify` before commit.
5. Run full DAG/full umbrella only at packet checkpoints or pre-promotion.

For CP-002 work, prefer:

```bash
lake env lean lean/InfoGeometry/Canonical/RelativeModularBlockDiagonalCore.lean
lake env lean lean/InfoGeometry/Canonical/RelativeModularScaleShapeSplit.lean
lake env lean lean/InfoGeometry/Canonical/SingularDecompositionSurrogate.lean
```
