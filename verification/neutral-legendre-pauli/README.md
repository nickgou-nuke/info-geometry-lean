# Neutral, Legendre, Pauli-incidence, and corner verification

Run from an independent checkout with the pinned toolchain and package sources:

```bash
python3 verification/neutral-legendre-pauli/check.py \
  --repo "$PWD" --output /absolute/new/report-directory
```

The output directory must not already exist and must be outside `lean/` and
`src/`. The runtime must be on `PATH`. The entrypoint reuses the existing
focused `verification/real-matrix-split` package and shared-lock wrapper, and
the common verification implementation in `real-dirac-spin-nambu/check.py`.
The latter's original command and Dirac-packet defaults are unchanged.

## Exact coverage

The runner builds and freshly elaborates all six selected owners with
`-DwarningAsError=true`:

- `Canonical.OrientedPfaffianMatching`: explicit-import repair and a constructive
  doubled-index matching with two simp readouts; existing proofs unchanged.
- `Canonical.MajoranaPfaffian4`: explicit-import repair, unchanged proofs.
- `Geometry.DualFlatKreinLegendreSubmodules`: six submodule equalities.
- `OperatorAlgebra.OperatorDirichlet.MatrixLegendreFenchel`: six quadratic bridges.
- `Twistor.RealPauliIncidence`: four real incidence bridges.
- `OperatorAlgebra.PeirceSpine.JordanCorner`: four corner/associator bridges.

It scans every selected source for forbidden proof constructs, inventories all
explicit public declaration heads, generates a fresh `#print axioms` probe,
and checks each expected record. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Private helpers are covered transitively. Generated
structure fields/recursors are not separately enumerated. The expected inventory
is 44 public heads and eleven separately reused declarations, giving 55 axiom
records in a completed run.

The runner records source/control hashes before and after execution, checks
root/focused dependency pins, verifies the runtime version, and fails if
selected sources or controls change during the run. It does not install
dependencies, update pins, invoke another package's default targets, or read
old acceptance reports. Exit codes are `0` passed, `1` failed, `2` blocked,
and `130` interrupted.

This is a focused package check. It is separate from the root integration
build, static/source gates, and independent mathematical review. A report
with `compilation: not_run` or without actual axiom records is not theorem
verification. The claim ledger is in
`handover/injections/neutral-legendre-pauli-20261124.md`.
