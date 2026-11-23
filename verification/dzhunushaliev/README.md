# Dzhunushaliev / Myung verification

Run from the repository root with the pinned Lean toolchain on `PATH`:

```bash
python3 verification/dzhunushaliev/check.py
```

The script reuses `verification/real-matrix-split/check.py` and its existing
locked Lake package. It compares the package's Lean and dependency pins to the
root manifest, builds the selected owners and their existing real derivation
consumer, freshly elaborates each changed
owner with warnings treated as errors, inventories explicitly named public
declarations, and checks their reported axiom dependencies. It also checks
that the source hashes remain unchanged during verification. Strict OpenGauss
screening/refutation, static Gate 4, and the semantic-vacuity scan run on the
same selected source. Static Gate 4 does not itself run Lean; the preceding
build and axiom commands supply the separate compiler evidence.

The eight compiler commands run serially beneath one invocation of the
maintained locking wrapper. A generated private worker preserves individual
logs and exact command/exit records, inherits the wrapper's process group,
and stops on the first error. It does not acquire a nested lock or detach
compiler processes. The parent requires the complete expected successful
command record before accepting the batch.

Raw logs and a machine-readable report are written to
`artifacts/verification/dzhunushaliev/` by default. Pass `--output-dir` to
record an independent second run. Generated files are not included in the
source commit by default.

Only `propext`, `Classical.choice`, and `Quot.sound` are permitted in the axiom
footprint. The source scan rejects proof holes, custom axioms, `native_decide`,
unsafe proof mechanisms, and `implemented_by` in the selected owners. It uses
the existing bounded declaration inventory, not a whole-environment parser.

## Mathematical scope

- All universal identities and Myung necessity use `NonUnitalNonAssocRing`.
- Myung's converse explicitly assumes cancellation of additive two-torsion.
- The printed Table I is transcribed and extended bilinearly to `Fin 8 → ℤ`.
  Its failure is established both in the linearized identity and in the
  repeated-argument right-alternative law.
- The corrected basis reuses the canonical `ZornMatrix` product and Peirce
  basis. Polynomial identities and nonzero real witnesses are distinguished.
- The whole quaternion slice is closed and associative. The characteristic-two
  Zorn algebra gives a counterexample to the unrestricted Myung converse.
- Associative-target impossibility means an injective multiplication-preserving
  map; no claim excludes faithful linear left-regular maps.

The full contract and primary-source corrections are in
[`handover/injections/dzhunushaliev-myung-zorn-20261123.md`](../../handover/injections/dzhunushaliev-myung-zorn-20261123.md).

The semantic scan reports coordinate readbacks, the definitionally exact
left-regular defect identity, and the retained self-commutator identity as
`trivial_surface` warnings. These are reviewed statements with their actual
scope, not suppressed scanner results or additional structural theorems.

This focused check does not certify the root Lake workspace, every historical
owner, physical unobservability, or an identification of the entire
`(V, Γ, J, D)` framework with the paper.
