# Real direct-limit verification

This bounded verifier checks the eight owners listed in `check.py`, using the
existing `verification/zeta-weil-krein` package. It does not add dependencies or
change the root toolchain. It also builds the existing real Fock completion and
finite arithmetic audit as downstream regression targets.

```bash
python3 verification/real-colimit/check.py --source-only
python3 verification/real-colimit/check.py
```

The first command checks source inventory, forbidden proof constructs, exact
dependency pins, the strict source screens, static GATE_4 review, and the
semantic-vacuity screen. It records `source_checks_passed_kernel_pending`, never
kernel success.

The second command additionally requests a serialized compiler batch. Its
default nonblocking readiness probe reports an occupied shared lock with exit
2 and status `source_checks_passed_kernel_blocked`. The probe does not launch a
compiler. The maintained `zeta-weil-krein/check.py` wrapper acquires the actual
execution lock for the entire batch. To wait for an occupied lane explicitly:

```bash
python3 verification/real-colimit/check.py --wait-for-build-lock
```

The kernel batch builds every selected owner and both regression targets with
`lake --wfail`, recompiles each selected source with warnings treated as errors,
and runs a generated `#print axioms` file. The existing bounded inventory and
axiom-log parser reject missing, repeated, unexpected, and disallowed axiom
reports. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. Private
helpers and generated declarations are not separately enumerated; their axiom
dependencies are included transitively through the audited public declarations.

Logs, the generated command plan, source hashes, and `verification.json` go to
`artifacts/verification/real-colimit/` by default. Use `--output-dir` for a separate
run. A `passed` status requires the exact compiler command plan to finish, the
fresh axiom output to pass, and the selected sources to retain their hashes.
The generated worker is run only under the maintained lock wrapper.

Neither source checks nor this focused package certify the whole repository.
The root publication gate is a separate check. The workflow
`.github/workflows/real-colimit.yml` runs this same verifier on the exact PR head;
its presence does not establish that CI has passed.
