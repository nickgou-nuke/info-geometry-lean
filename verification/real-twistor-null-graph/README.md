# Real twistor null-graph verification

This focused package compiles the canonical `lean/` sources with the exact root
Lean and Mathlib pins. It does not require the unrelated path dependencies of
the root Lake workspace. All commands use the repository's shared build lock.
It is a separate verification surface, not a replacement for the publication gate.
The default build checks the new theorem, its examples, and integration through
the existing `InfoGeometry.Twistor.RealConstructs` umbrella.

From the repository root:

```bash
python3 verification/real-twistor-null-graph/check.py exe cache get
python3 verification/real-twistor-null-graph/check.py build
python3 verification/real-twistor-null-graph/check.py env lean -DwarningAsError=true lean/InfoGeometry/Twistor/RealTwistorIncidence.lean
python3 verification/real-twistor-null-graph/check.py env lean -DwarningAsError=true lean/InfoGeometry/Twistor/RealTwistorIsotropicGraph.lean
python3 verification/real-twistor-null-graph/check.py env lean -DwarningAsError=true lean/InfoGeometry/Twistor/RealTwistorIsotropicGraphExamples.lean
python3 verification/real-twistor-null-graph/check.py env lean -DwarningAsError=true lean/InfoGeometry/Twistor/RealConstructs.lean
(
  set -e
  for source in RealTwistorIncidence RealTwistorIsotropicGraph RealTwistorIsotropicGraphExamples; do
    python3 verification/real-twistor-null-graph/check.py env lean --run tools/infra/axiom_check.lean "verification/real-twistor-null-graph/.lake/build/lib/lean/InfoGeometry/Twistor/$source.olean"
  done
)
```

The maintained `axiom_check.lean` replays each compiled module in the kernel,
checks every compiled declaration, rejects partial or unsafe declarations, and
permits only `propext`, `Classical.choice`, and `Quot.sound`. This checks generated
helper declarations as well as public theorem names.
Each module is replayed in a separate process to bound retained import state;
the checker and permitted axiom set are identical for all three modules.

See `docs/REAL_TWISTOR_NULL_GRAPH_CONTRACT.md` for source provenance, theorem
statements, prior owner search, and interpretation limits.
