# Proof-carrying quadratic optimization

The formalization is in `lean/InfoGeometry/Epistemology/CurryHowardReality.lean`.
It proves statements about the specified real quadratic model, not an identity
between physical reality and a type checker.

For a positive coupling, the completed-square identity proves the global bound
and the unique maximizing efficiency:

\[
R(e)=e(1-ke)=\frac1{4k}-k\left(e-\frac1{2k}\right)^2,
\qquad k>0.
\]

`CertifiedOptimum` is a subtype containing an efficiency and its proved global
optimality proposition. `certifiedOptimum` constructs that value, and the
uniqueness theorem gives a native `Subsingleton` instance. This is an actual
proof-carrying construction rather than a physical interpretation of types.

The normalization map deliberately discards its input. Its idempotence and
equal-output theorem reduce definitionally, but its optimality is proved by the
completed-square argument. A counterexample proves that equal normalized
outputs do not imply equal input efficiencies.

An additional, genuinely input-dependent relaxation is defined by

\[
e_{next}=e_*+(1-a)(e-e_*).
\]

Its response gap is multiplied exactly by \((1-a)^2\), and the response cannot
decrease when \(0\le a\le2\). A regression example with \(a=3\) shows why a
step restriction is necessary. This is a discrete algebraic model; no physical
relaxation equation or convergence theorem is assumed to follow from beta
reduction.

`CurryHowardRealityDependency.lean` gives a native finite partial order with
separate normalization-equality and relaxation-contraction branches.
`CurryHowardRealityTests.lean` contains concrete examples, a non-maximizer,
distinct inputs with equal outputs, and axiom audits.

No Curzon--Ahlborn identification, detector model validation, gauge homotopy,
HoTT path construction, supersymmetry claim, or physical definitional equality
is asserted by these theorem statements.

## Pinned validation procedure

Validation uses the configured Lean 4.28.1 executable. Dependency sources are
checked against `lake-manifest.json`; incompatible 4.28.0 compiled artifacts
are not loaded or patched. The required closure is rebuilt sequentially under
the shared `/tmp/info-geometry-build.lock`, with fresh outputs in
`/tmp/isnp-rebuilt-4.28.1`. No dependency source, toolchain pin, or manifest is
changed by this check.

Result: the complete 883-module source closure, including the model, dependency
poset, and regression module, passes Lean 4.28.1 (commit
`978f81d363eabdc49c5720726faa53a6007fcee8`). All nine printed axiom audits list
only `propext`, `Classical.choice`, and/or `Quot.sound`, with no `sorryAx`.
The three repository modules produce no warnings. This is a targeted result,
not a claim that the entire repository builds.

ProofWidgets' JavaScript assets were built from its pinned checkout using the
unchanged npm lockfile; no old Lean binaries or fabricated assets were used.

Recheck with the populated source-closure cache from the repository root:

```bash
cd lean
LEAN_PATH=/tmp/isnp-rebuilt-4.28.1 \
  elan run leanprover/lean4:v4.28.1 lean \
  InfoGeometry/Epistemology/CurryHowardRealityTests.lean
```
