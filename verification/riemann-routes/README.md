# Native arithmetic and real operator routes

This package compiles the actual canonical sources with the root repository's
unchanged Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins. It does not provide replacement
mathematical definitions or import the external claimed RH proof.

The selected owners cover real Mangoldt interpolation and transfer of assumed
signed bounds, finite smoothing Mellin integrals, the complete conditional
Mertens-to-native-RH implication, and real domain residual estimates including
the existing unbounded maximal-domain operator. Prerequisites from #421 and
#422 and the reused zeta/Möbius owner are included in the public-head inventory.

From the repository root:

```bash
python3 verification/riemann-routes/audit.py
python3 verification/riemann-routes/check.py build
python3 verification/riemann-routes/check.py env lean -DwarningAsError=true lean/InfoGeometry/Arithmetic/RiemannRoutesAudit.lean > riemann-routes-axioms.log
python3 verification/riemann-routes/audit.py --log riemann-routes-axioms.log
```

Every compiler or cache command goes through the maintained shared build lock.
The source inventory and axiom parser are reused from
`verification/real-matrix-split/audit.py`. Audit generation uses `--write`; it
lists every explicit public head in the selected owners exactly once.

The focused build preserves and reports warnings in reused unchanged sources.
Fresh checks of the selected owners and the audit use `warningAsError=true`.
In particular, the older `MobiusMertensRHEquivalence` dependency currently emits
two tactic-style warnings and two tactic suggestions; these are not new proof
failures and are not suppressed by this package.

Read the [theorem contract](../../docs/CENTERED_MANGOLDT_ROUTE_CONTRACT.md) and
[source route audit](../../docs/RIEMANN_ALTERNATIVE_ROUTES_AUDIT.md) for the exact
hypotheses, dependencies, and remaining work. The independent validation record
records compilation, foundational-axiom checks, source gates, and their actual
scope. The missing root path dependency is reported separately from the focused
build. No unconditional RH or root integration certificate is claimed.
