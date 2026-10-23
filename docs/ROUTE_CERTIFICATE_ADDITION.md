# Addition to PR #194: proof-carrying route certificates

Base: `b8f4038cccd18dc3eb1cf8023cdbfe4dddc178f7` on
`feat/functional-route-fiber-diagnostics`. Existing owners, runtime modules,
and dependency pins are unchanged.

## Ground-truth theorem contract

The source graph notes specify recurrent cycles, a synchronized retraction,
and the recurrence depth(f(i))+1=depth(i) away from the core. PR #194's
`FunctionalRouteCore.drazin_of_synchronized_retraction` already proves the
Drazin equations from that retraction plus an eventual-entry assumption.

This addition replaces the eventual-entry assumption with local natural-number
rank checks. The native carrier is still `Fin n -> Fin n`, with an explicit
embedding `Fin c -> Fin n` and native `Equiv.Perm (Fin c)`. `LocalCertificate`
contains only graph equations: retraction, cycle action, synchronization,
zero depth on the embedded core, membership of every zero-depth token in
that core, and exact positive-depth descent. No Drazin law, matrix inverse,
operator shell, or desired eventual-entry conclusion is a certificate field.

The eight theorems establish: one-step depth descent; the depth after any
iterate; exact entry iff depth <= time; a canonical Drazin witness for any
certified bound; injectivity of the native route matrix representation; the
Drazin power equation iff all entry depths are bounded by the exponent; the
same necessary bound for any Drazin witness using inverse uniqueness; and
minimality whenever the supplied bound is attained.

The theorem is general for all local certificates, including empty finite
types when its hypotheses permit them. The executable interface deliberately
requires a nonempty route and an attained maximum depth.

## Independent check and Lean export

`tools/route_certificate.py` verifies integer arrays without rerunning Kahn
peeling. It validates the permutation and inverse, the recurrent embedding,
the retraction, all local depth equations, and the exact maximum. A JSON
certificate has exactly `route`, `recurrent`, `cycle`, `inverse_cycle`, `rho`,
`depth`, and `bound`. Here `rho` uses recurrent coordinate indices, not
ambient token indices. The existing analyzer retains its original convention;
conversion is explicit in `certificate_from_geometry`.

The exporter writes native Lean data and proofs of the finite local equations
using `decide`. Real matrix Drazin equations are obtained by applying the
proved certificate theorem, not by evaluation of real matrices. Each exported
file audits its local certificate, Drazin witness and minimum-exponent theorem.

```bash
python3 -m tools.route_certificate --route 0,0,1,1 \
  --namespace Example.Branch --lean-out /tmp/branch_certificate.lean \
  > /tmp/branch_certificate.json
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Routing.FunctionalRouteCertificate
# After the locked build has finished, under the same sequential discipline:
lake env lean /tmp/branch_certificate.lean
```

An emitted file is only a proof candidate until Lean accepts it. The Python
checker is not proof authority. Forged local data must fail in Lean even if
it bypasses the Python validator.

## Verification and scope

The dedicated workflow runs 19 tests sequentially: the 11 existing exact and
PyTorch tests, plus 8 certificate tests. It then compiles the complete source
import closure against the unchanged pinned Mathlib revision, audits all eight
new theorems, kernel-checks eight generated route certificates (24 theorem
audits), and requires rejection of a deliberately corrupted depth table.

The exact runtime suite and certificate suite each include all 288 functions
on one through four vertices. Only the eight explicitly listed generated
fixtures are kernel-checked by this workflow. Do not confuse the finite test
coverage with universal verified execution of Python.

The artifact records the exact checked commit, toolchain, source hashes,
compiler output, generated files, axiom footprints, rejected-certificate log,
and runtime tests. Its success status is written only after all gates pass.

This does not prove total correctness or universal certificate construction
for Kahn's algorithm. It does not formalize the graph-specific pseudoinverse
fiber formula, peeling-height/shell-rank formula, or the whole Python runtime.
Those remain separately documented proof obligations. `shell_ranks`,
`peel_height` and `cycle_count` are deliberately outside this certificate.
No Autograd change, training-loop integration, speedup, or full-repository
build is implied. The existing residual-preserving diagnostics are unchanged.
