# Coordinate metric radical and positive restriction

Owner: `QuantumContext/MetriplecticChiralCl11.lean`. The carrier is its existing
four-entry `Cl11Matrix R` record; the form is
`(A12-A21)*(B12-B21) - (A11*B22+A22*B11)`.

The existing owner proves indefiniteness over the reals and sufficient nullity
conditions. The new extension characterizes its radical over every commutative
ring as `A11=A22=0` and `A12=A21`. On trace-zero real inputs its quadratic form
is `(A12-A21)^2+2*A11^2`, hence nonnegative, and self-nullity is equivalent to
membership in the full radical. No characteristic assumption is needed for
the radical classification; order and self-nullity results use real scalars.

Search of maintained Lean uses of `metricBracket` and the owner import found
the owner audit and `All`; the similarly named derivative-frame form in
`Thermo/BipolarObservableMetriplecticAlgebra` has a different carrier and formula.
The extension reuses the original definitions and does not replace either form.

This does not make the full form nonnegative, make the restricted form positive
definite, supply a Clifford representation, or construct metriplectic dynamics.
Parent locked audit build (session 74055) completed with exit 0, 865 jobs:
`/tmp/metriplectic-radical-audit.log`. Independent QA repeated the build
(session 32625), exit 0, 865 jobs: `/tmp/metriplectic-radical-qa.log`.
Five new theorems, six axiom reports (including the existing negative result),
and three examples passed. The axiom union is exactly `propext`,
`Classical.choice`, `Quot.sound`; source warnings: zero, package notices: two.
Strict OpenGauss screening found zero traps; scoped staged diff checks passed.
Independent mathematical contract and final source reviews both passed.
