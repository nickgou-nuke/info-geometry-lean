# Angular-model positivity criteria

The owner `Physics/CobaltAsymmetry.lean` already proves a nonnegative
anisotropic reflection-invariant example. `CobaltAsymmetryTests.lean` also
exhibits a negative value of `gammaAngularModel 1 2` at the equator.

`CobaltPositivityCriteria.lean` uses those same real-function definitions,
without a replacement carrier, to classify their global positivity:

- `beta_nonneg_everywhere_iff`: nonnegative at every angle iff `|a| ≤ 1`.
- `gamma_nonneg_everywhere_iff`: nonnegative at every angle iff `k ≤ a^2`.

The latter removes the unnecessary lower bound on anisotropy from the
existing sufficient-condition theorem. Necessity is tested at the equator;
negative anisotropy is handled by the nonnegativity of a square. The beta
necessity uses the two axial angles. These are parameter-domain completions,
not a claim that the existing sufficient conditions are false.

Searches of maintained Lean source for both model definitions found the
owner and tests; no equivalent iff was found in those search results.

The audit contains four boundary/counterexample specializations and three
axiom requests, including the existing anisotropy counterexample. Independent
semantic review passed; its requested license headers have been added.
Strict source screening passed before that header-only change.

Parent kernel verification passed: the locked build of
`InfoGeometry.Physics.CobaltPositivityCriteriaAudit` completed with exit code 0
(1960 jobs), recorded in `/tmp/cobalt-positivity-audit.log`; session 26439 was
observed terminal. All three axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. There were no source warnings, only two
existing package-local-change warnings. Final static AA passed after the
exact mandated headers were installed. Independent kernel QA passed in
session 38772: the combined Cobalt/projection audit completed with exit 0
(3195 jobs), `/tmp/cobalt-projection-final-qa.log`. All seven combined examples
and nine axiom reports passed, with zero own-source warnings, fourteen
dependency warnings, and two package notices. Four-source strict screening
and scoped diff checks passed. Acceptance is limited to the stated criteria.
No physical symmetry inference or experimental identification is asserted.
