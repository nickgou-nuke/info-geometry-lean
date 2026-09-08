# Prolate focal geometry, rapidity, and the sech profile

Status: proof-script candidate; no Lean compiler run has been performed in the
ChatGPT working environment. Do not describe this change as kernel-verified
until the pinned repository build and axiom audit succeed.

## Basis and reuse

Requested source: `Pasted markdown(20260908-132849).md`, especially the
`ConformalDetectorIntegral.lean` section and its three algebraic targets.
The focal sign convention is retained:

- A is at +c, with rA = c (xi - nu).
- B is at -c, with rB = c (xi + nu).
- chi = (1/2) log (rB / rA).

The repository was read at main commit
`fdce23724bcbd3cc63f78c6e0cdca7e371d99c1f`.
The existing `InfoGeometry.Nuclear.ApollonianBipolarField.fluxDensity` is reused
rather than redefined. Existing owner files and umbrella imports are unchanged.

Pinned environment read from the repository:

- Lean: `leanprover/lean4:v4.28.1`.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

No Lake manifest, toolchain, dependency, workflow, or existing proof file is
modified. GitHub code search returned no hits for `rapidity` or `sech`; direct
inspection of the Nuclear umbrella and Apollonian owner supplied the reuse
boundary. This is a bounded search, not a claim of exhaustive repo-wide absence.

## Modules

`FocalRapidity.lean` handles arbitrary positive u, v. It contains full proof
scripts for exponential null-coordinate reconstruction, the positive geometric
mean, tanh and sech ratio identities, the overlap bounds, the auxiliary Lorentz
quadratic identity, product preservation under opposite exponential scalings,
and rapidity translation under that action.

`ConformalDetectorIntegral.lean` retains the source configuration/point layout.
It adds positivity, the squared cylindrical radius, exact meridional distances
to both foci, focal sum/difference/product identities, the specified volume
factor, the flux-ratio rewrite, and the spheroidal tanh/sech specialization.
The `approachingFocus_weight` theorem gives an explicit boundary family whose
residual weight is 1/eps.

`FocalSechODE.lean` differentiates the reciprocal of native `Real.cosh` and
states the actual profile equation with `deriv (deriv ...)`:

    f'' = f - 2 f^3,     (f')^2 = f^2 - f^4.

`ConformalDetectorIntegralAudit.lean` is the narrow integration entrypoint and
prints the dependencies of the main theorem constants with `#print axioms`.

## Exact targets

For positive focal distances:

    exp(2 chi) = rB / rA
    tanh chi = (rB - rA) / (rA + rB)
    sech chi = 2 sqrt(rA rB) / (rA + rB)
    0 < sech chi <= 1.

For the open prolate domain xi > 1 and |nu| < 1:

    rA rB = c^2 (xi^2 - nu^2)
    J / rA^2 = c (xi + nu) / (xi - nu)
    J / (4 pi rA^2) = c / (4 pi) exp(2 chi)
    tanh chi = nu / xi
    sech chi = sqrt(xi^2 - nu^2) / xi.

The auxiliary Lorentz carrier is T = (u+v)/2, X = (v-u)/2, for which
T^2 - X^2 = uv. This is an algebraic identification, not a proof that a
Euclidean coordinate change changes the metric signature.

## Boundaries relative to the supplied exposition

1. The volume formula J = c^3 (xi^2 - nu^2) is specified as a definition here.
   Its identification with an absolute Cartesian Jacobian and a global
   change-of-variables theorem are not supplied by this module.
2. Cancellation is partial. For xi = 1+eps, nu = 1-eps, 0 < eps < 1, the
   remaining factor is exactly 1/eps. It is not globally bounded on the
   entire open prolate domain. A detector region bounded away from a focus
   requires an explicit domain/separation hypothesis.
3. No refractive index is inferred from a Euclidean coordinate scale factor.
   In particular, neither straight coordinate curves nor a physical optical
   medium are obtained merely by writing a conformal meridional metric.
4. No full-energy-peak transport model, finite-detector efficiency integral,
   empirical calibration claim, or exact shifted inverse-power VPD reduction
   is asserted. Those require separate geometry, kernel, and error theorems.
5. The sech ODE is an exact scalar stationary profile equation. A propagating
   soliton of a specified PDE, its stability, and its applicability to a
   detector do not follow from the focal algebra or this ODE alone.

## Validation

The supplied Lean sources contain no `sorry`, `admit`, custom `axiom`
declarations, or `unsafe` declarations. This is a lexical source check, not
a kernel certificate. Symbolic algebra checks are likewise not Lean checks.

In the canonical working tree, after observing its single-build discipline:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Nuclear.ConformalDetectorIntegralAudit
```

After this finishes, an optional separate direct audit is:

```bash
lake env lean lean/InfoGeometry/Nuclear/ConformalDetectorIntegralAudit.lean
```

Do not run these commands concurrently, change the pinned dependencies, or
clean the existing build cache. Inspect the audit output for `sorryAx` and
unexpected project axioms before promoting the candidate.
