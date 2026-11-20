# Centered Mangoldt bridge

This package verifies the canonical `lean/` owners at the root's exact Lean
and Mathlib pins. It integrates PR #421's finite smoothing and PR #422's RH
half-plane endpoint, then adds real-cutoff smoothing, explicit centered
interpolation, integer/real growth equivalences, and genuine Mellin integral
identities on `1 < s.re`.

## Mathematical scope

For the actual von Mangoldt function and Euler constant, set

\[
S(x)=\sum_{1\le n\le\lfloor x\rfloor}\Lambda(n)(x/n-1),\qquad
G(x)=S(x)-x\log x+(1+\gamma)x.
\]

The interpolation error for `G(N+t)` is nonnegative and at most
`t(1-t)/(2N)`, hence `1/(8N)`, for `N >= 1` and `0 <= t <= 1`.
For a fixed sign `eta = 1` or `eta = -1`, `alpha >= 0`, `C >= 0`, and an
integer threshold `N₀ >= 1`, a bound `eta*G(N) <= C*N^alpha` for every
`N >= N₀` transfers to every real `x >= N₀`, with constant
`2^alpha*C + 1/8`. The integer and real square-root-plus-epsilon
families are consequently equivalent, with the sign outside the epsilon
quantifier.

The Mellin results include `IntegrableOn` proofs and evaluate the actual
complex Bochner integrals on `(1, infinity)`:

\[
\int_1^\infty S(x)x^{-s-1}\,dx
=\frac{-\zeta'(s)/\zeta(s)}{s(s-1)},\qquad \Re(s)>1,
\]

\[
\int_1^\infty G(x)x^{-s-1}\,dx
=\frac{-\zeta'(s)/\zeta(s)}{s(s-1)}
-\frac1{(s-1)^2}+\frac{1+\gamma}{s-1}.
\]

The square-root cancellation assertion itself and the one-sided Landau
continuation theorem remain open. One-sided control is not absolute control
of `G`; these Mellin identities do not assert convergence throughout the
larger half-plane needed for RH. PR #422's native RH equivalence remains
conditional on its explicitly stated half-plane nonvanishing premise.
No external announced proof is imported or certified.

## Reproduce

From the repository root, with the pinned toolchain on `PATH`:

```bash
python3 verification/centered-mangoldt/audit.py
python3 verification/centered-mangoldt/check.py --wfail build
python3 verification/centered-mangoldt/check.py env lean -DwarningAsError=true lean/InfoGeometry/Arithmetic/CenteredMangoldtBridgeAudit.lean > /tmp/centered-mangoldt-axioms.log
python3 verification/centered-mangoldt/audit.py --log /tmp/centered-mangoldt-axioms.log
```

For a fresh checkout, first retrieve the pinned Mathlib artifacts:

```bash
python3 verification/centered-mangoldt/check.py exe cache get
```

The wrapper uses the shared repository build lock and validates both
workspace roots. The manifest retains all nine root Mathlib-related Git
pins. The inventory covers the five new owners and both prerequisite owners;
private helpers' dependencies are included transitively in their public
heads' axiom reports. The only permitted foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

See the [theorem contract](../../docs/CENTERED_MANGOLDT_BRIDGE_CONTRACT.md)
for exact obligations and the [validation record](validation.json) for
observed commands, source hashes, independent review, and root integration
status. Focused verification does not certify the full `InfoGeometry.All`
build. The dedicated GitHub workflow recreates the focused build and axiom
evidence for each checked revision.
