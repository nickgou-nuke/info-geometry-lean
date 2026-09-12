# Weak-value reconstruction boundary

This change implements a finite, native Mathlib theorem layer for the proposed
weak-value mechanism. It reuses the repository's `DoubledSpace`, `to_doubled`,
`modular_j`, `KreinSpace.kreinInner`, `IsKreinIsometry`, and `KreinHom` owners.
It does not replace the categorical infrastructure or assert a new continuum
completion. No toolchain or dependency manifest is changed.

## Source owners and scope

- `Krein/TransitionWeakValue.lean`: real transition readouts on the existing
  doubled carrier, explicit null/overlap distinctions, Hadamard repacking, and
  invariance under the existing pairing-preserving intertwiner.
- `Canonical/WeakValuePoleBounds.lean`: complex scalar quotient estimates,
  phase-sensitive real-readout criterion, an overlap logarithmic barrier,
  derivative identities, and a finite weighted-gradient lower bound.
- `Krein/TransitionWeakValueExamples.lean`: a constructive normalized state
  family with arbitrarily large readouts and a cancellation control example.
- `Krein/TransitionWeakValueAudit.lean`: narrow import and axiom-print target.

The inspected existing `Canonical/PolarizedMadelungBridge.lean` owns Hilbert
normalization and unnormalized Krein expectation, not this transition quotient.
`Canonical/NavierStokesBridge.lean` explicitly describes a linearized operator
model rather than a Navier--Stokes PDE formalization. Those owners are unchanged.
The broader repository search index returned incomplete/empty results; this
change makes no claim to have exhaustively audited every repository theorem.

## 1. Three distinct zero conditions

For real base states x,y, set v = to_doubled x y. Then

    overlap(v) = <y,x>
    kreinInner(v,v) = ||x||^2 - ||y||^2.

The diagonal state (x,x), x != 0, is Krein-null but has strictly positive
transition overlap. Conversely, orthogonal states of unequal norm have zero
transition overlap without being Krein-null. A nonzero isotropic vector must
also not be confused with a vector in the kernel of a specified operator.

There is a constructive bridge, but it requires an explicit map:

    kreinInner((x+y,x-y),(x+y,x-y)) = 4 <y,x>.

Thus real overlap zero is equivalent to nullity AFTER Hadamard repacking. For
complex overlaps this one real quadratic condition controls only the real part;
complex overlap zero requires both real and imaginary parts to vanish.

If the two states are embedded separately as (x,0) and (0,y), the diagonal
Krein pairing between these embedded sheets vanishes identically. The useful
transition pairing therefore uses the base components or an explicitly chosen
inter-sheet map, not the diagonal cross-sheet pairing by default.

## 2. Conditions for amplification

For n,d in C with d != 0,

    ||n/d|| = ||n|| / ||d||,
    R ||d|| < ||n||  ==>  R < ||n/d||.

This supplies a finite quantitative pole threshold. It does not assert that a
zero denominator by itself forces divergence. For example n=d gives readout 1.
Moreover,

    Re(n/d) = (Re(n) Re(d) + Im(n) Im(d)) / normSq(d).

The sign and size of this phase-sensitive numerator matter. For real d,
Re(i/d)=0 even though the complex modulus can grow without bound.

Mathlib's field inverse is totalized at zero, so n/0=0 in Lean. A physical weak
readout must be interpreted on the admissible chart d != 0; the totalized value
is not a physical prescription for continuation through a pole.

## 3. Constructive normalized pole family

In the existing real doubled carrier, define

    X(t) = 2t/(1+t^2),  Y(t) = (1-t^2)/(1+t^2),
    pre = (1,0),  post(t) = (X(t),Y(t)),
    state(t) = (pre,post(t)).

The implemented identities are

    ||pre||^2 = ||post(t)||^2 = 1,
    state(t) != 0,
    kreinInner(state(t),state(t)) = 0   for EVERY t,
    overlap(state(t)) = X(t),
    numerator(modular_j,state(t)) = Y(t).

At t=0 the overlap is zero and the numerator is one. On t != 0,

    readout(modular_j,state(t)) = (1-t^2)/(2t).

`arbitrarily_large_readout` constructs a positive t <= 1 for every requested
real threshold R, keeping the overlap nonzero and the readout greater than R.
The same states have identity-observable readout exactly 1.

This is an explicit finite-dimensional reconstruction pole, not a claimed
Navier--Stokes solution or a theorem about a spatial gradient. The source does
not construct an evolution generator, scattering law, or a continuation through
the inadmissible readout chart.

## 4. Transport and the colimit boundary

A Krein isometry preserves kreinInner(v,v), so a nonnull global state cannot
become null under a globally Krein-isometric evolution. This does not exclude
zeros of a LOCAL density when only an integrated pairing is preserved.

For the existing owner morphism f : KreinHom H F and an observable intertwining
relation B(f x)=f(A x), the implementation establishes

    kreinReadout(B,f phi,f psi) = kreinReadout(A,phi,psi)

and preservation of denominator nonvanishing. This is the finite-stage
compatibility law for the existing categorical tower/colimit owners. It is
not a second colimit construction and does not assert analytic continuation.

## 5. Barrier and gradient statements

Define the scalar overlap barrier B(d)=-log(normSq(d)). On d != 0,

    b < B(d)  <=>  normSq(d) < exp(-b).

This barrier is NOT enstrophy and is not identified with the existing matrix
log-det barrier or a self-concordant spatial regularity functional.

For differentiable real profiles, the exact quotient derivative is

    (n/d)' = (n' d - n d') / d^2.

The upper bound implemented in the source cannot be reversed into a blowup
lower bound. A divergent upper estimate does not prove divergence. Proportional
numerator/denominator profiles give exact cancellation of the derivative
numerator. The separate finite weighted-gradient lower bound explicitly requires
both nonnegative spatial weights and pointwise gradient lower bounds.

A continuum enstrophy or BKM claim still needs spatial noncancellation,
localization/measure control, actual PDE reconstruction, and the relevant
continuation theorem. None is silently assumed here.

## 6. Claims deliberately not asserted

This PR does not prove that every classical fluid velocity is a specified weak
momentum value, that all Navier--Stokes singularities are overlap zeros, that
Andreev reflection is forced at a zero, or that a Zorn mass gap supplies a global
self-healing evolution. These require explicit dynamics and reconstruction
intertwiners. The existing split-octonion and KKT owners are left unchanged.

## Verification

The authoring environment has no Lean/Lake executable and cannot download one.
The proof scripts therefore require an actual pinned-toolchain compiler verdict;
no kernel verification is claimed by this document. The focused PR workflow
attempts this without changing `lean-toolchain`, `lakefile.lean`, or
`lake-manifest.json`. Consult its job log and PR status for the actual result.

Sequential checks in a provisioned repository:

```sh
ps -eo comm,args | grep -E '(^|[ /])(lean|lake)([ ]|$)' || true
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Krein.TransitionWeakValueAudit
lake env lean lean/InfoGeometry/Krein/TransitionWeakValueAudit.lean
```

Inspect the printed axiom dependencies. No `sorryAx` or additional physical
axioms are permitted. Never run `lake clean`, delete the build cache, or launch
concurrent compiler processes. The PR remains a draft until verification is
recorded.
