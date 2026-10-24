# Peirce rotor alternation: theorem contract

## Intake and scope

Source: `Pasted text(20261024-105659).txt`, the proposed
`DeBruijnRotorAlternationCycle.lean` and companion audit. Base inspected:
`0d1b2d40e7979ce8b55508d66e35c3740a5ed8a8` (main).
This is an additive adaptation of that attachment, not publication of the
previous modular-parabolic candidate. No unmerged PR is an import dependency.

The source's four seed equations are preserved over an arbitrary associative
ring: d*d=0, b*b=0, d*b*d=d, b*d*b=b. This does not assume a star, positivity,
invertibility of 2, finite dimension, or existence of any inverse witness.
`IsDualSeedPair` packages only these inputs, not any claimed conclusions.
Its one-way MP adapter reuses `IsMoorePenroseInverse` and the already-owned
inverse-square-zero theorem. No replacement MP definition is added.

The aliases polePlus, poleMinus, carrierSupport, zeroModeSupport,
phasePolarization, transitionVelocity, and wheelGenerator refer to the existing
exact/coexact/active/harmonic/chiral support and Majorana definitions from
`Singular.SquareZeroChiralHodge` and `Core.DiracSuperalgebra`.
The native import closure, not documentation or graph proximity, supplies proof
authority. Search scope included the exact uploaded names, reflexive-pair
names, rotor owners, and the inspected support/Majorana sources. This is not a
repository-wide novelty claim or a categorical replacement.

## Preserved mathematics

Let p=d*b, q=b*d, Delta=p+q, H=1-Delta, G=p-q, Q=d+b, J=d-b.
The algebraic statements are:

- [J,p]=-Q, [J,q]=Q, [J,Delta]=0, [J,G]=-2 Q, [J,Q]=2 G.
- [J,[J,G]]=-4 G, and [J,p]=0 iff d=b=0.
- For central scalar c,s, the moving poles are
  p(c,s)=c^2 p+s^2 q-c*s Q and q(c,s)=s^2 p+c^2 q+c*s Q.
- When c^2+s^2=1, both are idempotent, both ordered cross-products vanish,
  and p(c,s)+q(c,s)=Delta.
- (p(c,s)-p)^2=s^2 Delta on the scalar circle.
- [p,p(c,s)]^2=-(c*s)^2 Delta and p*p(c,s)*p=c^2 p;
  these last two identities do not require c^2+s^2=1.

These equations retain the attachment's signs and scalar normalization.
The source's named `poincare_fubini_study_metric_master` is retained for API
traceability, but its type and documentation state only these algebraic
identities. No norm, metric, probabilistic fidelity, positivity, manifold,
Mostow theorem, or Poincare/Fubini--Study identification is constructed.

## Added connection and missing reverse-direction closure

The attachment defines a phase rotor but does not prove that the moving
idempotents come from its conjugation. The addition establishes
R(c,s)=H+c Delta+s J, R(c,s)R(e,f)=R(c*e-s*f,c*f+s*e),
and R(c,s)^{-1}=R(c,-s) on c^2+s^2=1, as a genuine native `Aˣ`.
The harmonic term supplies the ambient identity on proper active support.
Both moving poles are explicitly equal to R*p*R^{-1} and R*q*R^{-1}.
The two idempotences and both annihilation orders follow from that conjugation.

The four-coordinate `peirceBlock` evaluates in the original arbitrary algebra;
its multiplication is proved from the four input equations. It is not a scalar
surrogate or a replacement of the noncommutative carrier.

## Source repairs and interpretation boundaries

The uploaded code is not claimed to compile unchanged. The adaptation uses
explicit ring multiplication expansions, central-scalar module normalization,
and the existing owners. It supplies the moving-minus idempotence promised in
the source's introduction but not present as a theorem in its displayed code.
It also supplies reverse orthogonality rather than silently treating one
ordered zero product as both.

The source's first_derivative/second_derivative names are commutator identities.
No `HasDerivAt`, trigonometric parametrization, differential equation, or
exponential representation is certified here. The DeBruijn name is preserved
from the source; no de Bruijn graph or combinatorial cycle theorem is asserted.

Star symmetry is separate: even an MP seed pair can have b != star d. The
rational example d=2E01, b=(1/2)E10 has symmetric MP support projectors but its
moving pole at (3/5,4/5) is not symmetric. Thus the algebraic square identity
cannot be silently interpreted as a positive metric or Born probability.
A characteristic-two example has nonzero pole motion with vanishing double
commutator. No cancellation of two/four or nonzero-frequency claim is made.

## Verification protocol

Compile all four new modules and their full unchanged repository import
closure against exactly the root-pinned Mathlib and Lean versions. Reuse the
repository closure resolver. Use the shared sequential build lock, inspect
compiler processes, do not strip imports, alter dependency pins or sources,
delete caches, or permit concurrent compilation.

The checker imports all four new modules together and uses public
`Lean.collectAxioms` to audit every new-module declaration, including generated
declarations. Allowed transitive axioms are only propext, Classical.choice,
Quot.sound. Unsafe and partial declarations are rejected without exemptions.
Concrete matrix examples use ordinary kernel-checked `decide`.

Source status at submission is a proof candidate until the dedicated workflow
passes. The GitHub run and downloadable audit decide acceptance; this static
file does not upgrade itself to a verification assertion. The scoped result
is not a root-package build, full All.lean check, or all-green CI claim.

Production import:

```lean
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
```

Full-checkout verification, when root package dependencies are present:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.DeBruijnRotorAlternationCycleAudit
```
