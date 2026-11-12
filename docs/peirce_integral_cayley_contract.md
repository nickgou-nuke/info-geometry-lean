# Integral Peirce order, star geometry, and spectral gap contract

## Intake and source revision

The exact user attachment is preserved as
[`sources/peirce_integral_cayley_intake_20261112.txt`](sources/peirce_integral_cayley_intake_20261112.txt).
It has 23,809 bytes and SHA-256
`818424eb2eddaaed7aef7e66b698718f5c294390e1eb015c1b37d4b8077b6a52`.
The attachment itself ends midway through D3; no continuation is inferred.
Its narrative and proposed proofs are intake, not proof authority.

Work starts from PR #329, commit
`ca1de76570bb927a5dddd7c8ee3d91340e06b8a8`, over main
`a392af178af1fe2bcba2ba39eb405700c6ee103c`.
Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned.

## Exact mathematical contract

Use the existing arbitrary associative ring `B` and Peirce definitions
`N+ = P*A*(1-P)`, `N- = (1-P)*C*P`, `Phi=N++N-`, `J=N+-N-`,
`V=N+*N-+N-*N+`, `Sig=N+*N--N-*N+`, with `P*P=P`.
All algebraic operator statements retain this noncommutative carrier.

| Atom | Correct scope and planned owner | Intake correction |
|---|---|---|
| Integral scale-four sandwich | `IntegralReynolds`: composition on the centralizer of `V`; evaluations on the cut and corners | Relative centrality is not ambient centrality; unrestricted scaled idempotence is false. |
| Ambient counterexample | `Canonical.PeirceIntegralReynoldsCounterexample`: the existing full real 4-by-4 dense frame gives `VX=X`, `XV=0`, `KX=X`, and failure of the unrestricted scale-four law | The centralizer condition has a concrete noncommutative obstruction. |
| Free rank-four order | `IntegralOrder`: native subalgebra of `Mat(2,R[X])` with lower-left entry divisible by `X`, native coordinate equivalence and basis | Four spanning generators in an arbitrary realization do not prove freeness. This concrete order is not, without an additional theorem, a universally presented quotient. |
| Splitting and generator determinant | Same concrete order; unit-parameter full matrix algebra and change-of-generators determinant where proved | `-4V` belongs to the generator coordinate matrix. It is not the discriminant of the entire order and does not establish failure of Azumaya at 2. |
| Exact integral image | `IntegralOrderReynolds`: native cut/corner identification, `V=v I`, `K(M)=2v^2 tr(M) I`, and image exactly `2v^2 R I` in the concrete order | For `v=X` over a nontrivial coefficient ring, the identity is excluded. The unnormalized operator does not surject onto all scalar matrices. |
| Unipotent daughter | `StarDaughterGeometry`: `conjPlus P A P=P-N+`, exact star and Gram defects | `(1-N+)P(1+N+)=P+N+`; the intake reverses the sign. No bundle gluing is constructed. |
| Commutator detection | Same owner: selected corner detects `[P,A]` when `star A=A` or `star A=-A`; compose with existing proper-star zero criterion | General amplitudes have a lower-corner blind spot. Nonzero Gram does not imply injectivity. |
| Rational unitary daughter | `UnitaryCayley`: construct the inverse and unitary from invertibility of `1+V`, reuse `VerifiedUnitaryResolvent`, prove the exact projector formula | The invertibility condition is explicit; no inverse is available in a general ring merely from notation. |
| Positive spectral gap | `PositiveSpectralGap`: native C-star continuous functional calculus proves `0 <= V^2-c • V` iff every real spectral value is zero or at least `c`, assuming `V>=0` | Nonvanishing is not injectivity or a uniform lower bound. This is a conditional spectrum criterion, not a Yang--Mills mass-gap theorem. |

## Reused owners and dependency order

`Basic`, `Tetraktys`, `Unipotent`, and `StarGrading` own the Peirce products,
square-zero relations, daughter convention, and adjoint identities.
`HomogenizedFourierDefect` already proves the four channel defects and the
faulty weighted values `5*V^3` and `V^2*Phi`.
`StarMetricNondegeneracy` already proves nonnegative Gram coupling and the
proper-star zero criterion. `PeirceChannelCounterexamples` already supplies
the lower-corner blind spot and a nonzero singular Gram matrix with an
explicit annihilator. These results are reused rather than claimed as new.
`IndividuatedCayley.VerifiedUnitaryResolvent` owns generic starred-ring Cayley
unitarity; the new work must construct its inverse fields from `1+V`.
At the endpoint `V=1`, the arbitrary-ring Cayley conclusion still requires
invertibility of `1+V`, which is invertibility of `2` there. This is a
different issue from the integral order's full-matrix criterion, which
requires invertibility of `v` alone.

Automatic invertibility in a C-star algebra already has an owner:
`ChiralSchwarzResolvent.plus_denominator_strictlyPositive hPs X` proves
strict positivity of `1+genV P X (star X)`; its `.isUnit` consequence supplies
the native `IsUnit.nonempty_invertible` instance for the algebraic Cayley
theorems. No duplicate positivity or denominator theorem is added here.

Two other intake claims need separate wording corrections. Orthogonal
polynomial evaluation generally subtracts the constant term, as already
owned by PR #328; the shortened formula requires that term to vanish.
The intake never defines `omega_J`. If it denotes the existing
`weylJ = J + (1-V)` from `Unipotent.lean`, it belongs to the `(1,Phi,J,Sig)` frame span
with coordinates `(1-V,0,1,0)`. The intake's omission claim cannot be accepted
under that identification, and an undefined symbol is not identified by name
alone.

The algebraic corners precede the sandwich and daughter identities. Star
pairing then supplies the zero criteria. Invertibility of `1+V` supplies the
rational unitary. Native ordered C-star functional calculus separately
supplies the spectral equivalence. No analytic conclusion is inferred from
the integral coordinate model.

PR #328 was also inspected. It owns a normalized real Reynolds projection
on `V=1`, polynomial evaluation with the constant-term correction, and
Hilbert common-kernel/coercivity results. It is not imported here: its
`ReynoldsProjection` and PR #329's `HomogenizedFourierDefect` currently
duplicate two declaration names. No compatibility between those independent
branches is asserted.

## Acceptance and open boundaries

Candidates are independently reviewed before integration; compiler commands
are serialized under the shared build lock. Acceptance requires exact-source
compilation, a fresh audit of all declarations owned by the new modules
(including generated/private declarations), staged proof checks, and semantic
review of hypotheses and carrier. Allowed axioms are only `propext`,
`Classical.choice`, and `Quot.sound`.

The universal quotient presentation, an Azumaya classification, bundle
transition cocycles, analytic limits, and any physical mass-gap conclusion
remain outside the proved contract. Root-Lake coverage must be reported
separately from a pinned focused source-closure check.

Validation is pending; no candidate is marked kernel verified by this initial
contract. Final declaration counts, commands, and observed limitations will
be recorded after compilation and independent review.
