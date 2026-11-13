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

The inverse construction for the Cayley denominator is ring-level. Its
unitarity and self-adjoint daughter conclusions additionally assume a native
`StarRing B`, `star P = P`, and the adjoint pairing `C = star A`.
The star conclusions in `StarDaughterGeometry` also use a self-adjoint cut;
the proper-star zero criteria explicitly carry their properness hypothesis.

| Atom | Owner and proved scope | Intake correction |
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
unitarity; the new work constructs its inverse fields from `1+V`.
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
over the polynomial coefficient subring generated by `V`,
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

## Validation record — 2026-11-12

The complete proof sources passed the
[focused CI run](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43242943544)
for PR #332. The published proof revision is
`1e523804d70cd472754147039d9053dcfb04ef76`; GitHub checked the synthetic merge
revision `0143bd3223f9d15d5273c1a4c3fd8975902ab2eb`. Both revisions have the
same Git tree, `743c6fe7c00870bf85df208f9f3bc9c751ace60e`, also matching
local commit `ac11b4ff52e461e5d106641675c9a6631935f389`.
This validation-record update changes documentation only.

The workflow freshly compiled all **53 repository modules** in the selected
import closure against the pinned environment above. It then audited all
**218 declarations owned by the ten selected modules**, including generated
and private declarations. Of these, **163 belong to the seven new owners**.

| Owner | Audited declarations | Origin |
|---|---:|---|
| `PeirceSpine.IntegralOrder` | 49 | New |
| `PeirceSpine.IntegralReynolds` | 35 | New |
| `PeirceSpine.IntegralOrderReynolds` | 11 | New |
| `PeirceSpine.StarDaughterGeometry` | 21 | New |
| `PeirceSpine.UnitaryCayley` | 32 | New |
| `OperatorAlgebra.PositiveSpectralGap` | 11 | New |
| `Canonical.PeirceIntegralReynoldsCounterexample` | 4 | New |
| `PeirceSpine.HomogenizedFourierDefect` | 33 | PR #329 |
| `PeirceSpine.StarMetricNondegeneracy` | 6 | PR #329 |
| `Canonical.PeirceChannelCounterexamples` | 16 | PR #329 |

Here `PeirceSpine` abbreviates `InfoGeometry.OperatorAlgebra.PeirceSpine`;
the other prefixes are relative to `InfoGeometry`. The per-owner counts
reconcile exactly with the native audit's `AUDIT_COUNT: 218`.
The only observed axioms were `propext`, `Classical.choice`, and `Quot.sound`.
The audit rejects unsafe/partial declarations and any additional axiom.
All seven new owners compiled without warnings; existing dependency warnings
remain visible in the uploaded logs.

The workflow command, from the parent of its fresh `project` checkout, is:

```bash
python3 project/tools/quality/check_peirce_integral_cayley.py \
  --mathlib-root pinned-mathlib --output verification
```

The checker records copied sources, source hashes, the checked revision,
toolchain, compilation logs, and the native axiom audit in the workflow
artifact. It requires a new output directory. The final source-semantic
gate selected all seven new modules and reported zero findings; the normal
`proof_proxy_staged_gate.py` also passed for each code commit.

### Root build and repository-wide checks

The maintained `tools/infra/run_locked_lake_build.py` wrapper was run on all
seven new owners under the shared build lock. It exited with code 1 before
owner compilation because the configured `HomotopyHypothesis` package
directory, `external_refs/homotopy-hypothesis-lean4`, is absent. Read-only
preflight also confirmed absent configurations for `external_refs/atlas-lean`
and `external_refs/gift-framework-core`. No root-build success is claimed.

Other repository-wide jobs retain separate existing failures: the tracked
Lean debt gate reports 878 findings in 91 forensic/fixture files, with zero
package findings; the idempotent-chart checker has a Python syntax error in
the unchanged `tools/quality/check_operator_geometry.py`; and the docs job
cannot obtain the repository's GitHub Pages configuration. These do not
constitute a passing repository-wide gate. The focused kernel and axiom
result above has its explicitly stated scope.
