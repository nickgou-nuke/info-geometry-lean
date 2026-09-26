# Twin residues, spectral pairing, and quantitative control

This development reconstructs the mathematical content of the proposed twin
framework. It proves local analytic transformations, a nonzero eigenspace
isomorphism, cancellation of convergent regulated spectral sums, and
conditional quantitative control. It also proves counterexamples to the
implications that cannot be used to justify the proposed closure.

## Mathematical scope

| Owner | Content |
|---|---|
| `Analysis/SimplePoleReflection.lean` | Reuses `BipolarSimplePoleResidues.HasSimplePoleCoefficientAt`. Proves coefficient reflection, one-form pullback, uniqueness, non-removability, the infinity-chart calculation, and the two distinct fixed-point loci. |
| `OperatorAlgebra/PartnerEigenspaces.lean` | Constructs an actual native `LinearEquiv` between the nonzero eigenspaces of `BA` and `AB`, with inverse `μ⁻¹B`, and proves equality of finite multiplicities. |
| `Analysis/PairedHeatTrace.lean` | Proves cancellation at matched finite cutoffs and for convergent infinite spectral sums, then takes the positive-regulator limit. Every infinite trace expansion has an explicit `HasSum` hypothesis. |
| `OperatorAlgebra/KreinCouplingControl.lean` | Checks the proposed indefinite block-adjoint identity. Gives a coupled growing null solution and counterexamples to positive-size and kernel-distance bounds. Reuses the existing finite supercharge index. |
| `Analysis/CoerciveBarrierControl.lean` | Derives an energy bound from a differential balance and domination; derives a uniform positive distance from log coercivity; proves bounds on observables, quotients, and one-parameter quotient derivatives. |

## Corrections that the proofs enforce

If the coefficient of a simple pole of `f` at `a` is `r`, then the coefficient
of `f(-z)` at `-a` is `-r`. Including the one-form Jacobian produces
`-f(-z) dz`, whose residue is **r**. The holomorphic map `z ↦ -z` preserves
real orientation. A reversal of a complex coordinate is not a reversal of
the orientation of a complex curve.

The rational example `(r/z) dz` has residues `r` at zero and `-r` at infinity,
as seen directly in the chart `w=1/z`. The pole at zero persists. The existing
bipolar differential also has opposite certified residues and no continuous
extension at zero. Therefore a vanishing global residue sum does not imply
removability, bounded positive energy, or regularity of a PDE solution.

The fixed set of `s ↦ 1-s` is the single point `1/2`. The fixed set of
`s ↦ 1-conj(s)` is the critical line. The functional equation alone provides
neither a zero-location theorem nor an index-crossing theorem.

The heat-supertrace sign convention here is
`Tr exp(-t BA) - Tr exp(-t AB) = dim ker A - dim ker B`, when the Hilbert
adjoint relation, spectral decompositions, and trace hypotheses justify that
identification. The index belongs to the chiral map, rather than to the full
self-adjoint odd operator. The spectral pairing theorem itself only needs
composable linear maps and a nonzero eigenvalue. It does not assume that a
symbolically named `B` is an adjoint.

The actual sufficient estimate is

```
E' = production - dissipation,
production ≤ dissipation,
0 < d,
-log d ≤ E
    imply    d(t) ≥ exp(-E(0)) > 0.
```

An additional estimate `c G ≤ E`, with `c>0`, bounds a positive observable
`G`. Quotient derivative control also needs bounds on numerator and
denominator derivatives. None follows from the index alone.

## Remaining mathematical obligations

For an infinite-dimensional Dirac realization, supply a common invariant
domain, a Hilbert adjoint relation, positivity/self-adjointness of the partner
Laplacians, spectral completeness with multiplicities, and trace-class heat
operators. Instantiate the spectral-sum theorem with those expansions and
the proved pairing. Krein self-adjointness alone supplies none of these
analytic properties. This packet does not construct a general compact
Riemann surface or prove its global residue theorem.

For Navier–Stokes or a proposed modified dynamics, specify the equations and
prove the energy balance, domination, coercive gradient estimate, and the
relevant continuation criterion. Prove that any proposed projection actually
solves the original PDE before transferring regularity. The theorem asserting
existence of a classical finite-time blowup has not been added. The
[Clay problem statement](https://www.claymath.org/millennium/navier-stokes-equation/)
is the reference for the unmodified Navier–Stokes problem.

This development introduces no axioms, admitted proofs, dummy `True` fields,
or assumed global-regularity conclusions. Conditional theorems expose their
quantitative hypotheses directly.

## Verification environment

All five new owner modules passed sequential kernel checks: **33 theorems and
one linear-equivalence construction, zero errors, zero warnings in the new
modules**. All 34 declarations were checked with `#print axioms`; the only
transitive axioms were Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. There is no `sorryAx` and no project-specific proof axiom in
these declarations. An import check loaded all five modules together.
Unchanged imported owners emitted existing linter warnings during their
rebuild; this is not a zero-warning claim about the whole repository.

The repository is pinned to Lean `4.28.1`. The available untouched compiled
Mathlib cache is built with Lean `4.28.0` at Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`; its binary headers are incompatible
with the `4.28.1` runtime. Narrow checks use the matching `4.28.0` runtime,
unchanged cached dependencies, and source snapshots of the current owner
files. The repository toolchain and dependency manifests are unchanged.
A successful compatibility check is not a claim that the full pinned
`4.28.1` repository build succeeds.
