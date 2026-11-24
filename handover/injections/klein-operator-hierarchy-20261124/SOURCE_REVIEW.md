# Independent source review: Klein operator hierarchy

Reviewer: `/root/klein_review`
Date: 2026-11-24
Repository context: `/tmp/info-geometry-zorn-primal-dual-20261124`
Scope: three isolated source candidates and the preserved intake/theorem contract.

## Disposition

**Source-reviewed candidates; native validation pending.** No remaining definite
mathematical, sign, carrier, or pinned-API error was found in the snapshots below
after the two Clifford API corrections recorded here. The mathematical arguments
support the stated, bounded claims. This is authorization to integrate these
reviewed bytes for the normal validation process, not a compilation or axiom-audit
certificate.

No Lean compiler, Lake build, test, cache mutation, or owner mutation was performed
by this reviewer. The only reviewer-created artifact is this report. The parent
reported that another task still held the shared build lock; this review does not
claim independently to have exercised that lock or run the maintained checker.

| Reviewed artifact | SHA-256 |
| --- | --- |
| `clifford/ZornCliffordKleinHierarchy.lean` | `ea37f4082661ebee3c7519e290509c0162e51b9e4e2f61acca76e1db436cc5ba` |
| `incidence/ZornNullIncidence.lean` | `93c03658e0a7049f481bed255fbdb998cb00ac4e6bbb5b4f7162df34f11bd8e4` |
| `incidence/SplitOctonionNullPlaneCovariance.lean` | `43e69c589182d5eace8bf194b59648f7b110fb1549759d1805c0bef9e80346bd` |
| `handover/injections/klein-operator-hierarchy-20261124/CONTRACT.md` | `89bcdac0c46c4bd0dfa7f6e3962ffacaa0dadac833a52732155acc6a86009ace` |
| `handover/injections/klein-operator-hierarchy-20261124/INTAKE.md` | `d06528e80ea6dbd30010be3e22335a694d149cc318da8cc01c164c11e2b75bfb` |

The first three paths are relative to
`/workspace/scratch/5672353268f8/klein-candidates`; the last two are relative to the
repository context. Any optional oriented-volume candidate is outside this
disposition and must be reviewed separately.

## Resolved concrete findings

1. Mathlib's `CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero` takes the quadratic form
   explicitly. Both calls now pass `zornNorm` before the two vectors.
2. Mathlib's `ExteriorAlgebra.ι_add_mul_swap` has an implicit coefficient ring.
   The exterior readback now uses `(R := ℝ)` instead of an extra positional `ℝ`.
3. The contract now distinguishes the unhalved native polar form
   `P(x,y)=N(x+y)-N(x)-N(y)` from `B=P/2`. For
   `β(x,y)=[γ(x),γ(y)]/2`, its formula is correctly
   `[β(x,y),γ(z)]=γ(P(y,z)x-P(x,z)y)`.

A tentative concern about repeated finrank rewrites was checked against pinned
Lean rewrite implementation and withdrawn. It is not an outstanding finding.

## Clifford module: accepted mathematical scope

The owner uses the real specialization of the existing generic
`Canonical/ZornCliffordRepresentation.lean`. Its gamma action is the actual
off-diagonal product action
`γ(x)(s,t)=(x*t,conj(x)*s)` on `ZornMatrix ℝ × ZornMatrix ℝ`. The readback uses the
existing multiplication-preserving `canonicalVectorEquiv`, together with explicit
norm and conjugation compatibility. It does not silently substitute the similarly
named complex carrier.

The proposed dimension arguments correctly give carrier dimension 8, doubled
carrier dimension 16, endomorphism dimensions 64 and 256, and native Clifford
dimension 256. The Clifford dimension proof uses the Clifford-to-exterior linear
equivalence and the actual exterior basis indexed by finite subsets of `Fin 8`.
The finite-dimensional instances and the direction of `coordLinearEquiv.symm`
were checked. The dimension obstruction concerns linear equivalences with End(8);
equal dimensions of Cl(4,4) and End(16) do not establish an algebra isomorphism.

The chirality map `(s,t) ↦ (s,-t)` squares to identity and anticommutes with gamma
generators. The induction through native `CliffordAlgebra.induction` implements
Mathlib's involution on arbitrary Clifford elements; restriction to `spinGroup`
uses its actual involution-fixed property. These are parity statements on the
16-dimensional carrier. They do not identify chirality with a source-ordered
eight-vector volume element.

The half-commutator has both native even-submodule membership and a precise
exterior readback to `ι x * ι y`. The latter supports the simple exterior
two-vector interpretation; even membership alone would not establish integer
degree two. Clifford multiplication still mixes integer exterior degrees.

The bivector-vector commutator has the correct native unhalved-polar coefficients.
The bivector-bivector commutator formula is a sum of two simple bivectors and
retains noncommutative endomorphism multiplication throughout. Neither a
28-dimensional Lie-subalgebra equivalence with `so(4,4)` nor a differential gauge
connection/curvature is constructed here. There is also no faithfulness or
surjectivity theorem for the full Clifford representation in this candidate.

## Null-plane module: accepted mathematical scope

The projection `(a,b,v,w) ↦ (a+b,v-w)` is injective on every real linear subspace
on which the split norm vanishes. If the projection of a null vector is zero,
then `b=-a`, `w=v`, and the norm equation reduces to the negative of a sum of four
squares. The coordinate proof therefore has the right sign and proves the
required definiteness implication. Its restriction to a subspace gives the
dimension bound four.

For `x≠0`, right Kirmse contraction sends `x*y=0` to `N(y) • x=0`, proving every
kernel vector is null. Norm composition proves every image vector is null when
`N(x)=0`. Their two dimension bounds, carrier dimension eight, and rank-nullity
then yield both kernel and range dimension four for every nonzero null input.
There is no hidden trace-zero assumption. Maximality is correctly expressed
among norm-null linear subspaces, and internal polar isotropy follows by
polarization. The zero-input theorem correctly returns kernel dimension eight.

The two counterexamples correctly separate full-carrier product incidence from
norm-polar orthogonality. `E11,E11` has zero polar pairing and nonzero product;
`E11,E22` has zero product and polar pairing one. The first example uses the same
null vector twice and must not be advertised as a counterexample involving
distinct projective rays. Neither theorem claims that kernel elements mutually
multiply to zero.

## Automorphism and derivation module: accepted mathematical scope

The covariance owner restricts the existing explicit canonical/vector coordinate
equivalence to the two actual left kernels and transfers the full nonzero-null
dimension-four theorem to the canonical real carrier. Its norm conversion uses
the genuine Zorn determinant formula.

The acting objects are members of the existing subgroup of invertible linear
maps preserving the actual multiplication and unit. Multiplication preservation
and injectivity give the kernel-membership equivalence, the restricted linear
equivalence, submodule-map equivariance, and equality of kernel dimensions.
These conclusions are derived; they are not stored as assumed covariance fields.

The structure-constant theorem transports both multiplication inputs and the
coordinate basis. Pinned `Basis.map` is defined by the inverse linear map
followed by the original coordinate equivalence, so the candidate's `change`
step has the correct direction. The theorem does not assert fixed-coordinate
invariance under an arbitrary orthogonal transformation.

The derivation theorem retains both differentiated factors:
`(D x)*y + x*(D y)=0` when `x*y=0`. The fixed-kernel preservation result correctly
requires `D x=0`. No general fixed-kernel invariance for arbitrary derivations is
claimed. These are algebraic covariance statements, not a construction of a
smooth gauge field or a new group-level classification of split G2.

## Contract and intake

The intake preserves the proposed assertions as input. The contract correctly
separates the 4+4 Witt splitting from two 8-dimensional half-spinor spaces;
the full D4 null quadric from the classical Klein quadric and imaginary
split-Cayley hexagon; and triality of the three 8-dimensional representations
from its action on the 28-dimensional adjoint representation. Its P=2B convention
matches the candidate formulas exactly.

The contract also retains the necessary additional hypotheses for null-kernel
dimension, distinguishes multiplication automorphisms from general orthogonal
actions, and leaves the projective quotients, homogeneous spaces, full triality
identifications, group classifications, and cotangent symplectic groupoid outside
the implemented scope. These boundaries are consistent with the independently
reviewed primary mathematical references listed in the contract.

## Checks performed and remaining validation

The review read the three complete candidate sources, the contract and intake,
and bounded existing owner sources. Pinned Mathlib sources were checked for the
specific APIs used in finite-dimensional transport, finrank bounds and equality,
Clifford induction and grading, spin-group involution, change of quadratic form,
exterior basis/cardinality, and mapped bases. This is bounded dependency review,
not a transitive whole-repository audit.

The following source scan was run on the three candidates:

```text
rg -n '\b(sorry|admit|axiom|native_decide|unsafe)\b' <three candidate paths>
```

It returned exit status 1 with no matches. SHA-256 digests were computed with
`sha256sum` and the reviewed source snapshots remained stable on the final read.
A token scan cannot establish permitted axiom dependencies, successful
elaboration, or absence of an error in an imported owner.

Remaining acceptance work is native elaboration using the maintained serialized
wrapper, declaration-level axiom auditing of the elaborated owners, and the
repository's applicable staged/push gates. Any elaboration repair changes the
source hash and must receive a bounded follow-up review. No whole-repository
build or validation claim is made.
