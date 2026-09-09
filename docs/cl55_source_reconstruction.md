# Cl(5,5): occupation grading, two-boundary compression, deck obstruction, and log ratios

## Source and repository scope

Source: `Pasted markdown(20260905-165220).md` (323 lines). This is a corrected
mathematical reconstruction, not an endorsement of every assertion in that note.

The source was compared with actual theorem files on main
`b0fa422e6cb6d3da5be7cbbb5ecfae5c12f3237b` and relevant open branches. The
implementation is stacked on PR153 at
`55431fb0176b1279f696984bd7d95178cee55b25` to reuse its regular weak functional.
No pre-existing file is overwritten. This is a focused source audit, not a
claim that every file in the entire repository was semantically audited.

## Reused owners and exact scope

| Subject | Existing owner | What the source actually provides |
|---|---|---|
| Neutral Fock action | `Clifford/SplitClifford55ExteriorSpinor.lean` | Native exterior wedge/contraction, CAR, universal Clifford action, pure vacuum annihilator |
| Exterior dimensions | `Clifford/SplitClifford55ExteriorDegrees.lean` | Binomial homogeneous dimensions and a subset-indexed basis of the real exterior algebra |
| 32-dimensional readout | `Clifford/Cl55ExteriorSpinorCoordinateReadout.lean` | Basis-induced real coordinate equivalence and spinor finrank 32 |
| Clifford matrix equivalence | `Clifford/Cl55FockMatrixIntertwiner.lean` | Faithful and surjective Fock action, matrix algebra equivalence, comparison with the recursive representation |
| Chirality dimensions | `Clifford/Cl55EulerChiralFinrank.lean` | Complementary ranges with finranks 16 and 16 |
| Dyadic completeness | `Clifford/Cl55DyadicMoritaBridge.lean` | Full reconstruction using 32-by-32 matrix dyads, hence 1024 operator coordinates |
| Native CAR number operator | `Clifford/Cl55CARSpinAutomorphism.lean` | Creation/annihilation commutators and the actual five-mode number operator |
| Grade routing | `Clifford/Cl55OperatorFiveGradeClosure.lean` | Low-degree memberships and addition of adjoint grades; not a five-grade exhaustion of Cl55 |
| Contact Lie algebra | PR152 `Exceptional/FreudenthalSymplecticContactGrading.lean` | A separate concrete contact Euler element and a native Lie bracket adding its grades |
| Regular two-boundary readout | PR153 `Streaming/FiniteTwoBoundaryWeakFunctional.lean` | Nonzero-overlap domain, linear/unital weak functional, scale invariance |
| Existing static separation | PR153 `Streaming/WeakPropertySeparation.lean` | A finite support/property witness, not an automatically constructed physical current |
| Klein/pair glides | `External/Auto/KleinBottle.lean`; `Clifford/Pin55ReflectionGlide.lean` | Concrete transformations and their square/translation identities; commentary is stronger than some theorem statements |
| Anti-linear symmetry | PR145 `Quantum/QuaternionSpinTimeReversal.lean` | Anti-linear square-minus-one map; Kramers eigenpair theorem explicitly requires Hamiltonian commutation |
| Signed jumps | PR149 `SignedNetwork/BranchingEnsembleGenerator.lean` and companion event laws | Count-valued births and the local first-moment generator; not the entire continuous-time reconstruction theorem |
| Projective ratios | PR150 `Projective/ExpectationRatioMetric.lean` | Positive-ray ratio coordinates and a sup-norm/Hilbert projective metric; not the Aitchison Euclidean metric |
| Logarithmic barrier | `InformationGeometry/ItakuraSaitoBregmanBridge.lean` | IS equals the negative-log Bregman divergence, nonnegativity, common-scale invariance |

The PR metadata of different workstreams was not treated as a substitute for
reading the actual changed filenames and theorem owners.

## Corrected mathematical statements

1. The real exterior spinor is already implemented. Its complexification is
   additional scalar-extension data, not the same real 32-dimensional space.
   A null Witt basis is not orthonormal. CAR normalization must match the
   selected quadratic form; the native exterior normalization is retained.

2. If N is the existing number operator, a product of r creation operators has
   adjoint grade r. Centering N by 5/2 does not alter its commutator. The new
   source derives nonvanishing of every distinct creation word by stripping its
   first mode with a graded commutator. In particular the five-creation word is
   nonzero and has grade 5, not contact grade 2. The source's claimed universal
   five-grade truncation is therefore not used.

3. The supplied dimensions (1,16,34,16,1) do not specify a Lie bracket or an
   identification with an existing contact algebra. Ordinary brackets within
   one homogeneous component are alternating; a mixed (+1,-1) bracket has grade
   zero. Existing contact and occupation gradings remain distinct.

4. The rank-one normalized dyad P(x)=f(x)v/f(v) is an oblique projection in
   general. The new native-linear-map theorem proves P^2=P, its range and
   kernel, and P A P=[f(Av)/f(v)]P. The existing complex weak functional is
   connected to that formula directly. A 2-by-2 counterexample certifies that
   idempotence does not imply self-adjointness.

5. The native exterior-basis witness has readouts 0 on the singleton
   projection and 1 on the empty-to-full rank-one transition. This is a static
   matrix-coefficient separation. The rank-one transition is NOT silently
   equated with the separately normalized Cl55 creation word, and no current,
   propagation law, or contact interpretation is inferred.

6. Full affine inversion b(x)=c-x fixes c/2 and squares to identity. For
   c=(1/2,...,1/2), the fixed point is (1/4,...,1/4). Thus the proposed nontrivial
   transformation is not fixed-point free. A negative determinant does not
   establish a free deck action or the quoted manifold homology. Genuine
   existing Klein and split pair glides are reused as separate examples.
   Periodic T^5 coordinates are not automatically the real split Cartan.

7. A chiral direct sum is not a tensor product: discarding a summand is not a
   partial trace over a tensor factor. The simplex requires a separately
   specified positive normalized readout. The new CLR identity applies to
   positive coordinate representatives, with factor 1/(2*32)=1/64. It does not
   claim such a readout is produced by chirality alone.

8. The IS sum is a Bregman divergence, not automatically a Massieu difference
   or entropy production. The new source selects the positive flow
   x_i(t)=y_i+(x_i(0)-y_i)exp(-t) and proves the genuine derivative

   d/dt sum_i IS(x_i(t),y_i) = -sum_i (x_i(t)-y_i)^2/(x_i(t)y_i) <= 0.

   The choice of this dynamics is explicit. It is not identified with the
   signed Hamiltonian generator or a gravitational back-reaction.

## New owners

- `Clifford/Cl55CreationWordGradeObstruction.lean`
- `LinearAlgebra/RegularDyadCompression.lean`
- `Streaming/TwoBoundaryDyadCompression.lean`
- `Clifford/ExteriorBasisBoundaryWitness.lean`
- `Topology/AffineDeckFixedPointSeparation.lean`
- `InformationGeometry/FiniteChannelLogRatioBarrier.lean`

The aggregate is `Canonical/Cl55SourceReconstructionAll.lean`. The companion
`Canonical/Cl55SourceReconstructionAudit.lean` inspects every new theorem's
transitive axioms.

## Verification boundary

All theorems have explicit source proof scripts. No `sorry`, `admit`, custom
`axiom`, `unsafe`, or `native_decide` is inserted. This is NOT a claim that
these scripts have elaborated: neither `lean` nor `lake` is installed in the
working environment. The focused checker was attempted and exited 127 before
any Lean command could execute. Inherited dependencies also need a kernel run.

Independent exact arithmetic and symbolic checks cover CAR words, their
nonzero/grade/stripping identities, dyadic compression, the exterior-index
separation, affine fixed points, CLR algebra, and the specified IS relaxation.
Those tests are not Lean kernel proofs. The reported operator-grade dimension
table is an independently checked finite basis count, not a Lean declaration
added by this extension.

Run from the pinned repository root after applying this extension:

```
bash scripts/check_cl55_source_reconstruction.sh
```

The script builds the focused aggregate, executes all axiom queries, rejects
missing reports, and permits only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact subsequent boundaries

First obtain an executable kernel verdict and discharge concrete diagnostics.
Then calibrate the empty-to-full exterior dyad against the actual CAR top
creation operator through the existing Fock representation. A contact
identification must specify and intertwine a separate Lie bracket and Euler
element. A stochastic extension to a 32-level quantum system must use a
complete operator-coordinate frame and finish the trajectory/nonexplosion/
expectation proof, not reuse 32 populations as a complete density matrix.
