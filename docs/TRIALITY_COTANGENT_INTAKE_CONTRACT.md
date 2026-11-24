# Triality and cotangent automorphism theorem contract

## Provenance and intent

The intake is the user's Lean proposal in namespace
`TrialitySymplecticGroupoidBridge`, supplied on 2026-11-24. Its text is
preserved in `docs/intake/triality-cotangent-20261124/proposal.lean.txt` as a
faithful transcription with a final newline. It is untrusted mathematical
input, not a compiler receipt. The proposed source is not imported by the
project.

Frozen input SHA-256:
`d20e0b8cf6e90fe3865486462b00557d27ae9c07847dd5858a28ff3cdae5f77b`.

The implementation starts from PR #442 head
`af3434ad4dae8505cd759fa3901132564a6ad51e`, tree
`c47f11d01de1097c15305f3dfed42efcd3176716`. That draft and its parents are
reused source; publication is not evidence of native acceptance.

During this work, PR #442's hosted compiler run exposed three proof-script
errors and three warnings in its affected scope. A separately reviewed
four-file repair was published there as
`67a54aed7f4d860a531fe012c606f9bc79a37c5d`, tree
`4bc40893148ea582c4c05c7619fe48981bbe4cfe`. The new triality/cotangent PR is
stacked on that repaired head. Its theorem statements and dependency pins
were unchanged; the repaired native run is a separate acceptance obligation.

The requested content is an algebraic cotangent action, its automorphism and
fixed arrows, preservation of the actual bilinear cotangent form, and a
specific four-dimensional triality coordinate convention. Smooth geometry and
Lie-theoretic interpretations require their own compatibility constructions.

## Atomic claims and disposition

| Intake atom | Exact mathematical content | Disposition before native validation |
|---|---|---|
| `coadj` | Inverse pullback of a representation on the algebraic dual | Reuse native contragredient owner and bundle the action laws |
| `CotangentArrow` and total `mulArrow` | Pairs of a group element and a source covector; the proposed multiplication ignores endpoint matching | Replace with Mathlib `ActionCategory`, whose composition has typed endpoints |
| `liftAuto` | A group automorphism and compatible linear automorphism induce an equivariant map | Construct a native functor/equivalence using the actual compatibility equation |
| Fixed arrows | Fixed group elements act on fixed covectors | Construct the restricted native action groupoid, with inclusion into the original groupoid |
| `cotangentSympForm` | Scalar evaluation expression plus an arbitrary unbundled bracket term | The input does not imply bilinearity or alternation; reuse `CotangentBilinearGraph.cotangentForm` with a native Lie bracket pairing |
| Form invariance | The contragredient lift transports the bracket term and evaluation pairings | Conditional algebraic theorem under the stated intertwining hypotheses |
| Every fixed locus is symplectic | Restriction of a preserved nondegenerate form remains nondegenerate | **False for arbitrary automorphisms**: the cotangent lift of a unipotent shear is a counterexample |
| Order-three repair | A preserved nondegenerate real bilinear form restricts nondegenerately to the fixed submodule of an order-dividing-three endomorphism | Prove by the orbit sum `y + A y + A² y`; no manifold conclusion |
| Hadamard involution | The displayed `M₊` | Already owned by `trialitySwapVS`; do not redefine it |
| First-coordinate reflection | `S = diag(-1,1,1,1)` | New coordinate convention, related explicitly to the existing last-coordinate reflection |
| Cyclic and dihedral relations | `C = M₊ S`, `C³=I`, `SCS=C²`, exact nontriviality | Transport through the proved change of basis and retain concrete matrix witnesses |
| Fixed plane | `v₀=0` and `v₁+v₂+v₃=0` | Native fixed submodule, explicit linear equivalence, and dimension two |
| Weight orbit | The two displayed images of `e₀` | Exact four-dimensional matrix calculations; representation labels are separate |
| Killing form and specified `so(4,4)` Cartan | Identification of these coordinates with a particular Lie algebra, Killing form, and outer automorphism | Existing owners must be inspected and a matching coordinate map proved; matrix orthogonality alone is insufficient |
| Canonical symplectic subgroupoid `T*G^τ` | Smooth fixed subgroup, cotangent identification, closed nondegenerate multiplicative differential form | Open geometric debt; not asserted by the algebraic implementation |

## Owner search and reuse

The search covers the repository's `lean/InfoGeometry` owners, their imports
and consumers, and the pinned Mathlib source. It distinguishes source-owned
statements from comments and older reports.

- `Algebraic/CartanSouriauActionGroupoid.lean` already exposes the native
  `CategoryTheory.ActionCategory` for the affine cocycle action.
- `Canonical/SouriauContragredientPairing.lean` owns inverse pullback,
  `contragredientLinearEquiv`, pairing invariance, and the general-linear
  contragredient representation.
- `Twistor/RealDualTwistor.lean` owns `frameAction` on the actual
  `V × Module.Dual ℝ V`, the untwisted alternating bilinear form, and its
  nondegeneracy without a finite-dimensional hypothesis.
- `Algebraic/CotangentBilinearGraph.lean` owns the twisted cotangent bilinear
  form, its alternating condition, and the signed graph calculation. It does
  not provide manifold geometry.
- `Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean` owns `trialitySwapVS`,
  the **last-coordinate** reflection `trialitySwapSpin`, their presentation,
  a native joint fixed submodule, `s3FixedCartanEquiv`, and its finrank. Its
  later root and Lie-theoretic consumers use that specific convention.
- Mathlib owns `LinearMap.eqLocus`, `LinearMap.BilinForm.restrict`,
  `LinearMap.Nondegenerate`, native actions, categories, groupoids, functors,
  and linear equivalences. These structures are the implementation carriers.

The signed permutation

```text
Q(v₀,v₁,v₂,v₃) = (-v₃,v₁,v₂,-v₀)
```

is an involution, commutes with the existing Hadamard involution, and conjugates
the old reflection to the proposed one. The implementation must prove those
identities before transporting the fixed-plane and presentation results.
No equality of coordinate conventions is inferred from the word “triality.”

The original 122-line elementary matrix block is moved to
`Lie/TrialityCartanMatrixCore.lean` with its nine original names, types, and
proof bodies retained. Its block SHA-256 is
`4accd6d59f1397005999062100d15ab0a046f9199829a646907f2ddffbd81ea2`.
The larger synthesis imports that module, preserving its downstream API.
The focused native check and a separate build of that synthesis are distinct
acceptance surfaces.

The deeper synthesis also contains explicit root permutations and folded
weights, a 14-dimensional fixed coordinate carrier, a Cartan-commutator
intertwiner, and `s3FixedToG2LieEquiv`. That last equivalence uses
`s3FixedSolderedBracket`, a bracket transported from the target matrix Lie
algebra. These results are not silently promoted to preservation of an
independently defined full D4 bracket by the new coordinate matrices.
The separate `RootSystem/D4TrialityAction` finite discriminant-class action
and `CanonicalZornOuterTrialityGroup` related-triples action are also not
identified with this four-dimensional matrix action here.

## Counterexample and sufficient repair

The original arbitrary bracket has an earlier obstruction: take `g = ℝ`,
`bracket x y = 1`, `α = id`, and all automorphisms equal to the identity.
Every stated intertwining condition holds, but the displayed scalar formula
has value one on two zero vectors. It is therefore not a bilinear form under
the original assumptions. Native `LieRing`/`LieAlgebra` data supply the missing
laws in the implementation.

For the real shear `A(x,y) = (x+y,y)`, inverse pullback sends a covector
`(a,b)` to `(a,b-a)`. Its cotangent lift fixes exactly the pairs
`((x,0),(0,b))`. The canonical alternating pairing vanishes on every pair
of such fixed vectors, even though the ambient pairing is nondegenerate.
This is a nonzero fixed carrier, so the restriction is degenerate.

For an endomorphism `A` with `A³=I`, the orbit sum `y+Ay+A²y` is fixed.
If `x` is fixed and the form is invariant, pairing `x` with that orbit sum
gives three times the pairing with `y`. Over the reals this proves that both
radicals of the restricted form vanish. This repairs the linear algebra
claim with an explicit finite-order hypothesis; it does not identify a
smooth fixed cotangent groupoid.

`Lie/CartanTrialityCotangentFixedForm.lean` applies this repair to the actual
provided matrix cycle: it constructs its linear equivalence with inverse
`C²`, proves that the existing contragredient lift has cube one, and derives
alternation and nondegeneracy of the canonical form on the lift's actual
fixed submodule. This is the explicit algebraic connection between the two
parts of the intake.

## Dependency and acceptance boundary

Only established maps create dependencies: representation to contragredient
action to typed action groupoid; intertwining to lifted functor; fixed
subgroup and stable fixed objects to the restricted groupoid; bilinear
transport to preserved form; order three plus nondegeneracy to a nondegenerate
fixed restriction; and the signed coordinate map to transported matrix and
fixed-plane results. These implications do not supply a Lie group, smooth
cotangent bundle, action functional, quantization, or physical model.

Native acceptance requires focused builds, fresh warnings-as-errors
elaboration, module-owned declaration inventory, and transitive axiom checks.
Source review, exact rational calculations, source scans, and publication are
reported separately. No `sorry`, `admit`, custom axioms, unsafe proof bypass,
or `native_decide` is permitted. The repository's Lean and dependency pins
remain unchanged.
