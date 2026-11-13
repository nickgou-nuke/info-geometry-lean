# Tripotent grading, involution and corner-generation contract

## Intake and baseline

The verbatim Bulgarian intake is preserved in
`docs/intake/tripotent_krein_morita_20261113.txt` (SHA-256
`91f298d175b92810a214d6696f4a4a588c2fa231ee5058449a8a74c0bf89d2c8`,
44,529 bytes). It is a proposed synthesis, not evidence of completed proofs.
The implementation starts from PR #323 at
`c23aa651772224079271a35a0acca5a3f9767354`, with unchanged root Lean and
Mathlib pins. This branch is stacked on that source, not a claim that #323
has merged.

The carrier is the original arbitrary unital associative real algebra `A`.
Integer components are the existing `InfoGeometry.Physics.Algebra.adGrade S k`.
Operator kernel statements use the actual `Module.End ℝ V` action on `V`.
No scalar, diagonal or commuting replacement of the noncommutative carrier
is used. Tripotence is `S * S * S = S`; any of the five grades may vanish.

## Source owners and dependency order

Existing Peirce projectors, five ranges, eigenspace identification, quintic
annihilator, adjoint rigidity, parity and associative signed bracket are reused.
The PR #323 Banach exponential-flow equivalence is not re-proved or relabeled
as an unbounded modular-flow theorem.

| Owner | Exact construction or theorem | Dependencies |
|---|---|---|
| Core.TripotentIntegerGrading | Native graded monoid, internal direct sum, graded algebra and algebra equivalence for existing integer eigenspaces; support in [-2,2]; opposite-degree composites centralize S | Existing eigenspace and Peirce decomposition owners |
| PeirceSpine.TripotentIntegerSuperbracket | Actual sum-degree subtype brackets and one super-Jacobi equality for all three integer indices | Integer grades; existing associative super-Jacobi |
| Core.TripotentInvariantSubspaces | Existing five projectors equal native Lagrange polynomial aeval; every adjoint-invariant submodule has an internal decomposition; native Lie-subalgebra restriction | Native polynomial, eigenspace and direct-sum APIs |
| OperatorAlgebra.TripotentCornerActions | Square-zero corners; disjoint projector ranges; strict middle-range/kernel chain; exact individual dual kernels and their intersection | Actual endomorphism action and Peirce identities |
| OperatorAlgebra.TripotentExtremalJordanPair | Existing JordanPair bundle on L ∩ A±2, with constructed triple, double-commutator agreement, outer/fundamental identities and six shared linearity laws covering both signs | Homogeneous multiplication, native Lie closure and existing Jordan triple |
| Core.TripotentInvolution | Star and Krein grade transport; native ordinary skew Lie subalgebras; exact central-correction invariance; anticommutator obstruction | Native star modules and the owned Krein adjoint |
| Core.TripotentKreinBlocks | Projector exchange, reflected corner adjoint and reconstruction of actual skew elements in degrees zero and one | Existing projectors/eigenspaces and Krein involution |
| Core.TripotentOddGeneration | Real spans of odd anticommutators equal products of successive corner submodules; exact criterion for filling each extreme corner | Peirce orthogonality and native submodule multiplication |
| OperatorAlgebra.TripotentGradeTransport | Native algebra-automorphism covariance, unit conjugation, reversal, stationary transport and fixed-total-degree cancellation of composite generators | Existing grades, native ConjAct and component multiplication |
| Core.TripotentAdjointDefect | Native endomorphism identity D⁴ - D² = 12 • (Π₂ + Π₋₂), without a nonvanishing claim | Existing eigenpower evaluation and reconstruction |

All ten owners have now passed the exact-source Lean checks and native
declaration-axiom audit documented in the acceptance record below.
Source-semantic review, compilation and axiom audit remain distinct checks.
No definition assumes the desired construction as a witness field.

## Corrections required by the intake

1. The quintic is an annihilating polynomial. It need not be the minimal
   polynomial, and all five weights need not occur. The corrected defect is
   D⁴ - D² = D²(D² - I) = 12(Π₂ + Π₋₂); the extra factor 3 is incorrect.
2. For self-adjoint S, star reverses every grade, and each nonzero integer
   grade has zero intersection with the ordinary skew submodule. Skewness of
   S suffices for adjoint invariance, but is not a necessary classification.
   The exact condition is that S + star S centralize every skew element.
   The same correction holds for the stated Krein adjoint.
3. Ordinary skew elements are closed under commutators. Their anticommutator
   is self-adjoint and belongs to the skew space precisely when it is zero.
   A Krein involution therefore does not automatically produce odd-odd
   superclosure, nonzero extreme sectors, a particular conformal algebra,
   or a specified internal gauge algebra.
4. A single nonzero extreme operator cannot have kernel equal to the middle
   range. The equations N₊N₋ = P₊ and N₋N₊ = P₋ suffice for the intersection
   formula; they are not necessary for it.
5. Corner generation uses native submodule products and real spans: finite
   sums of ordered products. It does not assert surjectivity of a single
   anticommutator. Filling one extreme corner is not global Morita equivalence.
6. For inhomogeneous factors, cancellation concerns the sum of terms of each
   fixed nonzero total degree, not each individual product. A reversing unit
   reverses grades without having square one. The full normalizer of degree
   zero need not have only two components: even diagonal degree zero in M₃(ℝ)
   admits all permutation symmetries.
7. The bounded flow criterion uses differentiation and adjoint rigidity.
   Connectedness alone is not its proof. An unbounded Stone/resolvent theorem
   needs its domain, self-adjointness, spectral construction and strong
   topology. KMS additionally needs the specified state, dynamics and strip
   boundary condition. None follows from tripotence.
   If K = -log ρ, then exp(itK) = ρ^(-it); the opposite sign reverses time.
   A density with kernel requires restriction to its support for its densely
   defined logarithm.

## Analytic boundary

The bounded source search inspected pinned Mathlib
`Analysis/InnerProductSpace/LinearPMap.lean`, with partial adjoints, dense-domain
and closedness results for self-adjoint partial maps, and
`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean`, with bounded
continuous-functional-calculus commutation. The repository's
`KK/RealSplitKreinLinearResolventBridge.lean` supplies inverse and domain/range
identities for specified resolvent data. The inspected owners do not construct
an unbounded spectral measure or its unitary group from that resolvent.

Genuine bounded KMS analysis already exists in `ComplexTimeCorrelation.lean`
and `FilteredGNSMatrixAnalyticKMS.lean`. Those owners use actual complex-time
correlations, strip bounds, density/exponential compatibility and twisted
cyclicity. This is not an absence claim about all KMS machinery.

The remaining unbounded implication is the native construction and proof of

`[S,(i-K)⁻¹]=0 → [S,E_K(B)]=0 → [S,exp(itK)]=0`,

followed by invariance of a chosen smaller algebra and the state-specific KMS
boundary theorem. Bounded `cfc` at a discontinuous function on the resolvent
spectrum, or bounded `CFC.log` of a noninvertible density, cannot replace this
step. `commuting_unit_preserves_adGrade` supplies the subsequent algebraic
implication only after actual commutation has been established.

## Validation history and acceptance

**The selected mathematical source is accepted.** Two separate fresh CI runs
compiled all 58 modules in its exact repository-source closure and audited all
157 declarations owned by the ten modules. The owners contain 101 named
source theorems, including four private theorems. The observed axiom union is
exactly `propext`, `Classical.choice`, and `Quot.sound`.

The [scoped acceptance report](tripotent_structure_acceptance.md) links the
independent source reviews, both exact-source snapshots, both complete
ownership-audit records, the independently reviewed artifact verifier, and the
checksummed final QA record. QA independently checked both downloaded
artifacts and their immutable commit/tree identities. The two native audit
logs and all 58 module-log hashes are byte-identical.

| Successful execution | Source checkpoint | Kernel job |
|---|---|---|
| First | `7dda7101e3340adab4bf85d535895b445854e3ea` | [131831152975](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43409179642/job/131831152975) |
| Second | `337d7ef1c9433d342e92ead649f95b6e2481780a` | [131838779166](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43409480149/job/131838779166) |

All 58 proof-source files, the focused kernel job, checker files and dependency
pins are identical between these checkpoints. The sole intervening change
installs and verifies `ripgrep` before the source/root gates. No manual job
rerun or third focused run was requested for acceptance.

Earlier local attempts stopped during cache setup with ENOSPC and compiled
zero repository modules. Earlier remote iterations compiled respectively
51, 55 and 56 modules out of 58; each stopped before the declaration audit
because compilation failed. The reviewed repairs corrected elaboration and
proof terms while preserving theorem statements, hypotheses and ordered
noncommutative products. Those failed attempts are not acceptance evidence.

The completed first successful run passed the actual nonempty staged gate on
exactly the ten owner paths. Its unchanged incremental and explicit full root
builds failed at `external_refs/homotopy-hypothesis-lean4`. Its theory scan also
emitted missing-`rg` errors despite a successful wrapper exit; that scan is not
accepted as substantive execution. At the final QA observation on
2026-11-13 at 10:55:37 UTC, the second run's prerequisite and staged steps had
passed, its incremental root gate had failed, and its explicit full root gate
was still in progress. The preserved record does not infer the latest failure
cause or full-check completion.

This is scoped mathematical-source acceptance, not a whole-repository build
certificate or merge acceptance. The existing root gates and pins remain
unchanged; their integration boundary is reported separately.

## Explicit interpretation limits

These algebraic constructions do not identify a canonical KKT Lie algebra
from tripotence alone. Horizon, infinity-twistor, supercolor, thermal-equilibrium
and physical-dynamics interpretations need further objects and compatibility
theorems. The unbounded resolvent/Stone/KMS extension remains a separate analytic
target; no assumption-only wrapper is presented as its construction.
