# Pin representation, graded Morita, and operator compatibility

## Intake and baseline

The requested follow-up is: “connect that machinery to the particular Pin
construction with explicit representation, grading, operator, domain, and
family compatibility proofs.” It follows the source audit of geometric Dirac,
inner-graded Morita, split-Clifford colimit, and Hilbert operator owners.

The baseline is PR #338, commit
`1369d7181834704a5879e2e5dfcc0e1ad931131a`, based on upstream
`a392af178af1fe2bcba2ba39eb405700c6ee103c`. Its ordered Clifford maps and
normalized-vector Pin subgroup are the group and algebra carriers for this
follow-up. Lean `v4.34.1` and all root dependency revisions remain unchanged.

## Theorem contracts

| Layer | Construction and proof obligation | Existing owners |
| --- | --- | --- |
| Representation | Pull a native Clifford algebra representation through each ordered suspension; construct the represented normalized Pin group; prove exact generator order, compatibility with the restricted group maps, and preservation of intertwiners. | `Clifford.FreedCliffordSuspension`, `Clifford.NormalizedVectorPin` |
| Grading | Derive evenness of the suspended action from odd target Clifford generators. Construct the split atom's inner-graded module equivalence, with explicit grading conventions. | `Clifford.Cl11Matrix`, `OperatorAlgebra.PeirceSpine.InnerGradedMorita` |
| Residual coefficients | Construct graded matrix cancellation retaining an arbitrary noncommutative coefficient ring and its grading automorphism. Prove the comparison with the split Clifford graded tensor presentation when the required native graded algebra data are supplied. | `TripotentGradedMorita`, native `ModuleCat` matrix Morita, native `GradedTensorProduct` |
| Actual tower | Specialize the matrix presentation to the existing one-head algebraic factorization; prove compatibility with the canonical colimit grading and every actual fixed-head bond, retaining the full tail. | `Canonical.SplitCliffordHeadTailParity`, `SplitCliffordHeadTailTower`, `SplitCliffordTailParity` |
| Differential operator | Define a cover-level Dirac operator on the existing Klein spinor fields with `fderiv`; prove the actual orientation-twisted equivariance from the chain rule and Clifford reflection relations, then descend using the existing associated quotient. | `Topology.KleinCliffordPinLift`, `Topology.KleinAssociatedSpinors` |
| Concrete representation edge | Construct the suspended Klein representation using its internal volume operator, identify the full pullback with the existing Clifford representation, and identify the normalized Pin glide and differential coefficients. | `Clifford.NormalizedVectorPin`, `Topology.KleinCliffordPinLift` |
| Geometric grading | Double the two smooth equivariance sectors; construct the involutive diagonal grading and off-diagonal differential operator, and prove anticommutation and a nonzero smooth example. | The constructed Klein differential owner |
| Domain | Transport a submodule domain and a linear operator through a continuous linear equivalence; prove density and closed-graph transport, action compatibility, and transport of actual compact-resolvent identities. | `KK.RealSplitKreinLinearResolventBridge`, native topology and compact operators |
| Family | Instantiate operator/domain transport for represented Pin elements and exponential conjugation; preserve grading and chiral kernel data through explicit equivalences. | `Krein.ExponentialIsometry`, `Canonical.QuasilatticeDirac`, `KK.QuasilatticeIndexInvariance` |
| Native Fredholm family | Given a bounded source operator satisfying native `ContinuousLinearMap.IsFredholm`, construct its represented Pin and exponential conjugacy families, prove continuity into the Fredholm subtype, preserve the native kernel-minus-cokernel index, and apply native local stability. | Mathlib `Analysis.Normed.Operator.Fredholm.Basic` and `.Open` |

The differential reflection law must be checked before descent: the flat
Dirac operator changes the orientation character of the equivariance sector.
An assertion that it preserves an untwisted sector is not an acceptance target.
The two-dimensional Klein model and the existing three-dimensional quaternion
model are different carriers and are not silently identified.

The general matrix category consists of semilinear additive involutions.
An arbitrary-ring involution is not silently identified with a direct-sum
`ZMod 2` grading when two need not be invertible. The Clifford tensor
specialization uses a native real graded algebra, derives involutivity of
the coefficient parity from its homogeneous components, and retains the
full noncommutative coefficient algebra.

The analytic domain is a `Submodule`, and the unbounded operator is a linear
map on it. Density, closed graph, and compact-resolvent hypotheses must be
transported from named input data, not asserted for an unspecified geometric
operator. A compact resolvent is not used as an infinite-dimensional bounded
phase with compact square defect; those two compactness assumptions force
finite-dimensionality.

The bounded Fredholm statement uses Mathlib's actual strictness, closed-range,
finite-kernel, finite-cokernel, and complemented-kernel conditions. A source
Fredholm operator is an explicit input. Its Fredholm property is not inferred
from compactness of a resolvent. The native Fredholm index and a chiral
zero-mode dimension difference remain distinct definitions.

## Scope and dependency order

The algebra maps precede represented Pin actions; their generator identities
precede grading and operator intertwining. The differential formula and its
chain-rule calculation precede equivariant descent. Continuous conjugation
precedes graph/domain and resolvent transport, and kernel equivalences precede
index invariance. No index or physical interpretation is used to justify an
earlier algebraic identity.

This work targets explicit compatibility constructions. A general curved
Pin-frame bundle, geometric elliptic regularity, a general family index in
`KO(B)`, and differential `KO` groups and pushforwards are separate targets.
Existing algebraic direct limits are distinguished from analytic completions.

The concrete Klein smooth operator is connected to the particular Pin
construction by its actual representation, deck action, differential
coefficients, and smooth domains. These owners do not yet construct its
`L²` completion or instantiate it as the generic closed-domain or bounded
Fredholm seed. Likewise, the algebraic graded Morita equivalence does not
assert an analytic Hilbert-module equivalence. The actual tower specialization
concerns the algebraic colimit and naturality of its finite matrix
presentations, without asserting a categorical colimit of module categories.
The full represented Pin group and the subgroup preserving a particular deck
lattice are distinct claims.

## Acceptance

Each promoted owner requires an exact focused kernel build, declaration axiom
inspection, source/debt screening, and independent mathematical review.
Permitted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Root integration gates remain separate from the focused build.
The focused project reuses root-pinned dependencies; no root dependency,
toolchain, gate, or unrelated source is changed to obtain acceptance.

This initial contract records targets, not completed proofs. The final
verification record must identify the accepted source bytes, commands, results,
and any remaining obligations.

## Development validation status

Thirteen mathematical owners have been authored and independently reviewed
at source level. The selected-owner audit includes private and generated
declarations. Source review found no mathematical sign, order, carrier, or
circularity defect; it is not kernel acceptance.

The pinned dependency cache has been hydrated successfully. The initial local
kernel build is queued behind other live jobs using the shared build lock.
The focused GitHub Actions workflow runs the same project and declaration
audit on an independent runner. Compilation and the axiom audit are pending;
no current whole-root or geometric analytic-index certificate is claimed.
