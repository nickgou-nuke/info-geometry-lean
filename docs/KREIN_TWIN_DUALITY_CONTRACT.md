# Exchanged Krein projections, twin duality, and real loxodromic pairing

## Source and repository

This continuation processes the four user attachments preserved byte for byte
under `docs/intake/krein-twin-duality-20261117/`. The manifest records their
original names and SHA-256 hashes; the first two notes are identical.
Statements of verification inside the intake are claims to audit, not build
evidence.

Development base: `nickgou-nuke/info-geometry-lean`,
`08c34e03f610b452e03422037949196dc7d92d6d`. The separate
`yang-mills-group/OpenAI-YM-20261028` repository is the submission snapshot.
No source or pin in that snapshot is modified by this continuation.

## Structural motifs and their mathematical order

| Motif in the input | Precise mathematical object | Established dependency |
|---|---|---|
| Mirror or reversal | An involutive adjoint reversing multiplication | Reversal and `P♯ = 1-P` determine the correct ideal side and Peirce corner. |
| Division into twins | An idempotent `p` and complementary endomorphism `1-p` | Idempotency gives complementary ranges; the exchanged-adjoint equation makes both ranges totally isotropic. |
| Mutual recognition | The restricted bilinear cross pairing | Ambient separation gives cross separation; finite dimension upgrades it to a perfect pairing and a dual equivalence. |
| Expansion and contraction | The reflection `K = 1-2p` and its real boost | The projection supplies an involutive, skew-adjoint generator and fixes the two eigen-sector signs. |
| Rotation within the flow | A real linear `J` with `J² = -id` | Skew-adjointness proves rotor isometry; commuting axes preserve the boost sectors and give reciprocal weights. |
| Conserved relation and observed size | An invariant bilinear form and a separately specified observer form | Isometry preserves the former; the quadratic scaling theorem computes the latter when its rotor-invariance premise is supplied. |

These are dependencies between explicit mathematical claims. Narrative
associations do not supply missing adjoint, nondegeneracy, dimension, or
dynamical hypotheses.

## Formal intent

The new implication starts with an actual idempotent linear operator `p` on a
real module and the adjoint equation

\[
B(px,y)=B(x,(1-p)y).
\]

It derives total isotropy of the two ranges, their complementary decomposition,
and nondegeneracy of the restricted cross pairing when the ambient form is
nondegenerate. In finite dimension it constructs a native perfect pairing and
an equivalence to the algebraic dual. Nondegeneracy is discharged for the full
real matrix trace/Dirac form in the concrete adapter.

The second implication takes the existing real boost/rotation action and
proves preservation of a specified bilinear form from skew-adjoint generator
relations. It also computes the reciprocal eigen-sector weights and their
effect on a separately chosen rotor-invariant quadratic form.

These are algebraic and finite-dimensional duality statements, together with
explicit real functions of the flow parameters. They do not assume positive
Krein norm, bounded all-time evolution, a Hardy space, a modular state, or a
Dirac field equation. No scalar complex phase occurs in the new theorem
statements or implementations. Existing imports may themselves contain complex
infrastructure; this is not a claim of a complex-free transitive import graph.

## Existing owners and exact reuse

| Owner | Reused content | Boundary |
|---|---|---|
| `Canonical.ParaKahlerLagrangianDimension` | `crossPairing_injective` for an isotropic summand and a spanning partner | The new argument derives its isotropy premise from exchanged adjoints. |
| Native `Mathlib.LinearAlgebra.Projection` | Complementary range/kernel structure of an idempotent | No positivity assumption. |
| Native `Mathlib.LinearAlgebra.PerfectPairing.Basic` | `LinearMap.IsPerfPair`, `toPerfPair`, dimension comparison | Algebraic perfectness uses finite dimension. |
| `Physics.KreinDiracKasparovSpinorBilinear` | `KasparovKreinData.diracAdjoint`, multiplication reversal, involution | Algebraic fundamental symmetry, not an analytic Kasparov cycle. |
| `CliffordWeyl.KreinIdealBilinears` and `Algebra.IdempotentCornerCommutant` | Existing left/right ideal conventions and adjoint transport | `P A` is a principal right ideal; `A P` is a principal left ideal. |
| `Core.PeirceMatrixTracePairing` | Cyclic trace and full matrix separation | Ordinary matrix trace is cyclic here because entries are real; arbitrary noncommutative coefficients would need a cyclic functional. |
| `Core.TripotentKreinBlocks` | `sharp_jointPeirceProjector`: `(a,b)` maps to `(-b,-a)` | Already contains the corrected corner law; no replacement owner is introduced. |
| `Canonical.HestenesLoxodromicRotor` | Real action, composition, inverse, four-channel formula | New form preservation is proved, not assumed. |

`DiracPeircePerfectPairing` treats two-sided corners under the different
condition `diracAdjoint P = P`. The new theorem treats one-sided ideals with
`diracAdjoint P = 1-P`; these hypotheses must not be interchanged.

## New owner contracts

### `Krein.ExchangedProjectionPairing`

Carrier: an arbitrary real module `V`; native bilinear form
`B : LinearMap.BilinForm ℝ V`; native endomorphism `p : Module.End ℝ V`.

Inputs are `IsIdempotentElem p`, the displayed adjoint equation, and whichever
ambient separation assumption the conclusion requires. Neither symmetry nor
finite dimension is used for total isotropy or cross nondegeneracy.

Outputs:

- Native complementary submodules `range p` and `range (1-p)`.
- Both restricted forms vanish, including mixed pairs in the same sector.
- The actual cross restriction is separately injective in both arguments.
- With ambient nondegeneracy, it is nondegenerate.
- In finite dimension, it is `LinearMap.IsPerfPair`, induces an actual
  `LinearEquiv` to the opposite algebraic dual, uniquely represents every
  covector, and proves equal sector dimensions and half the ambient dimension.

The infinite-dimensional theorem gives separation, not surjectivity onto the
full algebraic or continuous dual. No analytic completion is constructed.

### `CliffordWeyl.KreinTwinIdealPairing`

Carrier: an associative, possibly noncommutative real algebra with its existing
algebraic Dirac adjoint. The functional `tau : A →ₗ[ℝ] ℝ` is explicitly cyclic.
The pairing is constructed as `tau (X * diracAdjoint Y)`.

The exchanged-idempotent condition derives the projection adjoint equation.
The matrix specialization uses all of `Matrix n n ℝ`, native matrix trace,
and actual nondegeneracy; it does not replace general matrices by scalar or
diagonal observables. The algebraic action-invariance theorem derives
preservation from the stated Dirac-unitarity equations and cyclicity.

### `Krein.LoxodromicPairingFlow`

Carrier: arbitrary real module with linear axes `K,J` and bilinear form `B`.
The existing predicates mean `K² = id`, `J² = -id`. Native
`B.IsSkewAdjoint` supplies the precise bilinear adjoint relation for each axis.

Outputs:

- The reflection `K = 1 - 2 • p` is involutive for an idempotent `p`,
  skew-adjoint for an exchanged-projection form, and has eigenvalue `-1`
  on `range p` and `+1` on `range (1-p)`. This supplies the actual bridge
  from the first owner to the flow hypotheses.
- The existing boost and real rotor each preserve `B`.
- Their composition preserves `B` without needing axis commutation.
- With commuting axes, the action is a native `B.IsometryEquiv B`, using the
  existing inverse with both parameters negated.
- On the positive and negative boost eigenspaces the action is respectively
  `exp t` and `exp (-t)` times the internal real rotor.
- On opposite eigenspaces, equal rotation parameters and unequal boost
  parameters give `B(L(t)x,L(u)y) = exp(u-t) B(x,y)`.
- Any bilinear form preserved by the rotor has quadratic weights
  `exp(2*t)` and `exp(-2*t)` on the respective eigenspaces. The theorem does
  not assert positivity of that form.

## Corrected intake claims

1. An anti-involution that exchanges projectors **preserves** each
   off-diagonal Peirce corner:
   `rev(P X Q) = P (rev X) Q` when `rev P = Q` and `rev Q = P`.
   It exchanges the two diagonal corners. A positive observer adjoint fixing
   each projector instead exchanges the off-diagonal corners.
2. Reversion takes a right ideal `P A` to the left ideal `A (rev P)`.
   It is not, by itself, a map into the opposite right ideal.
3. A diagonal corner has zero dilation weight, not necessarily zero value:
   `P * 1 * P = P` for an idempotent. Its vanishing is not a flow theorem.
4. Total isotropy refers to a bilinear form, not to a positive norm. A
   nondegenerate cross pairing does not make every pair of nonzero vectors
   have nonzero pairing.
5. Every finite-time boost is invertible. A family can be unbounded over all
   real times while preserving an indefinite form. Half-line contraction
   alone neither constructs Hardy spaces nor proves physical irreversibility.
6. A form-preserving internal rotation is not automatically a
   Tomita--Takesaki modular flow. The algebra, state/standard representation,
   modular operator and compatibility must be supplied and proved. General
   modular flow need not be periodic or compact.
7. For the native real spacetime current, the target is covariance
   `J(R psi) = R (J psi) (reverse R)`. Scalar invariants may be fixed while
   fixed-frame current components grow. A nonzero even spinor can have null
   reverse norm and null current; invertibility needs a nonzero norm factor.
8. Current conservation requires an actual field equation and differential
   hypotheses; positivity does not imply a bounded energy density or
   dynamical stability. Negative frequency is not negative physical mass.
9. A symmetric neutral form gives total isotropy. Calling a subspace
   Lagrangian requires a specified alternating form and the corresponding
   result. The narrative dependency graph proves no uniqueness of a physical
   theory.

The current formula and its geometric interpretation can be compared with
David Hestenes, [Clifford Algebra and the Interpretation of Quantum Mechanics](https://davidhestenes.net/geocalc/pdf/caiqm.pdf),
and the singular reverse-norm exception in
[Quantum Mechanics from Self-Interaction](https://davidhestenes.net/geocalc/pdf/QMfromSI.pdf).
The new Lean scope is the pairing/flow layer specified above; these references
do not substitute for native Clifford current proofs.

## Parallel work preserved

Source inspection found separate work based on the same upstream revision on
real loxodromic exponential orbit bounds, and on native real quaternion/Clifford
coordinates, the observer form and the current-time identification. Those
unpublished working trees are not dependencies and are not modified here.
Their existence does not count as validation of this continuation.

## Validation contract

Keep the repository's Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` unchanged. Use the maintained
`tools/quality/check_clifford_dirac.py` with the three exact targets, under the
shared build lock. Inspect every target declaration's transitive axioms and
reject any beyond `propext`, `Classical.choice`, `Quot.sound`. Require zero
warnings in the new owners, independent semantic review, the staged proof
gate, and the existing source audits. Record root Lake integration separately;
focused source-closure compilation cannot certify the entire repository.

Validation results are recorded separately after execution. This contract is
not a claim that any proposed source has already compiled.
