# Ground-truth theorem contract: concrete Fréchet–Leibniz Yukawa archetype

## Claim

Instantiate the existing registered finite-Yukawa Fréchet–Leibniz archetype
on the repository's concrete tilted, non-diagonal projection and amplitude,
transported from `Matrix (Fin 2) (Fin 2) ℂ` to
`SouriauOnsagerBKM.FiniteOperatorAlgebra 2` by the repository's `matrixOp`.
The conclusion is the existing archetype's continuous inner derivation and
its noncommutative Leibniz law, specialized to an actual operator input.

## Carrier and conventions

The target is the native continuous-linear-operator algebra
`FiniteHilbertSpace 2 →L[ℂ] FiniteHilbertSpace 2`; multiplication is composition
in the repository's `FiniteOperatorAlgebra` instance. `matrixOp` sends a
complex matrix to its continuous operator; `matrixOfOp` is its left inverse
and respects composition. The cut is the non-diagonal projection with all
entries `1/2`, and the amplitude is the non-diagonal self-adjoint matrix
`!![(1:ℂ), 1; 1, -1]`.

## Source-confirmed declarations

- `lean/InfoGeometry/Optics/OperatorDerivationForms.lean`,
  `FrechetOperatorDerivation` (line 107): a continuous linear endomorphism of
  a normed operator algebra with the explicit noncommutative product rule.
  Its `commutator_leibniz` theorem proves closure under commutators.
- `lean/InfoGeometry/Canonical/PeirceFrechetOperatorArchetypes.lean`,
  `PeirceCut` (line 36): the subtype of `FiniteOperatorAlgebra n` elements
  carrying the idempotence proof; `yukawaOneFormDerivation` (line 64) constructs
  the continuous inner derivation; `yukawaOneFormDerivation_leibniz` (line 80)
  proves its product law; `yukawaOneFormArchetype` (line 478) stores the proved
  claim and evidence.
- `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/PeirceArchetypeCausalSynthesis.lean`,
  `FiniteYukawaFrechetInput` (line 1042) and
  `finiteYukawaFrechetDerivationArchetype` (line 1049) define/register/audit
  the carrier-level archetype. `finite_yukawa_frechet_derivation_bridge`
  (line 982) proves its universal construction.
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CblinfunMatrix.lean`,
  `matrixOp`, `matrixOfOp_matrixOp`, and `matrixOfOp_comp` provide the actual
  matrix/operator carrier transport.
- `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/MatrixBlackHolePeirceD63.lean`,
  `d63TiltedProjection` (line 619), `d63TiltedAmplitude` (line 623), and
  `d63_tilted_projection_is_star_projection` (line 641) provide the concrete
  non-diagonal matrix data and projection law.

## Smallest source-confirmed gap

The registered finite Fréchet–Leibniz archetype and its universal evidence
exist, as do concrete matrix and continuous-operator carriers. Repo-wide source
search found no declaration applying this archetype to the tilted matrix
projection after `matrixOp` transport. Add that concrete application; do not
redefine the derivation structure or duplicate the Leibniz theorem.

## Causal order

`d63_tilted_projection_is_star_projection`
→ `matrixOp` preserves the idempotent equation
→ inhabited `PeirceCut 2` and `FiniteYukawaFrechetInput 2`
→ existing registered archetype discharges the continuous inner derivation and
  Leibniz conclusion.

## Adjacent claims not established

This is a concrete finite operator instance, not an analytic continuum result,
a parameterized parity pump, a spectral-gap theorem, or a field-theoretic
interpretation. It does not identify the benchmark's omitted perturbation
family.

## Status: closed by owner implementation

The gap is implemented in
`lean/InfoGeometry/OperatorAlgebra/PeirceSpine/PeirceArchetypeCausalSynthesis.lean`:

- `d63FrechetOperatorCut` (after line 1074): inhabited `PeirceCut 2` from
  `matrixOp d63TiltedProjection`, idempotence discharged through
  `matrixOfOp_injective`, `matrixOfOp_comp`, and
  `d63_tilted_projection_is_star_projection.isIdempotentElem.eq` — exactly the
  contract's causal order.
- `d63FrechetYukawaInput`: `FiniteYukawaFrechetInput 2` with forward amplitude
  `matrixOp d63TiltedAmplitude` and backward amplitude
  `matrixOp (star d63TiltedAmplitude)`.
- `d63_tilted_frechet_yukawa_archetype_and_noncommutativity`: the registered
  `finiteYukawaFrechetDerivationArchetype 2` discharges by
  `TypedArchetype.discharge`, and the cut/amplitude pair is proved genuinely
  noncommutative via `d63_tilted_cut_amplitude_noncommute`. No derivation
  structure was redefined and the Leibniz theorem was not duplicated — the
  instantiation only consumes the owned universal bridge
  `finite_yukawa_frechet_derivation_bridge`.
