# Zorn Clifford triality: theorem contract

**Status: reviewed source candidate; Lean compilation and axiom acceptance
are pending.** The implementation below describes the mathematical contract
and its proof scripts, not a successful compiler result.

## Intake and source authority

The verbatim attachment is preserved at
`verification/zorn-cl44-triality/intake.txt`. The source baseline is
`fe24e350b08fdea04f74c0748ef9fd9417c47529`; the pinned environment is Lean
4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The attachment's assertions of successful compilation are intake claims,
not build evidence for this change.

## Mathematical contract

Use the existing `InfoGeometry.Canonical.ZornMatrix ℝ`, its actual
nonassociative multiplication, and associative `Module.End` composition.
`Canonical.ZornCliffordRepresentation` already constructs the native
quadratic form, doubled gamma operators, square law, and universal
`CliffordAlgebra.lift`. `Canonical.ZornMultiplicationOperators` owns left
and right multiplication. Reuse these owners without introducing another
octonion carrier.

The canonical multiplication has upper `-cross` and lower `+cross`.
The attachment uses upper `+cross` and lower `-cross`. Its coordinates
transport by `(a,b,v,w) ↦ (a,b,-v,-w)`. Accordingly its spatial ladders
are `-chiralUpperBasis` and `chiralLowerBasis`. The signed convention must
be proved compatible with the full product before basis identities are
reported in the attachment's notation.

The bilinear form is the native `zornNorm.associated`, with
`B(z,z) = zornNorm z`. The normalization is:

* `T₊(a,b) = (L_a L_conj(b) - L_b L_conj(a))/4`;
* `T₋(a,b) = (L_conj(a) L_b - L_conj(b) L_a)/4`;
* `Tᵥ(a,b)v = B(b,v) a - B(a,v) b`.

The central new theorem is the actual identity, for all vectors and spinors,
`T₊(a,b)(v*s) = (Tᵥ(a,b)v)*s + v*(T₋(a,b)s)`.
Its dependency chain is the native Clifford square law, polarization,
the associative double commutator, and extraction of the upper-right block.
No triality or Leibniz assumption may replace this construction.

For the calibrated quaternion axes `e_i` and split axes `f_i = ell*e_i`,
construct `D₁₂ = Tᵥ(e₁,e₂) - Tᵥ(f₁,f₂)`. Prove equality with the
corresponding difference of both spin actions, derive its Leibniz law, and
place it in the existing `CanonicalZornDerivation.canonicalZornDerivations`.
Its exact coordinate action is
`(a,b,x,y) ↦ (0,0,(x₁,-x₀,0),(y₁,-y₀,0))`.
In particular `D₁₂(e₁) = -e₂`, so it is nonzero.

Gamma exchanges the two summands of `DiracSpinor16`; its bivectors and the
diagonal derivation preserve them. These parity statements must not be
interchanged. The three actions also have actual native `IsSkewAdjoint`
proofs and membership in `skewAdjointLieSubalgebra zornBilin`. Their
infinitesimal norm preservation is constructed, not assumed.

## Faithful full Clifford representation

`ZornCl44Faithfulness` supplies the additional implication that the input
incorrectly inferred from the generator square laws alone. It constructs
a norm-preserving isometry to the existing `CliffordTower.Qsplit 4` using
the canonical coordinate equivalence and four explicit pairs:

* scalar pair `((a+b)/2, (a-b)/2)`;
* each spatial pair `((x_i-y_i)/2, (x_i+y_i)/2)`.

The inverse coordinates are explicit. The existing
`Cl11SplitTowerMatrixEquiv.splitTowerEquivMatrix 4` then gives an algebra
equivalence from the native Zorn Clifford algebra to real 16 by 16
matrices. Mathlib simple-ring injectivity applies to the original unital
`zornCliffordRepresentation`. Equal source and target dimensions, both
256, give surjectivity of that same representation and bundle it as
`zornCliffordEndEquiv`, with its generator action identified explicitly.

The existing `SplitOctonionNonmultiplicativity.e` was inspected: it
matches the negative Zorn norm and imports 304 repository modules. The
norm-preserving coordinate map here has a distinct sign and uses the narrow
canonical coordinate and split-tower owners directly. No existing carrier
or representation is replaced; no dependency pin is changed.

## Reuse search and scope

The bounded search covered canonical `lean/InfoGeometry` Zorn, Clifford,
Lie, algebra, and selected source mirror owners, their imports and direct
consumers. `Lie.TrialitySpin44Action` supplies a related-triple skeleton
and a conditional diagonal lemma; it does not construct these bivectors.
`Lie.CanonicalZornDerivationDimension` already parameterizes all derivations
and proves dimension 14. This change will reuse the existing Lie algebra
without reproducing that classification.

The eight generator relations alone do not prove faithfulness of the
universal algebra representation; the separate isometry/simplicity/dimension
argument above is required. The concrete infinitesimal identity does not
construct an outer `S₃` action or prove the general extension-and-uniqueness
form of Cartan triality. Those stronger claims require their own declarations.

## Acceptance

Required evidence is focused native compilation, fresh changed-owner
elaboration, a complete declaration axiom audit allowing only `propext`,
`Classical.choice`, and `Quot.sound`, independent source review, and the
repository's staged and publication gates at their actual scope.
Exact rational coordinate checks are supporting evidence only.

## Observed verification status

At 2026-11-24 09:53 UTC, the initial two-owner build had waited more than
43 minutes for the maintained shared build lock. Its status was `queued`
and its command count was zero. The lock was held by another
`real-matrix-split` transaction. No Lean elaboration, axiom-audit success,
or root/publication-gate success is claimed.

The five owner sources have received independent mathematical/source
review. The staged proof gate passed, and strict OpenGauss source screening
reported no findings. Independent exact rational calculations checked the
Clifford relations, triality basis triples, equality of the three selected
derivation actions, and the Leibniz identity. These are supporting source
and calculation results; they do not replace the Lean kernel check.

The full five-owner command is recorded in
`verification/zorn-cl44-triality/README.md`. It must freshly elaborate all
five owners and audit every owned declaration before compiler acceptance.
The queued initial run selects only `ZornCl44Triality` and
`ZornSignedConvention`, so success of that initial run alone would not
establish the full five-owner acceptance contract.

Repository publication has separate unresolved prerequisites. The root
package references local `HomotopyHypothesis` and `Atlas` packages whose
configuration/source directories are absent and are not recorded as source
or gitlinks in this baseline. Other tracked/path dependencies also need
materialization in this sparse checkout. No package stub, pin change, or
publication-gate bypass was used. The installed pre-push hook has not been
claimed to pass.

## Correction ledger

| Intake claim or risk | Canonical statement in the source candidate |
| --- | --- |
| The primal-dual product can omit the upper vector entry | Its upper vector entry is `p 0 • xSpatial`. |
| The two same-polarity ladder products need opposite signs | Both cyclic products have positive epsilon coefficients under the input convention. |
| The final narrative gives `D12(e1) = -e2/2` | The stated normalization gives `D12(e1) = -e2`; the attachment's theorem target already has this value. |
| The derivation exchanges chiral summands | Gamma is odd; Clifford bivectors and the selected diagonal derivation preserve both summands. |
| The Clifford square law establishes full faithfulness | A separate isometry, simple-ring injectivity, and equal-dimension argument is required and is supplied as a proof script. |
| A local `hTri` for fixed `a,b` can be specialized by `simpa` to another pair | Triality is a universally quantified standalone theorem, specialized to each pair before subtraction. |

The additional signed-basis recovery scripts make the convention explicit:
`ell^2 = 1`, `(ell*e_i)^2 = 1`, `e_i*ell = -(ell*e_i)`,
`u_i^+ = (e_i + ell*e_i)/2`, `u_i^- = (e_i - ell*e_i)/2`, and
`u_0^+ = (1+ell)/2`, `u_0^- = (1-ell)/2`.
