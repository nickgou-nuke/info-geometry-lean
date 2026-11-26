# Circular spin, doubled real Weyl operators, and native Zorn channels

## Intake and theorem contract

Source: the user attachment `Pasted text(20261126-185712).txt`, supplied on
2026-11-26. The proposed namespace was
`CircularPolarizedSpinAndOctonionBridge`. The implementation base is
`fe24e350b08fdea04f74c0748ef9fd9417c47529`.

Attachment SHA-256:
`817a37cb512dd8f419d645dd5389eaf0215f37374a1724431d905cf1f35cdc97`.

The requested finite algebraic content is retained on native real matrix
carriers and the repository's existing Zorn carrier. The supplied replacement
`SplitOctonion` structure is unnecessary. No dependency or toolchain change is
part of this work.

| Layer | Existing source reused | New implication |
|---|---|---|
| Real Pauli matrices | `Clifford.GullDoranPseudoscalarBridge` | Quaternion relations, circular ladders, grading weights, and real soldering |
| Split two-sheet atom | `Clifford.SplitAtomDoubling.Basic` and `Cl11KleinTwist` | Doubled operators, mirror parity, chiral support, and Weyl square |
| Zorn channels | Native Zorn owners and `Canonical.LocalZornCl11Slice` | Actual multiplication on a single paired channel, with its sign conventions |

`RealCircularSpin.circularRepresentation` is an injective real algebra
homomorphism from the same `M₂(ℝ)` source to the circular matrix subalgebra.
`CircularSpinBridge.fixedChannel i` is an injective linear map to the native
Zorn carrier, with its unit and multiplication preservation proved separately.
Together these maps identify the selected matrix channel with its signed spin
realization; they do not extend that identification to the full Zorn algebra.

The dependency order is the native two-sheet and Pauli definitions, their
matrix identities, the doubled operator identities, and the separately
established same-channel Zorn multiplication. Similarity of names supplies no
extra map between carriers.

## Conventions and corrected interpretations

1. The internal phase is `-realPhaseAxis` from the existing real Pauli owner.
   This sign gives the attachment's positively oriented Hamilton triple.
2. The two circular operators square to zero and are nonzero. Their products
   are **negative** longitudinal projectors. The one-mode CAR normalization
   therefore uses `circularPlus` and `-circularMinus`.
3. The weights `+2` and `-2` refer to the commutator with the specified matrix
   `sigma 2`. A physical helicity theorem would need additional definitions.
4. Spatially reversed Pauli soldering is called `solderConjugate`. The real
   soldering matrix is symmetric, so spatial reversal is not its Hilbert
   adjoint. It is also not the ordinary real four-by-four matrix adjugate.
5. Chiral corner rotations have different corner units. Their cross products
   vanish. Mirror parity separates the displayed rotation and boost
   generators, but the two compact real spin blocks do not give a real Lie
   algebra decomposition of the Lorentz algebra. Recovering boosts from their
   difference uses multiplication by an internal phase matrix.
6. For an associative exponential, a generator with square `+1` has
   hyperbolic coefficients; square `-1` has circular coefficients. The Zorn
   paired generators are named by their algebraic signs. These identities
   alone do not classify physical spacelike directions or boosts.
7. A single Zorn channel supports associative two-by-two matrix multiplication.
   The full split-octonion product is nonassociative. The implementation must
   not identify that full product with composition in a matrix algebra.

## Validation record

The repository pins Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Validation uses the maintained source-closure checker
`tools/quality/check_clifford_dirac.py` with explicit targets, the pinned
Mathlib checkout, and an isolated output directory. It compiles the exact
repository dependency closure under the shared build lock and inspects every
new declaration's transitive axiom dependencies. Its scope is the selected
owners, not a whole-repository certificate.

At initial draft publication, local kernel checking is **pending**: the
source-closure checker is waiting on a pre-existing held shared build lock.
No local compiler or axiom success is claimed. The dedicated
`circular-real-spin-zorn.yml` workflow checks the same 13-module repository
source closure on a separate CI runner. Compilation, source scans, semantic
review, and root build coverage are reported separately in the pull request.

The semantic scanner's short-proof warnings require review rather than proof
obfuscation: the transpose of a Kronecker product is definitional,
`mirror8_transpose` follows from the actual symmetric atom, and
`twice_rotation` simplifies the explicit half normalization, and
`vectorEquiv_neg` records the definitional native coordinate transport. These are useful
coordinate/normalization lemmas, not stored theorem assumptions. The legacy
vacuity linter's unused-parameter heuristic likewise does not detect the
parameter used through the unfolded `rotation` definition. The CI source scan
rejects error-level findings and retains warnings for semantic review; a
separate check requires zero **Lean compiler** warnings in new owners.

## Scope

These are finite real matrix and native Zorn multiplication theorems. They do
not establish an infinite tensor limit, analytic field theory, a KMS system,
an identification of nonassociative multiplication with operator composition,
or a classification of physical representations.
