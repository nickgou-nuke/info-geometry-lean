# Circular phonon coefficients and dressed interference

## Source and reuse

[Soloviev, Sushkov and Shirikova, *Dipole excitations in deformed nuclei*](https://www1.jinr.ru/Archive/Pepan/v-31-4/v-31-4-2.pdf),
printed page 788, equations (2)–(3), distinguishes electric-only phonons from
the combined electric/magnetic expression. The latter contains `1 ± iσ`:
these factors have both real and imaginary parts, not a purely imaginary total
coefficient. The paper attributes important spectral effects to interference
between orbital and spin amplitudes (abstract and printed page 787).
Page 788 was visually checked using the previously downloaded PDF.

A recursive content search across hidden/ignored and recovery Lean sources
produced 509 matching lines in `/tmp/soloviev-interference-reuse.txt`.
Inspected owners include `SolovievPhononCorrections`, `SolovievTwoModePhonon`,
`CliffordNilpotentInterference`, `RiemannKleinBottleThroatBridge`, and the existing
dressing/cocycle modules. The latter interference owners address different
identities; no replacement Clifford, Zorn, CAR, or five-grading is introduced.

## Exact results

`Physics/SolovievCircularInterference.lean` reuses `circularAmplitude` and
`phononCreation`. It proves their real/imaginary coefficient split, conjugation
under sign reversal, nonzero real component for nonzero amplitude, and the
operator decomposition into real coefficient combinations and an imaginary
coefficient combination. The operator decomposition itself assumes no star
structure or self-adjointness of the pair operators.

Mathlib's `Complex.normSq_add` supplies the strength cross term. Suppression
below the incoherent sum is equivalent to a negative real cross term; complete
cancellation requires exactly opposite amplitudes. The circular real-amplitude
specialization includes its normalization factor.

`Physics/SolovievDressedInterference.lean` proves that a common circle-valued
cocycle preserves the total strength, cross term, and cancellation criterion
between frames. The two amplitudes must transform by the **same** cocycle.
Separately, independent unit phases of the forward/backward phonon coefficients
preserve their exact CAR commutator, including the occupation correction. This
does not assert that the phonon operators themselves are phase-independent.

`Physics/SolovievInterferenceDependency.lean` records the parallel coefficient,
CAR, complex-strength, and cocyclic-transport dependencies as a finite partial
order. Dressed interference and phase-invariant commutators are incomparable
branches. This is a mathematical model, not inspection of Lean declarations.

## Excluded identifications

Destructive interference is not implied by commutativity, anticommutativity,
complex conjugation, or the mere existence of a modular conjugation. The tests
include conjugation-fixed amplitudes adding constructively. No identification
of orbital/spin amplitudes with a von Neumann algebra and its commutant is made.
No theorem derives a Tomita operator, a Clifford representation, a thermal
state, spherical-nucleus selection rules, a multiphonon spectrum, or a
six-quasiparticle/split-octonion identification from these scalar formulas.

The earlier dressing invariance theorem does not imply membership in the center
of an operator algebra. Its stabilizer obstruction is an algebraic obstruction
to an equivariant frame, not the Gribov–Singer theorem. The earlier normalization
result separates set-theoretic orbits; it does not construct a Krein-metric
orthogonal projection. These distinctions remain unchanged by this extension.

## Validation

Checks use installed Lean 4.28.0 and cached Mathlib, serially under the shared
build lock, with isolated outputs. Pinned Lean 4.28.1 remains unavailable; no
dependency metadata or caches are changed. This is not a full repository build.

All four new Lean modules compile. All six regression examples pass. Audits of
all 18 new theorems report only subsets of `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx`, custom axioms, or `native_decide` are used. Targeted
staged-diff whitespace checks pass.
