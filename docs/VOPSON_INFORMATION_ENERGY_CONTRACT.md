# Vopson information-energy proposal: theorem contract

## Source and environment

Melvin M. Vopson, *Experimental protocol for testing the mass-energy-information
equivalence principle*, AIP Advances 12, 035311 (2022), DOI 10.1063/5.0087175.
The attached PDF has seven pages; its publisher cover is PDF page 1, so article
page numbers are one less than PDF page numbers. Published 4 March 2022.
Source SHA-256: `ab340a54eb158c85713c5fe644ac160bab29f1fb61d9f9170a73f48e5925944b`.

The implementation base is `936e5a90e24fbc7f9dc0a81d68573df86fd1f743`, which
contains the preceding boundary-reconstruction proofs. The upstream main
revision remains `08c34e03f610b452e03422037949196dc7d92d6d`.
Preserve Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Exact mathematical branches

| Intake | Carrier and assumptions | Intended conclusion | Status boundary |
|---|---|---|---|
| Logical erasure | Full matrices over a field; native trace and `LinearMap.smulRight`; trace-one prepared matrix | Exact traceless kernel, prepared-state range, constructive trace/remainder split, idempotence, nonmultiplicativity, no invertible conjugation | Finite operator algebra; positivity needed for a physical state/channel interpretation |
| Information mass, Eqs. 3-5 | Real quantities in fixed consistent units; proposed mass contribution `q/c^2`; nonzero `c` | Total mass already contains `q`; precise excess from counting it again | Does not derive the information-mass hypothesis |
| Conservation, Eqs. 7-10 | Explicit input/output balance; nonnegative extra-channel energies | Exhausted exact gamma budget leaves no positive extra energy; a repaired allocation reduces gamma energy | Approximate 511 keV labels do not rule out a small reallocation |
| Erasure heat | First-law balance `change = work - heat` and a heat lower bound | Countermodel to forced internal-energy decrease when supplied work is allowed | Does not refute the separate mass conjecture experimentally |
| Emission channel | Finite positive count, equal photon energies, emitted energy fraction | Wavelength depends on count and energy allocation; scalar conservation does not select two photons | No scattering amplitude, branching ratio, or detection theorem |
| Spectrum, Eq. 11 | Positive real `h`, `c`, `kB`, information, temperature | Inverse temperature/information scaling, exact inference formula, effective-parameter identifiability | Formula is a model; the additional fraction is emitted energy allocation, not detector efficiency |
| Momentum | Existing real FourVector and Minkowski quadratic form; future-null conditions | Two-particle opposition gives equal energies; total four-particle balance does not imply designated pairwise opposition | Units `c=1` (time component is energy divided by `c`); no spin/helicity scattering theory |

## Existing owners and reuse decisions

The bounded search covered native owner definitions, theorem statements,
imports, and consumers for entropy, Landauer, information mass, replacement
channels, CPT, annihilation, photons, and real momentum. No fresh declaration
graph index or exhaustive repository certificate is claimed.

- `Holographic.BoundaryReconstruction` constructs the actual splitting from
  `E D = id`. Specialize `E` to trace and `D` to native `toSpanSingleton sigma`.
- `Quantum.ReplacementStateChannel.replacement` has the same trace-reset
  formula and existing complete-positivity results under positive output state.
  The new algebraic results use the native `traceLinearMap.smulRight` expression
  directly, without defining a competing reset API. The existing 49-module
  complete-positivity import closure is not part of this selected verification.
- `Canonical.LandauerCramerRaoBoundBridge.landauerMinWork` defines
  `kB*T*log(2)*bits`; inspected Landauer owners prove positivity or consequences
  of supplied heat formulas. They do not derive intrinsic particle mass or a
  photon-conversion channel. The new balance theorems therefore take the
  proposed energy as explicit data rather than importing a physical conclusion.
- `Inference.FiniteGibbsThermodynamicIdentity` already owns positive normalized
  Shannon entropy and its maximum/uniformity theorem. No duplicate entropy
  definition or unsupported assignment of an ensemble average to each particle
  is introduced here.
- `Physics.LorentzBoostMinkowski` supplies the real four-vector and quadratic
  form for the momentum branch. Fock annihilation operators elsewhere in the
  repository are not identified with electron-positron scattering.

## Actual dependency edges

Trace normalization gives encoding/decoding consistency, hence the previous
reconstruction splitting. Native cyclic trace hides commutators; matrix units
give nonmultiplicativity and noninjectivity, hence the conjugation obstruction.

The mass assignment and explicit balance equations give the bookkeeping
results. Equal sharing and a chosen emitted-energy fraction give the spectral
law; that law gives inverse scaling and conditional parameter inference.
Future-null kinematics gives the two-photon energy equality, while a concrete
four-photon configuration tests the overstrong pairwise-conservation inference.

No theorem edge connects logical reset to thermodynamic cost, thermodynamic
cost to stored mass, or mass to a fixed photon-emission channel.

## Acceptance

Complete native proofs; no `sorry`, `admit`, custom axioms, `native_decide`,
unsafe bypasses, assumed conclusion fields, or commutative replacement of
matrix products. Only `propext`, `Classical.choice`, and `Quot.sound` may occur
in the declaration axiom audit. Compile the selected exact source closure
with the shared build lock, run source gates, and obtain separate source-review
and independent fresh-verification dispositions. State root dependency blockers
separately from the selected theorem certificate.
