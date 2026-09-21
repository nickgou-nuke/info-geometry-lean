# Klein seam operator descent

## Source ownership audit

Discovery covered file-name searches and declaration/body searches across `lean/`
and `lib/`, followed by direct inspection of the owners below and their relevant
imports. This is a bounded source audit, not a claim to have read every repository
declaration or to have kernel-checked the new files.

| Concern | Existing owner | Reuse boundary |
| --- | --- | --- |
| Torus and free glide involution | `Topology/KleinBrillouinBase.lean` | Actual `AddCircle (2π)` coordinates; not a finite matrix sign quotient |
| Literal orbit quotient | `Topology/KleinBottleOrbitQuotient.lean` | `glideSetoid`, quotient map, exact fibres and surjectivity |
| Cover and local operator bundle | `Topology/KleinGlideCovering.lean`, `Topology/KleinOperatorAlgebraBundleCore.lean` | Existing covering and complex matrix-fibre construction remain unchanged |
| Continuous scalar descent | `Topology/KleinGlideSeamDescent.lean` | Existing continuous-map universal property; new operator API concerns algebraic vector-valued fields |
| Finite band descent | `Canonical/D6KleinDiracBands.lean` | A different finite carrier and conditional radicand positivity |
| Involution and twisted sectors | `Canonical/KleinBottleTwistedCommutantBridge.lean` | Reuse `KleinInvolution`; no `RealKleinGeometry` replacement |
| Parity closure | `Canonical/CartanSuperbracketClosure.lean`, `Canonical/Cl11ChiralCommutant.lean` | Existing sector multiplication and square rules remain owners |
| Dirac square | `Canonical/DiscreteDiracHodgeChiral.lean` | Reuse `diracHodge_sq_eq_hodgeLaplacian` after proving nilpotence survives descent |
| Exterior Dirac and real phase | `Canonical/DiracKahlerLaplacianOperatorBridge.lean`, `Canonical/ConcreteChiralHodgeDiracHestenesColimit.lean` | No replacement exterior complex or colimit construction |
| Linear quotient factorization | `Canonical/BoundaryFibonacciQuotientFactorization.lean` | Quotient by a submodule, distinct from functions on an orbit quotient |
| Weyl/wallpaper projection | `Canonical/Pin55WallpaperQuotientBridge.lean` | Existing finite projection, not an identification of a noncommutative torus with a manifold |
| Off-diagonal pairing | `Canonical/ZornBdGHamiltonianChiralBridge.lean` | Existing concrete matrix decomposition, not newly inferred from the seam |

## Added interfaces

`Topology/KleinRealOperatorDescent.lean` constructs a native real `LinearEquiv`
between functions on the existing quotient and glide-invariant torus fields.
It transports invariant-preserving endomorphisms using native `conjAlgEquiv`,
proves their evaluation and uniqueness, and transports nilpotence. Commutation
with glide pullback is a sufficient preservation criterion. The Dirac square
then follows from the existing ring-level owner. Restriction is delegated to
Mathlib's `LinearMap.restrict`.

`Synthesis/KleinDiracKahler.lean` proves the exact cancellation implication:

```
phase² = -1, twist(phase) = -phase
    ⇒ [twist(coefficient * phase) = coefficient * phase
       ↔ twist(coefficient) = -coefficient]
```

For a fixed state and fixed derivative satisfying
`derivative = coefficient * state * phase`, cancellation of a unit state
gives coefficient oddness. Without cancellability the proved conclusion is
only oddness of `coefficient * state`. The identity-state case is a corollary.
Zero coefficient remains compatible. Signed coefficient and phase fields,
with a fixed state field, yield a genuinely descended coupling on the existing
Klein orbit quotient.

The submitted double-loop commutation identity is already the theorem
`DiscreteDiracHodgeChiral.square_commutes_chirality_of_anticommutes`; the test
module applies it directly. It establishes commutation of the square, not an
exact order, a rotation angle, or a spin representation. No replacement
`KleinSylvesterGeometry` class is added.

## Dependency order and limits

The dependencies are branched:

* Torus glide and orbit quotient → invariant fields ↔ quotient fields.
* Invariant-preserving operators + that equivalence → descended operators.
* Square-zero components + operator descent → quotient Dirac square.
* Reversed invertible phase + fixed product → odd coefficient.
* Fixed cancellable state + invariant equation → coefficient parity.
* Signed fields + orbit quotient → descended coupling.

No theorem here derives a spectral gap, nonzero mass, a propagator inverse,
an analytic Dirac operator, or a physical topology of spacetime. Equivariance
and continuity are not interchangeable. The link identifying a particular
Cuntz/Sylvester representation with the literal glide quotient still requires
an explicit compatible representation; it is not supplied by naming the two
objects alike.

## Verification

Proof bodies contain no placeholders. Compilation has not been performed:
the shared build lane was occupied by an existing `lake build -R`. No competing
compiler was started. Once that build finishes, run the narrow locked target:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Synthesis.KleinDiracKahlerTests
```
