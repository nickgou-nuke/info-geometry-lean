# Walecka parameters on the existing Zorn/Soloviev carriers

## Owner search and reuse

The source search used `context_preflight.py --include-external` plus declaration,
import, multiplication, regular-action, CAR/CCR, and five-grade searches. Generated
graph indexes were absent; the findings below come from inspected Lean sources,
not a generated graph or an external theory claim.

Existing owners, all under `lean/InfoGeometry/`:

- `Nuclear/SplitOctonionNambuGorkovBridge.lean`: `NambuGorkovCarrier`, `toZorn`,
  the Witt expansion, reduced norm and `bogoliubovEnergy`.
- `Canonical/SplitOctonionGogberashviliVectorMultiplicationBridge.lean`:
  `oldToVector` and its compatibility with genuine Zorn multiplication.
- `Algebra/ZornVectorMatrix.lean`: nonassociative dot/cross multiplication and
  `characteristic_equation`, reused to derive the trace-zero Hamiltonian square
  without duplicating the product expansion.
- `Algebra/ZornLeftCAR.lean`: `leftMultiplication`, its square law from
  alternativity, CAR, and an explicit counterexample to multiplicativity.
- `Physics/NuclearFiveGradeCommonCarrierRepresentation.lean`: the common
  `ℕ → (Fin 4 → ZornVectorMatrix ℝ)` carrier, five adjoint grades, fermionic
  representation, phonon CCR, and `coefficientLift`.
- `Physics/NuclearFiveGradeSolovievCommonCompression.lean`: `fullHamiltonian`,
  model embedding/projection, and exact two-channel Soloviev compression.
- `Physics/NuclearBdGSolovievAffineBridge.lean`: the existing centered BdG
  decomposition of that Soloviev matrix.

`Physics/OperatorZornMatrixAlgebra.lean` is an associative operator-block owner;
it is not substituted for split-octonion multiplication. No replacement Zorn,
Fock, CAR, CCR, or five-grade structure is introduced.

## Added adapter and dependency order

`Nuclear/WaleckaZornBdG.lean` supplies the missing parameter map
`xi = bareMass - scalarCoupling * scalarField` into `NambuGorkovCarrier`.
It uses the existing vector-carrier conversion, multiplies the actual native
Zorn elements, then transports the resulting square through the existing
left-regular action. The square is a proved product identity, not a definition
of a record containing a desired answer.

`Nuclear/WaleckaZornSoloviev.lean` lifts that endomorphism through the existing
coefficient action. The resulting operator has grade zero and commutes with
the existing phonon shifts. Multiplication by it preserves every represented
adjoint grade, using the existing `commutatorAction_product_component` theorem
from `Canonical/KantorPeirceFiveGrading.lean`. Separately, its scalar Bogoliubov energy supplies
the quasiparticle-energy parameter of the existing Soloviev Hamiltonian and
its model-space compression theorem.

Dependency branches are:

1. Native Zorn multiplication + Nambu carrier → element square.
2. Element square + left alternativity → endomorphism square.
3. Endomorphism + existing common carrier → coefficient square and grade zero.
4. Mean-field parameter + existing energy + existing compression → Soloviev readout.
5. Positive reduced mass + positive pairing square → strict ratio increase.

The fifth branch does not establish any new algebra/commutant interaction.
The scalar energy readout is not asserted to identify the coefficient operator
with the full quasiparticle–phonon Hamiltonian.

## Boundaries

The pairing ansatz is a four-parameter family inside the full eight-dimensional
Zorn carrier, not an identification of all split octonions with BdG states.
Operator composition is associative; the underlying Zorn product is not.
No Hilbert/Krein self-adjointness is inferred solely from the square identity.

Positive scalar coupling and field do not alone guarantee positive effective
mass; that requires `scalarCoupling * scalarField < bareMass`. At exactly zero
mass, Lean's totalized division makes the ratio zero, not infinity. A divergent
one-sided limit would require a separate limit theorem. The massless operator
square remains the actual pairing quadratic form.

This is not yet a self-consistent Walecka field equation, a density-dependent
chiral-restoration theorem, a full interacting Soloviev/RPA solution, or a
derivation of physical coupling to a Tomita commutant. The existing common
carrier is algebraic; this adapter does not add analytic Hilbert completion or
time evolution.

## Verification status

The three new modules contain explicit proof scripts and regression examples,
but remain **pending Lean 4.28.1 verification**. Dependency discovery resolves
8,041 pinned source modules for `InfoGeometry.Nuclear.WaleckaZornTests`.
The earlier sequential run stopped at a parser error in
`Spectrometry/WeightedQuadraticDescent.lean:29`, after compiling its Mathlib
dependencies and `GeometricMedianCore` with Lean 4.28.1. It did not check the
Walecka modules. No global integration or
whole-repository compilation is claimed.

Dependency discovery also found the empty local `lib/InfoGeometryCore` package.
The affected `Canonical/SplitCliffordSourceWickBase.lean` used it only for the
real two-by-two matrix alias. That owner now uses the already-imported
`FiniteSpin.Mat2R` instead, without creating a replacement core package or
changing the dependency manifest.

The pinned-source checker was corrected to pass Mathlib's configured
`autoImplicit=false` and `maxSynthPendingDepth=3`. This repaired the observed
`Analysis.Normed.Operator.Bilinear` dependency failure without modifying any
dependency source, manifest, or toolchain version.
