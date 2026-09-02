import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
import InfoGeometry.Canonical.SplitOctonion1331GradedProjectorActionBridge
import InfoGeometry.Canonical.Exterior3NativeGradedLadderBridge
import InfoGeometry.Canonical.HeisenbergColimitVirasoroGradedBridge
import InfoGeometry.Canonical.ConstructiveCurrentHeisenbergColimitBridge
import InfoGeometry.Canonical.CompletedCurrentRepresentationBridge
import InfoGeometry.Canonical.SolovievCircularInformationMetriplecticBridge
import InfoGeometry.Canonical.Cl55ChiralOccupationFiveGradeBridge
import InfoGeometry.Canonical.Cl11WittOccupationParityFactorization
import InfoGeometry.Canonical.Cl55ChiralParityNormalOrderingBridge
import InfoGeometry.Canonical.Cl55FiveGradeSuperParityBridge
import InfoGeometry.Canonical.NoncommutativeGibbsExpectationCyclicDerivative
import InfoGeometry.Canonical.FiniteCFCNormedExpGibbsBridge
import InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
import InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge

/-!
# Exterior–CAR–Virasoro–chiral operator geometry capstone

This module is the canonical import boundary for the theorem-level corridor
constructed by the imported owners:

* the `1 + 3 + 3 + 1` Peirce/exterior-degree decomposition and its projectors;
* native exterior creation and pure-spinor/Grassmannian readouts;
* CAR currents, their locally finite completion, the filtered Heisenberg
  colimit, and the represented Sugawara/Virasoro mode shift;
* raw and centered `Cl(5,5)` occupation, chiral projectors, ordered parity
  factorization, and the reduction of the five-grading modulo two;
* the four-coordinate Soloviev, split-octonion derivation, BKM/Berry,
  para-Kähler, and metriplectic readouts;
* the unconditional noncommutative Duhamel trace collapse;
* the arbitrary-direction Fréchet derivative of the traced exponential and
  the full noncommutative log-partition/expectation theorem;
* reconciliation of the finite Hermitian-CFC Gibbs weight with the native
  Banach-algebra exponential weight, including normalized matrix-state and
  canonical matrix/operator transport readouts;
* the native centered BKM covariance algebra, including zero first moment and
  subtraction of the product of expectations;
* the genuine two-point Fréchet numerator and quotient-rule derivative that
  isolate the remaining concrete Gibbs Hessian calculus edge.

The imported modules intentionally retain their distinct carriers. This
capstone does not assert any unproved definitional identification between:

* Zorn multiplication and exterior wedge multiplication;
* finite Soloviev Hamiltonians and Gibbs density operators;
* the four selected derivation slots and all of `Der(O_s)`;
* BKM operator carriers and trace-driver carriers;
* braid, Weyl, cyclotomic, and Galois actions;
* the finite centering constant `5/2` and a specified Hamiltonian vacuum
  expectation;
* the existing `c = 1` charged-Fock Virasoro representation and a hypothetical
  five-flavour `c = 5` representation;
* the operator-valued changed-origin exponential Fréchet derivative and the
  real Bochner--Duhamel operator before application of the finite trace.

At trace level the two one-insertion exponential derivatives are proved equal
in every operator direction.  This is exactly the strength needed for the
first Gibbs expectation identity; no stronger operator equality is silently
asserted.

For the second derivative the current strongest concrete statement is
separated cleanly into two proved sides:

* `NoncommutativeGibbsTwoPointFrechetBridge` gives the actual derivative of
  `H ↦ Tr(exp H * B)` as
  `Tr(exponentialDerivative H A * B)`;
* `NoncommutativeGibbsCenteredBKMCovariance` gives the exact centered
  Kubo--Mori/BKM covariance algebra.

The remaining analytic theorem is the identification of that two-insertion
Fréchet trace with the corresponding normalized Kubo--Mori interval integral.
Until that theorem is proved, this capstone does not call the centered BKM
covariance the Hessian of the concrete Gibbs log-partition.

Its purpose is compositional: downstream developments can import one module
while continuing to use the native theorem owners for every individual edge.
-/