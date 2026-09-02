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
import InfoGeometry.Canonical.FullNoncommutativeGibbsExpectationBridge

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
  the full noncommutative log-partition/expectation theorem.

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

At trace level the two exponential derivatives are now proved equal in every
operator direction.  This is exactly the strength needed for the Gibbs
expectation identity; no stronger operator equality is silently asserted.

Its purpose is compositional: downstream developments can import one module
while continuing to use the native theorem owners for every individual edge.
-/