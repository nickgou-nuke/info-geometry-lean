import InfoGeometry.Canonical.SplitOctonion1331PureSpinorGradingBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
import InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelFiniteDifference
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelContinuityReduction

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
* the self-adjoint finite-operator specialization in which `exp H` is strictly
  positive, `Tr(exp H)` is a strictly positive real partition function, and
  normalization yields the repository-native `FaithfulDensityOperator`;
* the native centered BKM covariance algebra, including zero first moment and
  subtraction of the product of expectations;
* the genuine two-point Fréchet numerator and quotient-rule derivative;
* the exact noncommutative finite-difference Duhamel identity
  `exp(a+r h)-exp(a) = r • ∫ exp((1-s)a) h exp(s(a+r h)) ds`;
* the reduction showing that continuity at `r=0` of that one parameterized
  Bochner integral is sufficient for operator-level
  `exponentialDerivative a h = duhamelDerivative a h`.

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
  five-flavour `c = 5` representation.

At trace level the two one-insertion exponential derivatives are proved equal
in every operator direction.  The stronger operator identity is now reduced
to the concrete topological statement

`ContinuousAt (duhamelPerturbationIntegral a h) 0`.

That continuity property is not stored as a law field and is not silently
assumed by this capstone.  The exact finite-difference formula and the
continuity-reduction theorem isolate it as the remaining operator-level
Fréchet--Duhamel edge.

For the second derivative the current strongest concrete statement is
separated cleanly into two proved sides:

* `NoncommutativeGibbsTwoPointFrechetBridge` gives the actual derivative of
  `H ↦ Tr(exp H * B)` as
  `Tr(exponentialDerivative H A * B)`;
* `NoncommutativeGibbsCenteredBKMCovariance` gives the exact centered
  Kubo--Mori/BKM covariance algebra.

On the self-adjoint Gibbs locus the logarithmic branch and faithful-density
normalization are already discharged.  What remains before calling the
concrete Gibbs Hessian the BKM covariance is therefore:

1. discharge the parameter-integral continuity above, hence obtain the full
   operator Fréchet--Duhamel identity;
2. identify the real CFC powers of the normalized exponential Gibbs density
   with the corresponding normalized exponential powers;
3. transport the two-insertion Duhamel integral to the existing Kubo--Mori
   pairing and compose with the proved centered covariance identity.

Until those theorem edges are proved, this capstone does not call the centered
BKM covariance the Hessian of the concrete Gibbs log-partition.

Its purpose is compositional: downstream developments can import one module
while continuing to use the native theorem owners for every individual edge.
-/
