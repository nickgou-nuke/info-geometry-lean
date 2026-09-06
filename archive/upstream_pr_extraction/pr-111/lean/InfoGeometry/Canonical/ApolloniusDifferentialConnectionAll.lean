import InfoGeometry.Coordinate.ApolloniusLogCoordinates
import InfoGeometry.Bridge.ApolloniusPauliLift
import InfoGeometry.Canonical.ApolloniusGradientCircularBridge
import InfoGeometry.Canonical.ApolloniusPauliConnectionBridge
import InfoGeometry.Canonical.ApolloniusMaurerCartan

/-!
# Apollonius differential-connection import surface

This barrel collects the theorem-safe intrinsic layer added above the existing
Apollonius surprisal, winding, Pauli, and derivation owners:

* logarithmic Cayley coordinates on the twice-punctured plane;
* the critical-line zero locus and non-vanishing normal derivative;
* branch-aware reflection and exact source--sink inversion;
* finite pullback-metric distance toward infinity;
* the explicit diagonal SL(2, ℂ) Pauli lift;
* longitudinal light-cone and transverse circular weights;
* branch-independent rational differential of the logarithmic scale;
* orthogonal metric and circular responses generated from one covector;
* exact normal/tangential behavior on the critical line;
* unit bipolar-cometric norm away from the punctures;
* circular Pauli adjoint weights;
* the global rational q⁻¹dq Maurer--Cartan coefficient;
* cycle-indexed half-weight spin holonomies and their composite sign;
* commuting one-axis Cartan connection values and closed-implies-flat readout.

Conditional BdG/Andreev and scattering realizations are intentionally excluded.
-/
