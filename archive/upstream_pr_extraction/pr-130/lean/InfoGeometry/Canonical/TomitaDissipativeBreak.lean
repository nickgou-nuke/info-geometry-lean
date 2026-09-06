import InfoGeometry.Canonical.MetriplecticCore
import InfoGeometry.Canonical.TomitaStaticVsDissipative

/-!
# Retired Tomita/dissipative compatibility surface

This module intentionally exports no second metriplectic or parabolic model.

The former contents duplicated two scalar compatibility layers:

* the operator-algebraic bracket laws are owned by
  `InfoGeometry.Canonical.MetriplecticCore`;
* the equilibrium-versus-dissipative flow interface is owned by
  `InfoGeometry.Canonical.TomitaStaticVsDissipative`.

The old `ParabolicOperator` was a hand-written dual-number scalar model.  It
was not connected to the repository's noncommutative operator carriers, so it
is deliberately not promoted as a quantization or Tomita theorem.

Downstream code must import the native owners above and use their kernel-checked
theorems.  This file remains only as a stable import path for the umbrella
modules while the obsolete scalar namespace is removed.
-/
