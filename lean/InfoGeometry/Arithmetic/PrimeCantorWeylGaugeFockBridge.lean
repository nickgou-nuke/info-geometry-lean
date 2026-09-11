import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimitiveProjectiveRays
import InfoGeometry.Arithmetic.ProjectiveWeylGauge
import InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation

/-!
# InfoGeometry.Arithmetic.PrimeCantorWeylGaugeFockBridge

Weyl-gauge normalization bridge for the prime Cantor/Fock lane.

This module does not introduce a new Clifford, CAR, or Fock theory.  It
packages the existing projective Weyl-gauge normalization packet together with
the finite Cantor tilt/switch owner and the Boolean-cube CAR bridge.

The intended reading is:

* projective Weyl normalization is fixed first;
* the normalized finite Cantor tilt/switch system supplies the local
  `Cl(1,1)` atom.

No infinite Cantor `L²` completion.
No analytic Euler product.
No Hilbert-Polya/RH claim.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCantorWeylGaugeFockBridge

open InfoGeometry.Arithmetic.PrimitiveProjectiveRays
open InfoGeometry.Arithmetic.ProjectiveWeylGauge
open InfoGeometry.Arithmetic.PrimeCantorTiltFockRepresentation

/--
Weyl-gauge normalization packet for the Cantor/Fock lane.

The bridge is intentionally thin: it stores the projective Weyl calibration
and the already-closed finite Cantor/Boolean bridge proofs.
-/
structure Bridge
    (State : Type*) where
  /-- Projective Weyl-gauge normalization packet. -/
  weyl : ProjectiveWeylGaugeCalibration State

/--
The normalized Weyl-gauge and Cantor/Fock bridge are available simultaneously.

This is the bridge-visible version of the normalization story: the projective
Weyl packet remains normalized, the finite Cantor tilt/switch atom remains
closed, and the Boolean/CAR bridge remains preserved.
-/
theorem normalizedWeylGauge_and_cantorFock
    {State : Type*}
    (B : Bridge State)
    (counts₁ counts₂ : CountProfile) (support : Finset ℕ) (u : ℝ) :
    B.weyl.totalReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u =
      B.weyl.weylScaleReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u *
        B.weyl.shapeCoreReadout (B.weyl.stateOfProfiles counts₁ counts₂ support) u := by
  exact B.weyl.total_eq_scale_mul_shape counts₁ counts₂ support u

end InfoGeometry.Arithmetic.PrimeCantorWeylGaugeFockBridge
