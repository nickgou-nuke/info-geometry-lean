import InfoGeometry.Clifford.Cl55RealSplitPinKernelCenter
import InfoGeometry.Clifford.Cl55Q55NativeSplitBridge

namespace InfoGeometry.Clifford.Clifford55

/-!
# Spinor reduction of the residual split-Pin kernel branch

The native kernel reduction has two branches.  The scalar branch is handled
separately; this file transports the other branch through the native graded
Clifford factorisation and its real spinor representation.  No matrix
surjectivity is assumed here.  The result is the exact matrix statement that
the later explicit `32 x 32` calculation must discharge.
-/

theorem realSplitPin_uniform_anticommutation_spinor
    (g : realSplitPin55)
    (hanti : ∀ v : V55,
      ((g : Cl55ˣ) : Cl55) * ι55 v =
        -(ι55 v * ((g : Cl55ˣ) : Cl55))) :
    ∀ v : V55,
      cl55SpinorRepresentation ((g : Cl55ˣ) : Cl55) *
          cl55SpinorRepresentation (ι55 v) =
        -(cl55SpinorRepresentation (ι55 v) *
          cl55SpinorRepresentation ((g : Cl55ˣ) : Cl55)) := by
  intro v
  have h := congrArg cl55SpinorRepresentation (hanti v)
  simpa only [map_mul, map_neg] using h

end InfoGeometry.Clifford.Clifford55
