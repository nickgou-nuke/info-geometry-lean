import Mathlib
import InfoGeometry.Topology.ProjectiveKleinCompactification
import InfoGeometry.Canonical.PSLDescent
import InfoGeometry.Canonical.MobiusHyperbolicCompactification

/-!
# Projective Klein compactification bridge

This is the theorem-safe bridge between three already-existing owner layers:

* the explicit Klein glide-reflection identity on `2 × 2` matrices;
* the `±I`-insensitive `SL(2, ℝ)` descent contract;
* the compactified Möbius inversion on the two-sheet hyperbolic chart.

It does not claim a new global classification of projective/Klein spaces.
It packages the exact algebraic facts already proved in the owners above.
-/

noncomputable section

namespace InfoGeometry.Topology.ProjectiveKleinCompactificationBridge

open InfoGeometry.Topology.ProjectiveKleinCompactification
open InfoGeometry.Canonical.PSLDescent
open InfoGeometry.Canonical.MobiusHyperbolicCompactification

/-- The projective Klein refocusing packet. -/
structure ProjectiveKleinRefocusingPacket where
  projective_sign_trivial :
    ProjectivelyEqual I2 minusI2
  glide_reflection_identity :
    twistA * parabolicB * twistA * parabolicB = I2
  mobius_refocus :
    ∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]
  sign_kernel_trivial :
    PSLDescentContract
  mobius_involutive :
    Function.Involutive mobiusInv
  two_sheet_swap :
    ∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x)

/-- The packet is witnessed directly by the existing owner theorems. -/
theorem projectiveKleinRefocusingPacket : ProjectiveKleinRefocusingPacket := by
  refine
    { projective_sign_trivial := projective_identifies_central_sign
      , glide_reflection_identity := klein_bottle_relation
      , mobius_refocus := mobius_refocus_vector
      , sign_kernel_trivial := pslDescentContract
      , mobius_involutive := mobiusInv_involutive
      , two_sheet_swap := ?_ }
  intro x
  exact twoSheet_mobius_swap x

/-- Readout theorem for the projective Klein compactification bridge. -/
theorem projectiveKlein_refocusing_readout :
    ProjectiveKleinRefocusingPacket :=
  projectiveKleinRefocusingPacket

end InfoGeometry.Topology.ProjectiveKleinCompactificationBridge
