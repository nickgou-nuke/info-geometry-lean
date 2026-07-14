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

/-- The projective Klein packet exposes the Möbius involution directly. -/
theorem projectiveKlein_mobius_involutive :
    Function.Involutive mobiusInv :=
  (projectiveKleinRefocusingPacket).mobius_involutive

/-- The projective Klein packet exposes the two-sheet swap law directly. -/
theorem projectiveKlein_two_sheet_swap (x : HyperChart) :
    twoSheet (mobiusInv x) = Prod.swap (twoSheet x) :=
  (projectiveKleinRefocusingPacket).two_sheet_swap x

/-- The projective Klein packet exposes the sign-triviality witness directly. -/
theorem projectiveKlein_projective_sign_trivial :
    ProjectivelyEqual I2 minusI2 :=
  (projectiveKleinRefocusingPacket).projective_sign_trivial

/-- The projective Klein packet exposes the Klein-bottle glide identity directly. -/
theorem projectiveKlein_glide_reflection_identity :
    twistA * parabolicB * twistA * parabolicB = I2 :=
  (projectiveKleinRefocusingPacket).glide_reflection_identity

/-- The projective Klein packet exposes the explicit Möbius refocusing law directly. -/
theorem projectiveKlein_mobius_refocus (t : ℚ) :
    mobiusS.mulVec ![t, 1] = ![-1, t] :=
  (projectiveKleinRefocusingPacket).mobius_refocus t

/-- The projective Klein packet exposes the quotient descent contract directly. -/
theorem projectiveKlein_sign_kernel_trivial :
    PSLDescentContract :=
  (projectiveKleinRefocusingPacket).sign_kernel_trivial

end InfoGeometry.Topology.ProjectiveKleinCompactificationBridge
