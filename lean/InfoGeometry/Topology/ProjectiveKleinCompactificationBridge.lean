import Mathlib.Tactic
import InfoGeometry.Topology.ProjectiveKleinCompactification
import InfoGeometry.Canonical.PSLDescent
import InfoGeometry.Canonical.MobiusHyperbolicCompactification

/-!
# Projective Klein compactification bridge

Direct theorem composition between the exact rational Klein model, central-sign
invariance of the modular action, and compactified Möbius inversion.  No packet
stores these already-proved propositions.
-/

noncomputable section

namespace InfoGeometry.Topology.ProjectiveKleinCompactificationBridge

open InfoGeometry.Topology.ProjectiveKleinCompactification
open InfoGeometry.Canonical.PSLDescent
open InfoGeometry.Canonical.MobiusHyperbolicCompactification

namespace ProjectiveKleinRefocusingPacket

theorem projective_sign_trivial
    (h : ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
      PSLDescentContract ∧ Function.Involutive mobiusInv ∧
        (∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x))) :
    ProjectivelyEqual I2 minusI2 :=
  h.1

theorem glide_reflection_identity
    (h : ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
      PSLDescentContract ∧ Function.Involutive mobiusInv ∧
        (∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x))) :
    twistA * parabolicB * twistA * parabolicB = I2 :=
  h.2.1

theorem mobius_refocus
    (h : ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
      PSLDescentContract ∧ Function.Involutive mobiusInv ∧
        (∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x))) :
    ∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t] :=
  h.2.2.1

theorem sign_kernel_trivial
    (h : ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
      PSLDescentContract ∧ Function.Involutive mobiusInv ∧
        (∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x))) :
    PSLDescentContract :=
  h.2.2.2.1

theorem mobius_involutive
    (h : ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
      PSLDescentContract ∧ Function.Involutive mobiusInv ∧
        (∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x))) :
    Function.Involutive mobiusInv :=
  h.2.2.2.2.1

theorem two_sheet_swap
    (h : ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
      PSLDescentContract ∧ Function.Involutive mobiusInv ∧
        (∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x))) :
    ∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x) :=
  h.2.2.2.2.2

end ProjectiveKleinRefocusingPacket

/-- Canonical packet assembled from the native Klein, PSL, and Möbius owners. -/
theorem projectiveKleinRefocusingPacket :
    ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
      PSLDescentContract ∧ Function.Involutive mobiusInv ∧
        (∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x)) :=
  ⟨projective_identifies_central_sign,
   klein_bottle_relation,
   mobius_refocus_vector,
   pslDescentContract,
   mobiusInv_involutive,
   twoSheet_mobius_swap⟩

/-- Compatibility readout of the complete owner-backed packet. -/
theorem projectiveKlein_refocusing_readout :
    ProjectivelyEqual I2 minusI2 ∧
      twistA * parabolicB * twistA * parabolicB = I2 ∧
      (∀ t : ℚ, mobiusS.mulVec ![t, 1] = ![-1, t]) ∧
      PSLDescentContract ∧ Function.Involutive mobiusInv ∧
        (∀ x : HyperChart, twoSheet (mobiusInv x) = Prod.swap (twoSheet x)) :=
  projectiveKleinRefocusingPacket

/-- Möbius inversion on the compact hyperbolic chart is involutive. -/
theorem projectiveKlein_mobius_involutive :
    Function.Involutive mobiusInv :=
  ProjectiveKleinRefocusingPacket.mobius_involutive projectiveKleinRefocusingPacket

/-- Möbius inversion exchanges the two compactified sheets. -/
theorem projectiveKlein_two_sheet_swap (x : HyperChart) :
    twoSheet (mobiusInv x) = Prod.swap (twoSheet x) :=
  ProjectiveKleinRefocusingPacket.two_sheet_swap projectiveKleinRefocusingPacket x

/-- The projective rational chart identifies the two central signs. -/
theorem projectiveKlein_projective_sign_trivial :
    ProjectivelyEqual I2 minusI2 :=
  ProjectiveKleinRefocusingPacket.projective_sign_trivial projectiveKleinRefocusingPacket

/-- Exact Klein-bottle glide-reflection identity. -/
theorem projectiveKlein_glide_reflection_identity :
    twistA * parabolicB * twistA * parabolicB = I2 :=
  ProjectiveKleinRefocusingPacket.glide_reflection_identity projectiveKleinRefocusingPacket

/-- Explicit Möbius refocusing law on rational affine vectors. -/
theorem projectiveKlein_mobius_refocus (t : ℚ) :
    mobiusS.mulVec ![t, 1] = ![-1, t] :=
  ProjectiveKleinRefocusingPacket.mobius_refocus projectiveKleinRefocusingPacket t

/-- Direct central-sign kernel triviality on the upper half-plane. -/
theorem projectiveKlein_sign_kernel_trivial
    (g : SL2R) (tau : UpperHalfPlane) :
  (-g) • tau = g • tau :=
  (ProjectiveKleinRefocusingPacket.sign_kernel_trivial projectiveKleinRefocusingPacket).sl2r_kernel_trivial_on_base g tau

/-- Finite refocusing and compactified sheet exchange hold simultaneously. -/
theorem projectiveKlein_refocusing_and_sheet_swap
    (t : ℚ) (x : HyperChart) :
    mobiusS.mulVec ![t, 1] = ![-1, t] ∧
      twoSheet (mobiusInv x) = Prod.swap (twoSheet x) :=
  ⟨mobius_refocus_vector t, twoSheet_mobius_swap x⟩

end InfoGeometry.Topology.ProjectiveKleinCompactificationBridge
