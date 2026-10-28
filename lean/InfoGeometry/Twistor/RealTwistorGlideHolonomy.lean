/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Topology.KleinQuotientDeckInvariants
import InfoGeometry.Twistor.RealPluckerCl55Reflection

/-!
# Real twistor holonomy with the full affine glide

Integer powers of the real block rotation act on the twistor fiber over the
existing Klein covering-plane action. Two glides translate the base and negate
the twistor; four retain a nonzero base translation and restore the twistor.
The induced native Clifford reflection is involutive on its fiber. Its odd
infinity-origin channel carries a nontrivial sign, while the sum is invariant.
These are explicit deck actions and channel identities. The companion
`RealTwistorPinReflection` gives an algebraic Pin lift of the Clifford vector
action. An intertwiner with this four-dimensional twistor representation,
a geometric spin/Pin structure and an associated-bundle quotient remain
separate constructions; the `Alg 5` action is also kept distinct.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorGlideHolonomy

open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Canonical.Cl55InfinityWittBoundary
open RealTwistorBlockInversion RealPluckerCl55Reflection

/-- Integer winding of the actual real twistor automorphism. -/
def spinHolonomy (g : KleinDeckGroup) : TwistorSpace ≃ₗ[ℝ] TwistorSpace :=
  blockRotation ^ g.n

@[simp] theorem spinHolonomy_one : spinHolonomy KleinDeckGroup.one = 1 := by
  simp [spinHolonomy, KleinDeckGroup.one]

theorem spinHolonomy_mul (g h : KleinDeckGroup) :
    spinHolonomy (KleinDeckGroup.mul g h) = spinHolonomy g * spinHolonomy h := by
  exact zpow_add blockRotation g.n h.n

/-- The translation remains in the base component of the total action. -/
def totalSpinAction (g : KleinDeckGroup) (s : PlanePoint × TwistorSpace) :
    PlanePoint × TwistorSpace :=
  (deckAction g s.1, spinHolonomy g s.2)

@[simp] theorem totalSpinAction_one (s : PlanePoint × TwistorSpace) :
    totalSpinAction KleinDeckGroup.one s = s := by
  simp [totalSpinAction, spinHolonomy_one, deckAction_one]

theorem totalSpinAction_mul (g h : KleinDeckGroup) (s : PlanePoint × TwistorSpace) :
    totalSpinAction (KleinDeckGroup.mul g h) s =
      totalSpinAction g (totalSpinAction h s) := by
  simp only [totalSpinAction, deckAction_mul, spinHolonomy_mul, LinearEquiv.mul_apply]

def totalSpinGlide (s : PlanePoint × TwistorSpace) : PlanePoint × TwistorSpace :=
  totalSpinAction KleinDeckGroup.b s

@[simp] theorem totalSpinGlide_apply (s : PlanePoint × TwistorSpace) :
    totalSpinGlide s = (deckB s.1, blockRotation s.2) := by
  simp [totalSpinGlide, totalSpinAction, spinHolonomy, KleinDeckGroup.b,
    deckAction, deckB, signR, signZ]

/-- Squaring the glide retains translation and the twistor's central minus sign. -/
theorem totalSpinGlide_sq (s : PlanePoint × TwistorSpace) :
    totalSpinGlide (totalSpinGlide s) = ((s.1.1, s.1.2 + 2), -s.2) := by
  simp only [totalSpinGlide_apply, deckB_sq, blockRotation_sq]

theorem totalSpinGlide_four (s : PlanePoint × TwistorSpace) :
    totalSpinGlide (totalSpinGlide (totalSpinGlide (totalSpinGlide s))) =
      ((s.1.1, s.1.2 + 4), s.2) := by
  simp only [totalSpinGlide_sq, neg_neg]
  have hy : s.1.2 + 2 + 2 = s.1.2 + 4 := by ring
  rw [hy]

/-- The base translation prevents a fixed point for every choice of fiber map. -/
theorem glideFiber_no_fixed {F : Type*} (f : F → F) (s : PlanePoint × F) :
    (deckB s.1, f s.2) ≠ s := by
  intro h
  have hy := congrArg (fun t : PlanePoint × F => t.1.2) h
  change s.1.2 + 1 = s.1.2 at hy
  linarith

theorem totalSpinGlide_no_fixed (s : PlanePoint × TwistorSpace) : totalSpinGlide s ≠ s := by
  simpa only [totalSpinGlide_apply] using glideFiber_no_fixed blockRotation s

/-- The same base rescaling works for any real fiber carrier. -/
def scaleBase {F : Type*} (s : PlanePoint × F) : PlanePoint × F :=
  (halfShiftScale s.1, s.2)

def halfSpinGlide (s : PlanePoint × TwistorSpace) : PlanePoint × TwistorSpace :=
  (halfShiftGlide s.1, blockRotation s.2)

theorem scaleBase_halfSpinGlide (s : PlanePoint × TwistorSpace) :
    scaleBase (halfSpinGlide s) = totalSpinGlide (scaleBase s) := by
  rw [totalSpinGlide_apply]
  exact Prod.ext (halfShiftScale_glide s.1) rfl

theorem halfSpinGlide_sq (s : PlanePoint × TwistorSpace) :
    halfSpinGlide (halfSpinGlide s) = ((s.1.1, s.1.2 + 1), -s.2) := by
  simp only [halfSpinGlide, halfShiftGlide_sq, blockRotation_sq]

/-- Lift the vector involution to the whole native Clifford algebra. -/
theorem partialReflectionAlg_involutive (A : Cl55) :
    partialReflectionAlg (partialReflectionAlg A) = A := by
  have h : partialReflectionAlg.toAlgHom.comp partialReflectionAlg.toAlgHom =
      AlgHom.id ℝ Cl55 := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro v
    change partialReflectionAlg (partialReflectionAlg (ι55 v)) = ι55 v
    rw [partialReflectionAlg_apply_ι, partialReflectionAlg_apply_ι,
      partialReflection_involutive]
  exact DFunLike.congr_fun h A

def totalCliffordGlide (s : PlanePoint × Cl55) : PlanePoint × Cl55 :=
  (deckB s.1, partialReflectionAlg s.2)

/-- Fiber involutivity does not remove the square's base translation. -/
theorem totalCliffordGlide_sq (s : PlanePoint × Cl55) :
    totalCliffordGlide (totalCliffordGlide s) = ((s.1.1, s.1.2 + 2), s.2) := by
  simp only [totalCliffordGlide, deckB_sq, partialReflectionAlg_involutive]

theorem totalCliffordGlide_no_fixed (s : PlanePoint × Cl55) :
    totalCliffordGlide s ≠ s :=
  glideFiber_no_fixed partialReflectionAlg s

def halfCliffordGlide (s : PlanePoint × Cl55) : PlanePoint × Cl55 :=
  (halfShiftGlide s.1, partialReflectionAlg s.2)

theorem scaleBase_halfCliffordGlide (s : PlanePoint × Cl55) :
    scaleBase (halfCliffordGlide s) = totalCliffordGlide (scaleBase s) :=
  Prod.ext (halfShiftScale_glide s.1) rfl

theorem halfCliffordGlide_sq (s : PlanePoint × Cl55) :
    halfCliffordGlide (halfCliffordGlide s) = ((s.1.1, s.1.2 + 1), s.2) := by
  simp only [halfCliffordGlide, halfShiftGlide_sq, partialReflectionAlg_involutive]

/-- The associated sign channel changes sign under one glide's fiber action. -/
theorem partialReflectionAlg_infinity_difference :
    partialReflectionAlg (infinityClifford55 - originClifford55) =
      -(infinityClifford55 - originClifford55) := by
  simp only [map_sub, partialReflectionAlg_infinity, partialReflectionAlg_origin, neg_sub]

/-- The sign channel is nonzero on the actual native generator carrier. -/
theorem infinity_difference_ne_zero : infinityClifford55 - originClifford55 ≠ 0 := by
  intro hz
  have heq : infinityClifford55 = originClifford55 := sub_eq_zero.mp hz
  have hv : infinityVector55 = originVector55 := ι55_injective heq
  have hc := congrArg (fun v : V55 => v.2 4) hv
  norm_num [infinityVector55, originVector55, n_bar_vec, n_vec,
    nbar_pair, n_pair, e_pos, f_neg] at hc

/-- The complementary sum channel is invariant under the same fiber action. -/
theorem partialReflectionAlg_infinity_sum :
    partialReflectionAlg (infinityClifford55 + originClifford55) =
      infinityClifford55 + originClifford55 := by
  rw [map_add, partialReflectionAlg_infinity, partialReflectionAlg_origin, add_comm]

/-- Exchanging the native Witt endpoints reverses their occupation grading. -/
theorem partialReflectionAlg_infinityGrading55 :
    partialReflectionAlg infinityGrading55 = -infinityGrading55 := by
  simp only [infinityGrading55, infinityProjector55, originProjector55,
    map_sub, map_mul, partialReflectionAlg_infinity, partialReflectionAlg_origin, neg_sub]

/-- The translated fiber action retains the exact native Plücker intertwiner. -/
theorem totalCliffordGlide_plucker (p : PlanePoint) (z w : TwistorSpace) :
    totalCliffordGlide (p, ι55 (pluckerToV55 (twistorPlucker z w))) =
      (deckB p, ι55 (pluckerToV55
        (twistorPlucker (blockRotation z) (blockRotation w)))) := by
  simp only [totalCliffordGlide, native_reflection_intertwiner,
    twistorPlucker_blockRotation]

end InfoGeometry.Twistor.RealTwistorGlideHolonomy
