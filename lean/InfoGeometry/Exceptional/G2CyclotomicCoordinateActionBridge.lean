/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CyclotomicWeylBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Exceptional.G2ArtinPresentation

/-!
# Cyclotomic Weyl action transported to the coordinate-root carrier

The cyclotomic `Root` action is the authoritative finite dihedral action.
This file transports it across the existing signed-coordinate equivalence;
it does not introduce a second Weyl group or enumerate the twelve roots.
-/

namespace InfoGeometry.Exceptional.G2CyclotomicCoordinateActionBridge

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Exceptional.G2ArtinPresentation

noncomputable def transportRootPerm
    (p : Equiv.Perm Root) : Equiv.Perm G2CoordinateRoot :=
  signedRootCyclotomicEquiv.trans (p.trans signedRootCyclotomicEquiv.symm)

theorem transportRootPerm_mul (p q : Equiv.Perm Root) :
    transportRootPerm (p * q) =
      transportRootPerm p * transportRootPerm q := by
  apply Equiv.ext
  intro x
  simp [transportRootPerm, Equiv.trans_apply]

/-! Package the conjugation transport as the homomorphism it already is.
    Keeping this wrapper here makes subsequent comparisons of finite actions
    extensional at the `MonoidHom` level. -/

noncomputable def transportRootPermHom :
    Equiv.Perm Root →* Equiv.Perm G2CoordinateRoot where
  toFun := transportRootPerm
  map_one' := by
    apply Equiv.ext
    intro x
    simp [transportRootPerm]
  map_mul' p q := transportRootPerm_mul p q

theorem transportRootPerm_cyclotomicS1 :
    transportRootPerm cyclotomicS1Perm = s1Root := by
  apply Equiv.ext
  intro x
  apply signedRootCyclotomicEquiv.injective
  simp [transportRootPerm, Equiv.trans_apply, signedRootCyclotomicEquiv_s1]

theorem transportRootPerm_cyclotomicS2 :
    transportRootPerm cyclotomicS2Perm = s2Root := by
  apply Equiv.ext
  intro x
  apply signedRootCyclotomicEquiv.injective
  simp [transportRootPerm, Equiv.trans_apply, signedRootCyclotomicEquiv_s2]

/-! The calibrated reflection `cyclotomicS1Perm` is not the default
    `DihedralGroup` reflection `sr 0`: its two sectors use different axes.
    This obstruction records the convention mismatch explicitly, rather than
    silently identifying the two actions. -/

theorem cyclotomicS1Perm_ne_dihedral_sr_zero :
    cyclotomicS1Perm ≠ dihedralRootPermutationRep (DihedralGroup.sr 0) := by
  intro h
  have hx := congrArg (fun p : Equiv.Perm Root => p (false, (0 : ZMod 6))) h
  change (false, (3 : ZMod 6)) = (false, (0 : ZMod 6)) at hx
  exact (by decide : ¬ ((3 : ZMod 6) = 0)) (congrArg Prod.snd hx)

theorem coordinateAction_sigmaZero_eq_transport_cyclotomicS1 :
    coordinateAction G2ArtinPresentation.sigmaZero =
      transportRootPerm cyclotomicS1Perm := by
  rw [coordinateAction_sigmaZero, transportRootPerm_cyclotomicS1]

theorem coordinateAction_sigmaOne_eq_transport_cyclotomicS2 :
    coordinateAction G2ArtinPresentation.sigmaOne =
      transportRootPerm cyclotomicS2Perm := by
  rw [coordinateAction_sigmaOne, transportRootPerm_cyclotomicS2]

noncomputable def dihedralCoordinateAction :
    DihedralGroup 6 →* Equiv.Perm G2CoordinateRoot where
  toFun g := transportRootPerm
    (dihedralRootPermutationRep g)
  map_one' := by
    apply Equiv.ext
    intro x
    simp [transportRootPerm]
  map_mul' := by
    intro g h
    simp only [dihedralRootPermutationRep.map_mul]
    exact transportRootPerm_mul _ _

theorem dihedralCoordinateAction_apply (g : DihedralGroup 6)
    (x : G2CoordinateRoot) :
    dihedralCoordinateAction g x =
      signedRootCyclotomicEquiv.symm
        (dihedralRootPermutationRep g (signedRootCyclotomicEquiv x)) := by
  rfl

end InfoGeometry.Exceptional.G2CyclotomicCoordinateActionBridge
