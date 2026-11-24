/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.FenchelContactIncidence
import InfoGeometry.Convex.TransportedFenchel
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Moving Fenchel contact cuts and their Peirce superderivation

The homogeneous point determines a genuine idempotent in the full real
endomorphism algebra. Its Peirce reflection squares to one. At Fenchel
contact the nonzero incidence dyad is odd, and its twisted commutator is a
nonzero, square-zero linear endomorphism satisfying the graded Leibniz law.
The nilpotency and Leibniz identities instantiate the existing Peirce owner.

Continuous linear changes of primal coordinates lift to homogeneous linear
frames, with the covector transported contragrediently. The actual Fenchel
conjugate transports by the existing support-set theorem. Projectors, dyads,
reflections, and superderivations transform by native algebra conjugation.

An explicit Mathlib transvection sends the reference homogeneous point
`(0, 0, 1)` to `(x, f x, 1)`. This constructs the change from the reference
cut to the moving contact cut. It does not identify these cuts with an
independent Zorn grading, assert star self-adjointness, or introduce dynamics.
-/

noncomputable section

namespace InfoGeometry.Twistor.FenchelContactIncidence

open InfoGeometry.Twistor.RealDualTwistor
open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## The actual contact cut and odd operator -/

/-- The Peirce reflection belonging to the homogeneous contact projector. -/
def contactGrading (f : E → ℝ) (x : E) : Module.End ℝ (E × (ℝ × ℝ)) :=
  invS (contactProjector f x)

theorem contactGrading_eq_two_mul_sub_one (f : E → ℝ) (x : E) :
    contactGrading f x = 2 * contactProjector f x - 1 := by
  unfold contactGrading invS
  noncomm_ring

theorem contactGrading_sq (f : E → ℝ) (x : E) :
    contactGrading f x * contactGrading f x = 1 := by
  have hP := contactProjector_sq f x
  unfold contactGrading invS
  noncomm_ring [hP]

theorem contactDyad_eq_conePlus (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    conePlus (contactProjector f x) (dyad (contactPair f fStar x p)) =
      dyad (contactPair f fStar x p) :=
  dyad_contactProjector_corner_of_equality f fStar x p heq

/-- The contact dyad has left parity `+1`, right parity `-1`, and is odd
under conjugation by the actual moving reflection. -/
theorem contactDyad_grading (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    contactGrading f x * dyad (contactPair f fStar x p) =
        dyad (contactPair f fStar x p) ∧
      dyad (contactPair f fStar x p) * contactGrading f x =
        -dyad (contactPair f fStar x p) ∧
      parityConj (contactProjector f x) (dyad (contactPair f fStar x p)) =
        -dyad (contactPair f fStar x p) := by
  have h := archetype_A27_grading_parities (contactProjector_sq f x)
    (dyad (contactPair f fStar x p)) (0 : Module.End ℝ (E × (ℝ × ℝ)))
  have hcorner := contactDyad_eq_conePlus f fStar x p heq
  have hleft : contactGrading f x * dyad (contactPair f fStar x p) =
      dyad (contactPair f fStar x p) := by
    simpa only [hcorner, contactGrading] using h.1
  have hright : dyad (contactPair f fStar x p) * contactGrading f x =
      -dyad (contactPair f fStar x p) := by
    simpa only [hcorner, contactGrading] using h.2.1
  refine ⟨hleft, hright, ?_⟩
  change contactGrading f x * dyad (contactPair f fStar x p) *
      contactGrading f x = -dyad (contactPair f fStar x p)
  rw [hleft, hright]

theorem contactDyad_anticommutes_grading (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    contactGrading f x * dyad (contactPair f fStar x p) +
        dyad (contactPair f fStar x p) * contactGrading f x = 0 := by
  have h := contactDyad_grading f fStar x p heq
  rw [h.1, h.2.1]
  exact add_neg_cancel _

/-- The twisted commutator on the full noncommutative endomorphism algebra,
bundled as a native real linear endomorphism. -/
def contactSuperDerivation (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ) :
    Module.End ℝ (Module.End ℝ (E × (ℝ × ℝ))) where
  toFun A := dyad (contactPair f fStar x p) * A -
    parityConj (contactProjector f x) A * dyad (contactPair f fStar x p)
  map_add' A B := by
    unfold parityConj
    noncomm_ring
  map_smul' r A := by
    simp only [RingHom.id_apply, parityConj, mul_smul_comm, smul_mul_assoc, smul_sub]

@[simp] theorem contactSuperDerivation_apply (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (A : Module.End ℝ (E × (ℝ × ℝ))) :
    contactSuperDerivation f fStar x p A =
      dyad (contactPair f fStar x p) * A -
        parityConj (contactProjector f x) A * dyad (contactPair f fStar x p) := rfl

/-- At contact this is exactly the existing upper-corner superderivation. -/
theorem contactSuperDerivation_eq_superDerivPlus (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p)
    (A : Module.End ℝ (E × (ℝ × ℝ))) :
    contactSuperDerivation f fStar x p A =
      superDerivPlus (contactProjector f x) (dyad (contactPair f fStar x p)) A := by
  rw [contactSuperDerivation_apply, superDerivPlus,
    contactDyad_eq_conePlus f fStar x p heq]

/-- Nilpotency in the native endomorphism algebra of the operator algebra. -/
theorem contactSuperDerivation_sq (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    contactSuperDerivation f fStar x p * contactSuperDerivation f fStar x p = 0 := by
  apply LinearMap.ext
  intro A
  change contactSuperDerivation f fStar x p
    (contactSuperDerivation f fStar x p A) = 0
  have h := (archetype_A28_graded_derivations (contactProjector_sq f x)
    (dyad (contactPair f fStar x p)) (0 : Module.End ℝ (E × (ℝ × ℝ)))
    A (0 : Module.End ℝ (E × (ℝ × ℝ)))).1
  simpa only [contactSuperDerivation_eq_superDerivPlus f fStar x p heq] using h

theorem contactSuperDerivation_leibniz (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p)
    (A B : Module.End ℝ (E × (ℝ × ℝ))) :
    contactSuperDerivation f fStar x p (A * B) =
      contactSuperDerivation f fStar x p A * B +
        parityConj (contactProjector f x) A * contactSuperDerivation f fStar x p B := by
  have h := (archetype_A28_graded_derivations (contactProjector_sq f x)
    (dyad (contactPair f fStar x p)) (0 : Module.End ℝ (E × (ℝ × ℝ))) A B).2.2.2.2.1
  simpa only [contactSuperDerivation_eq_superDerivPlus f fStar x p heq] using h

theorem contactSuperDerivation_projector (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    contactSuperDerivation f fStar x p (contactProjector f x) =
      -dyad (contactPair f fStar x p) := by
  have hP := contactProjector_sq f x
  have hpar : parityConj (contactProjector f x) (contactProjector f x) =
      contactProjector f x := by
    unfold parityConj invS
    noncomm_ring [hP]
  have hgap := (Geometry.fenchelYoungEquality_iff_gap_eq_zero f fStar x p).1 heq
  rw [contactSuperDerivation_apply, hpar, dyad_mul_contactProjector,
    contactProjector_mul_dyad, hgap]
  simp

/-- The square-zero superderivation is nonzero: its value on the projector
is the negative of the already nonzero contact dyad. -/
theorem contactSuperDerivation_ne_zero (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    contactSuperDerivation f fStar x p ≠ 0 := by
  intro hzero
  have h := LinearMap.congr_fun hzero (contactProjector f x)
  rw [contactSuperDerivation_projector f fStar x p heq] at h
  have hD : dyad (contactPair f fStar x p) = 0 := neg_eq_zero.mp (by simpa using h)
  exact dyad_contactPair_ne_zero f fStar x p hD

/-- For an actual derivative of a globally convex potential, the preceding
nonzero nilpotent operator is obtained without assuming Fenchel contact. -/
theorem contactSuperDerivation_fenchel_sq_and_ne_zero_of_hasFDerivAt
    (f : E → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (hconv : ConvexOn ℝ Set.univ f) (hd : HasFDerivAt f p x) :
    contactSuperDerivation f (Convex.fenchelConj f) x p *
        contactSuperDerivation f (Convex.fenchelConj f) x p = 0 ∧
      contactSuperDerivation f (Convex.fenchelConj f) x p ≠ 0 := by
  have heq := (dyad_contactPair_sq_zero_iff f (Convex.fenchelConj f) x p).1
    (dyad_fenchel_sq_zero_of_hasFDerivAt f x p hconv hd)
  exact ⟨contactSuperDerivation_sq f (Convex.fenchelConj f) x p heq,
    contactSuperDerivation_ne_zero f (Convex.fenchelConj f) x p heq⟩

/-! ## Conjugation of the point-normalized cut -/

/-- A homogeneous frame transports the canonical projector whenever it
transports the point and preserves the final-coordinate normalization. -/
theorem contactProjector_conjugate (f : E → ℝ) (g : F → ℝ)
    (x : E) (y : F) (e : (E × (ℝ × ℝ)) ≃ₗ[ℝ] (F × (ℝ × ℝ)))
    (hpoint : e (homogeneousPoint f x) = homogeneousPoint g y)
    (hcoord : (homogeneousCoordinate (E := E)).comp e.symm.toLinearMap =
      homogeneousCoordinate (E := F)) :
    contactProjector g y = e.conjAlgEquiv ℝ (contactProjector f x) := by
  have hpair : frameAction e (homogeneousPoint f x, homogeneousCoordinate) =
      (homogeneousPoint g y, homogeneousCoordinate) := by
    apply Prod.ext
    · exact hpoint
    · exact hcoord
  have h := dyad_frameAction e (homogeneousPoint f x, homogeneousCoordinate)
  rw [hpair] at h
  simpa only [contactProjector, LinearEquiv.conjAlgEquiv_apply,
    LinearMap.comp_assoc] using h

theorem contactGrading_conjugate (f : E → ℝ) (g : F → ℝ)
    (x : E) (y : F) (e : (E × (ℝ × ℝ)) ≃ₗ[ℝ] (F × (ℝ × ℝ)))
    (hpoint : e (homogeneousPoint f x) = homogeneousPoint g y)
    (hcoord : (homogeneousCoordinate (E := E)).comp e.symm.toLinearMap =
      homogeneousCoordinate (E := F)) :
    contactGrading g y = e.conjAlgEquiv ℝ (contactGrading f x) := by
  have hP := contactProjector_conjugate f g x y e hpoint hcoord
  simp only [contactGrading, invS, map_sub, map_one, ← hP]

/-! ## Linear primal frames and the actual Fenchel conjugate -/

/-- A primal frame extended by the identity on height and homogenization. -/
def homogeneousFrame (e : E ≃ₗ[ℝ] F) :
    (E × (ℝ × ℝ)) ≃ₗ[ℝ] (F × (ℝ × ℝ)) :=
  e.prodCongr (LinearEquiv.refl ℝ (ℝ × ℝ))

@[simp] theorem homogeneousFrame_apply (e : E ≃ₗ[ℝ] F)
    (z : E × (ℝ × ℝ)) : homogeneousFrame e z = (e z.1, z.2) := rfl

@[simp] theorem homogeneousFrame_symm_apply (e : E ≃ₗ[ℝ] F)
    (z : F × (ℝ × ℝ)) : (homogeneousFrame e).symm z = (e.symm z.1, z.2) := rfl

theorem homogeneousFrame_coordinate (e : E ≃ₗ[ℝ] F) :
    (homogeneousCoordinate (E := E)).comp (homogeneousFrame e).symm.toLinearMap =
      homogeneousCoordinate (E := F) := by
  apply LinearMap.ext
  intro z
  rfl

/-- The same primal potential in the new frame. -/
def framePotential (e : E ≃L[ℝ] F) (f : E → ℝ) : F → ℝ :=
  fun y => f (e.symm y)

/-- Dual coordinates transform by the pullback of the primal frame. -/
def frameDualPotential (e : E ≃L[ℝ] F)
    (fStar : (E →L[ℝ] ℝ) → ℝ) : (F →L[ℝ] ℝ) → ℝ :=
  fun q => fStar (Convex.dualTransport e q)

theorem dualTransport_frame_inverse (e : E ≃L[ℝ] F) (p : E →L[ℝ] ℝ) :
    Convex.dualTransport e (Convex.dualTransport e.symm p) = p := by
  ext x
  simp [Convex.dualTransport]

theorem dualTransport_inverse_frame (e : E ≃L[ℝ] F) (q : F →L[ℝ] ℝ) :
    Convex.dualTransport e.symm (Convex.dualTransport e q) = q := by
  ext y
  simp [Convex.dualTransport]

/-- Transport is proved for the defining supremum, without a postulated
conjugacy equality or additional boundedness premise. -/
theorem fenchelConj_framePotential (e : E ≃L[ℝ] F) (f : E → ℝ)
    (q : F →L[ℝ] ℝ) :
    Convex.fenchelConj (framePotential e f) q =
      frameDualPotential e (Convex.fenchelConj f) q := by
  change sSup (Convex.fenchelSet (fun y => f (e.symm y)) q) =
    Convex.fenchelConj f (Convex.dualTransport e q)
  have h := Convex.transportedFenchelConjFromDual_eq f e.symm
    (Convex.dualTransport e q)
  simpa only [Convex.transportedFenchelSetFromDual,
    dualTransport_inverse_frame e q] using h

theorem homogeneousFrame_point (e : E ≃L[ℝ] F) (f : E → ℝ) (x : E) :
    homogeneousFrame e.toLinearEquiv (homogeneousPoint f x) =
      homogeneousPoint (framePotential e f) (e x) := by
  simp [homogeneousPoint, framePotential]

theorem contactPair_frameAction (e : E ≃L[ℝ] F) (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ) :
    frameAction (homogeneousFrame e.toLinearEquiv) (contactPair f fStar x p) =
      contactPair (framePotential e f) (frameDualPotential e fStar)
        (e x) (Convex.dualTransport e.symm p) := by
  apply Prod.ext
  · exact homogeneousFrame_point e f x
  · apply LinearMap.ext
    intro z
    change p (e.symm z.1) - z.2.1 - fStar p * z.2.2 =
      p (e.symm z.1) - z.2.1 -
        fStar (Convex.dualTransport e (Convex.dualTransport e.symm p)) * z.2.2
    rw [dualTransport_frame_inverse]

theorem contactProjector_frame (e : E ≃L[ℝ] F) (f : E → ℝ) (x : E) :
    contactProjector (framePotential e f) (e x) =
      (homogeneousFrame e.toLinearEquiv).conjAlgEquiv ℝ (contactProjector f x) :=
  contactProjector_conjugate f (framePotential e f) x (e x)
    (homogeneousFrame e.toLinearEquiv) (homogeneousFrame_point e f x)
    (homogeneousFrame_coordinate e.toLinearEquiv)

theorem contactGrading_frame (e : E ≃L[ℝ] F) (f : E → ℝ) (x : E) :
    contactGrading (framePotential e f) (e x) =
      (homogeneousFrame e.toLinearEquiv).conjAlgEquiv ℝ (contactGrading f x) :=
  contactGrading_conjugate f (framePotential e f) x (e x)
    (homogeneousFrame e.toLinearEquiv) (homogeneousFrame_point e f x)
    (homogeneousFrame_coordinate e.toLinearEquiv)

theorem contactDyad_frame (e : E ≃L[ℝ] F) (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ) :
    dyad (contactPair (framePotential e f) (frameDualPotential e fStar)
      (e x) (Convex.dualTransport e.symm p)) =
        (homogeneousFrame e.toLinearEquiv).conjAlgEquiv ℝ
          (dyad (contactPair f fStar x p)) := by
  have h := dyad_frameAction (homogeneousFrame e.toLinearEquiv) (contactPair f fStar x p)
  rw [contactPair_frameAction] at h
  simpa only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_assoc] using h

theorem contactSuperDerivation_frame (e : E ≃L[ℝ] F) (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (A : Module.End ℝ (E × (ℝ × ℝ))) :
    contactSuperDerivation (framePotential e f) (frameDualPotential e fStar)
        (e x) (Convex.dualTransport e.symm p)
        ((homogeneousFrame e.toLinearEquiv).conjAlgEquiv ℝ A) =
      (homogeneousFrame e.toLinearEquiv).conjAlgEquiv ℝ
        (contactSuperDerivation f fStar x p A) := by
  rw [contactSuperDerivation_apply, contactSuperDerivation_apply,
    contactDyad_frame, contactProjector_frame]
  simp only [parityConj, invS, map_sub, map_one, map_mul]

/-! ## Explicit shear from the reference cut -/

/-- A Mathlib transvection preserving the final homogeneous coordinate. -/
def contactChartShear (f : E → ℝ) (x : E) :
    (E × (ℝ × ℝ)) ≃ₗ[ℝ] (E × (ℝ × ℝ)) :=
  LinearEquiv.transvection
    (f := homogeneousCoordinate) (v := (x, f x, 0)) (by rfl)

@[simp] theorem contactChartShear_apply (f : E → ℝ) (x : E)
    (z : E × (ℝ × ℝ)) :
    contactChartShear f x z =
      (z.1 + z.2.2 • x, z.2.1 + z.2.2 * f x, z.2.2) := by
  change z + z.2.2 • (x, f x, 0) = _
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simp

@[simp] theorem contactChartShear_symm_apply (f : E → ℝ) (x : E)
    (z : E × (ℝ × ℝ)) :
    (contactChartShear f x).symm z =
      (z.1 - z.2.2 • x, z.2.1 - z.2.2 * f x, z.2.2) := by
  change z + z.2.2 • (-(x, f x, 0)) = _
  apply Prod.ext
  · simp [sub_eq_add_neg]
  · apply Prod.ext
    · simp [sub_eq_add_neg]
    · simp

theorem contactChartShear_point (f : E → ℝ) (x : E) :
    contactChartShear f x (homogeneousPoint (fun _ : E => 0) 0) =
      homogeneousPoint f x := by
  simp [homogeneousPoint]

theorem contactChartShear_coordinate (f : E → ℝ) (x : E) :
    homogeneousCoordinate.comp (contactChartShear f x).symm.toLinearMap =
      homogeneousCoordinate := by
  apply LinearMap.ext
  intro z
  change ((contactChartShear f x).symm z).2.2 = z.2.2
  rw [contactChartShear_symm_apply]

theorem contactProjector_shear (f : E → ℝ) (x : E) :
    contactProjector f x = (contactChartShear f x).conjAlgEquiv ℝ
      (contactProjector (fun _ : E => 0) 0) :=
  contactProjector_conjugate (fun _ : E => 0) f 0 x (contactChartShear f x)
    (contactChartShear_point f x) (contactChartShear_coordinate f x)

theorem contactGrading_shear (f : E → ℝ) (x : E) :
    contactGrading f x = (contactChartShear f x).conjAlgEquiv ℝ
      (contactGrading (fun _ : E => 0) 0) :=
  contactGrading_conjugate (fun _ : E => 0) f 0 x (contactChartShear f x)
    (contactChartShear_point f x) (contactChartShear_coordinate f x)

/-- Contact removes precisely the final-coordinate defect in the covector
after transporting from the reference chart. -/
theorem contactPair_shear_of_equality (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    frameAction (contactChartShear f x)
        (contactPair (fun _ : E => 0) (fun _ => 0) 0 p) =
      contactPair f fStar x p := by
  apply Prod.ext
  · exact contactChartShear_point f x
  · apply LinearMap.ext
    intro z
    change hyperplaneCovector p 0 ((contactChartShear f x).symm z) =
      hyperplaneCovector p (fStar p) z
    rw [contactChartShear_symm_apply]
    simp only [hyperplaneCovector_apply, map_sub, map_smul, smul_eq_mul, zero_mul,
      sub_zero]
    have hc : fStar p = p x - f x := by
      change f x + fStar p = p x at heq
      linarith
    rw [hc]
    ring

theorem contactDyad_shear_of_equality (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p) :
    dyad (contactPair f fStar x p) = (contactChartShear f x).conjAlgEquiv ℝ
      (dyad (contactPair (fun _ : E => 0) (fun _ => 0) 0 p)) := by
  have h := dyad_frameAction (contactChartShear f x)
    (contactPair (fun _ : E => 0) (fun _ => 0) 0 p)
  rw [contactPair_shear_of_equality f fStar x p heq] at h
  simpa only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_assoc] using h

theorem contactSuperDerivation_shear_of_equality (f : E → ℝ)
    (fStar : (E →L[ℝ] ℝ) → ℝ) (x : E) (p : E →L[ℝ] ℝ)
    (heq : Geometry.FenchelYoungEquality f fStar x p)
    (A : Module.End ℝ (E × (ℝ × ℝ))) :
    contactSuperDerivation f fStar x p
        ((contactChartShear f x).conjAlgEquiv ℝ A) =
      (contactChartShear f x).conjAlgEquiv ℝ
        (contactSuperDerivation (fun _ : E => 0) (fun _ => 0) 0 p A) := by
  rw [contactSuperDerivation_apply, contactSuperDerivation_apply,
    contactDyad_shear_of_equality f fStar x p heq, contactProjector_shear]
  simp only [parityConj, invS, map_sub, map_one, map_mul]

end InfoGeometry.Twistor.FenchelContactIncidence
