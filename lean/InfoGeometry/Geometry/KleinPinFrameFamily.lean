/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FreedKleinRepresentation
import InfoGeometry.Clifford.FreedPinRepresentation
import InfoGeometry.Geometry.KleinPinGradedDirac

/-!
# Concrete Klein Pin frame families

A constant Pin frame acts simultaneously on the spinor representation, the
actual deck monodromy, the smooth equivariant domain, and the differential
coefficients. The resulting geometric operator is proved to intertwine the
original operator by the real Fréchet chain rule. The associated quotient and
the doubled sector grading are transported explicitly.

The family of normalized source vectors `(cos t, sin t)` gives actual elements
of PR338's normalized Pin subgroup. Its matrix action is
`cos t • gammaX + sin t • gammaY`; parameter smoothness is derived from this
formula. At two parameter values these represented frames do not commute.

Parameter smoothness below concerns the evaluated smooth fields and their
Dirac images in the displayed domain identifications. No Hilbert completion,
operator-norm topology on unbounded operators, or Fredholm seed is asserted.
The transported deck representation is necessary: arbitrary fibre Pin frames
are not asserted to preserve a fixed Klein boundary condition.
-/

noncomputable section

namespace InfoGeometry.Geometry.KleinPinFrameFamily

open InfoGeometry.Topology.KleinQuotientDeckInvariants
open InfoGeometry.Topology.KleinDeckRepresentation
open InfoGeometry.Topology.KleinCliffordPinLift
open InfoGeometry.Topology.KleinAssociatedSpinors
open InfoGeometry.Geometry.KleinPinDirac
open InfoGeometry.Clifford.NormalizedVectorPin
open InfoGeometry.Clifford.FreedPinRepresentation
open scoped Matrix ContDiff

/-- Actual invertible matrices act on the existing complex spinor fibre. -/
def unitFrame (a : Matˣ) : Spinor ≃ₗ[ℂ] Spinor where
  toFun := a.val.mulVec
  invFun := a.inv.mulVec
  left_inv s := by
    rw [Matrix.mulVec_mulVec, Units.inv_val, Matrix.one_mulVec]
  right_inv s := by
    rw [Matrix.mulVec_mulVec, Units.val_inv, Matrix.one_mulVec]
  map_add' s t := Matrix.mulVec_add _ _ _
  map_smul' r s := Matrix.mulVec_smul _ _ _

/-- Ordered multiplication is retained by the actual spinor action. -/
def unitFrameHom : Matˣ →* (Spinor ≃ₗ[ℂ] Spinor) where
  toFun := unitFrame
  map_one' := by ext s; simp [unitFrame]
  map_mul' a b := by
    apply LinearEquiv.ext
    intro s
    change (a.val * b.val).mulVec s = a.val.mulVec (b.val.mulVec s)
    exact (Matrix.mulVec_mulVec s a.val b.val).symm

/-- The concrete source action of the particular normalized Pin construction. -/
def pinFrame : pin positiveForm →* (Spinor ≃ₗ[ℂ] Spinor) :=
  unitFrameHom.comp (pinRepresentation positiveForm
    InfoGeometry.Topology.KleinCliffordPinLift.positiveRepresentation)

@[simp] theorem pinFrame_apply (g : pin positiveForm) (s : Spinor) :
    pinFrame g s =
      (InfoGeometry.Topology.KleinCliffordPinLift.positiveRepresentation
        ((g : (CliffordAlgebra positiveForm)ˣ) : CliffordAlgebra positiveForm)).mulVec s := rfl

/-- This action equals the represented ordered positive suspension for every
actual Pin element, rather than only for a chosen matrix generator. -/
theorem pinFrame_eq_suspended (g : pin positiveForm) (s : Spinor) :
    pinFrame g s =
      (Units.map InfoGeometry.Clifford.FreedKleinRepresentation.representation.toMonoidHom
        (evenPinToUnits InfoGeometry.Clifford.FreedKleinRepresentation.targetForm
          (positivePinHom positiveForm g))).val.mulVec s := by
  rw [InfoGeometry.Clifford.FreedKleinRepresentation.positivePinHom_representation]
  rfl

/-- A frame changes the actual deck representation by ordered conjugation. -/
def conjugateMonodromy (U : Spinor ≃ₗ[ℂ] Spinor)
    (ρ : KleinDeckGroup →* (Spinor ≃ₗ[ℂ] Spinor)) :
    KleinDeckGroup →* (Spinor ≃ₗ[ℂ] Spinor) where
  toFun g := U * ρ g * U⁻¹
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

@[simp] theorem conjugateMonodromy_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (ρ : KleinDeckGroup →* (Spinor ≃ₗ[ℂ] Spinor))
    (g : KleinDeckGroup) (s : Spinor) :
    conjugateMonodromy U ρ g s = U (ρ g (U.symm s)) := rfl

/-- Successive frame changes retain their noncommutative order. -/
theorem conjugateMonodromy_mul (U V : Spinor ≃ₗ[ℂ] Spinor)
    (ρ : KleinDeckGroup →* (Spinor ≃ₗ[ℂ] Spinor)) :
    conjugateMonodromy (U * V) ρ =
      conjugateMonodromy U (conjugateMonodromy V ρ) := by
  ext g s
  simp [conjugateMonodromy, mul_assoc]

abbrev framedMonodromy (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :=
  conjugateMonodromy U (monodromy sector)

/-- Finite-dimensionality supplies continuity of this specified fibre map. -/
def realFrame (U : Spinor ≃ₗ[ℂ] Spinor) : Spinor ≃L[ℝ] Spinor :=
  (U.restrictScalars ℝ).toContinuousLinearEquiv

@[simp] theorem realFrame_apply (U : Spinor ≃ₗ[ℂ] Spinor) (s : Spinor) :
    realFrame U s = U s := rfl

@[simp] theorem realFrame_symm_apply (U : Spinor ≃ₗ[ℂ] Spinor) (s : Spinor) :
    (realFrame U).symm s = U.symm s := rfl

@[simp] theorem realFrame_clm_apply (U : Spinor ≃ₗ[ℂ] Spinor) (s : Spinor) :
    (realFrame U : Spinor →L[ℝ] Spinor) s = U s := rfl

/-- Forward transport satisfies the conjugated deck law by construction. -/
def frameSection (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool)
    (ψ : equivariantSections (monodromy sector)) :
    equivariantSections (framedMonodromy U sector) :=
  ⟨fun p => U (ψ.val p), by
    intro g p
    change U (ψ.val (deckAction g p)) = U (monodromy sector g (U.symm (U (ψ.val p))))
    rw [ψ.property g p, U.symm_apply_apply]⟩

/-- The inverse frame really returns a section with the original deck law. -/
def unframeSection (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool)
    (ψ : equivariantSections (framedMonodromy U sector)) :
    equivariantSections (monodromy sector) :=
  ⟨fun p => U.symm (ψ.val p), by
    intro g p
    have h := congrArg U.symm (ψ.property g p)
    simpa only [framedMonodromy, conjugateMonodromy_apply,
      U.symm_apply_apply] using h⟩

/-- The transported smooth domain is an actual submodule of actual
conjugate-equivariant fields. -/
def framedSmoothSections (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    Submodule ℝ (equivariantSections (framedMonodromy U sector)) where
  carrier := {ψ | ContDiff ℝ ∞ (ψ : PlanePoint → Spinor)}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : PlanePoint => (0 : Spinor))
    exact contDiff_const
  add_mem' := by
    intro ψ χ hψ hχ
    change ContDiff ℝ ∞ (ψ : PlanePoint → Spinor) at hψ
    change ContDiff ℝ ∞ (χ : PlanePoint → Spinor) at hχ
    change ContDiff ℝ ∞ ((ψ : PlanePoint → Spinor) + (χ : PlanePoint → Spinor))
    exact hψ.add hχ
  smul_mem' := by
    intro r ψ hψ
    change ContDiff ℝ ∞ (ψ : PlanePoint → Spinor) at hψ
    change ContDiff ℝ ∞ (r • (ψ : PlanePoint → Spinor))
    exact hψ.const_smul r

instance framedSmoothSectionsAddCommGroup (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    AddCommGroup (framedSmoothSections U sector) := by
  letI := Submodule.addCommGroup (equivariantSections (framedMonodromy U sector))
  exact Submodule.addCommGroup (framedSmoothSections U sector)

/-- The smooth-domain equivalence has explicit pointwise inverse and proves
smoothness in both directions from the actual bounded fibre maps. -/
def frameSmoothEquiv (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    smoothSections sector ≃ₗ[ℝ] framedSmoothSections U sector where
  toFun ψ := ⟨frameSection U sector ψ.val, by
    change ContDiff ℝ ∞ (fun p => U (ψ.val.val p))
    have hd := (realFrame U).contDiff.comp (smoothSection_contDiff sector ψ)
    refine contDiffOn_univ.mp (hd.contDiffOn.congr ?_)
    intro p _
    rfl⟩
  invFun ψ := ⟨unframeSection U sector ψ.val, by
    have hψ : ContDiff ℝ ∞ (ψ.val : PlanePoint → Spinor) := ψ.property
    change ContDiff ℝ ∞ (fun p => U.symm (ψ.val.val p))
    have hd := (realFrame U).symm.contDiff.comp hψ
    refine contDiffOn_univ.mp (hd.contDiffOn.congr ?_)
    intro p _
    rfl⟩
  left_inv ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact U.symm_apply_apply (ψ.val.val p)
  right_inv ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact U.apply_symm_apply (ψ.val.val p)
  map_add' ψ χ := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact U.map_add (ψ.val.val p) (χ.val.val p)
  map_smul' r ψ := by
    apply Subtype.ext
    apply Subtype.ext
    funext p
    exact (U.restrictScalars ℝ).map_smul r (ψ.val.val p)

@[simp] theorem frameSmoothEquiv_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : smoothSections sector) (p : PlanePoint) :
    (frameSmoothEquiv U sector ψ).val.val p = U (ψ.val.val p) := rfl

@[simp] theorem frameSmoothEquiv_symm_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : framedSmoothSections U sector) (p : PlanePoint) :
    ((frameSmoothEquiv U sector).symm ψ).val.val p = U.symm (ψ.val.val p) := rfl

/-- Expose the transported field without unfolding the domain-equivalence proof. -/
theorem frameSmoothEquiv_field (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : smoothSections sector) :
    ((frameSmoothEquiv U sector ψ).val : PlanePoint → Spinor) =
      fun p => U (ψ.val.val p) := rfl

/-- A further frame `U` maps the domain already framed by `V` to the domain
framed by the ordered product `U * V`. -/
def relativeFrameSmoothEquiv (U V : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    framedSmoothSections V sector ≃ₗ[ℝ] framedSmoothSections (U * V) sector :=
  (frameSmoothEquiv V sector).symm.trans (frameSmoothEquiv (U * V) sector)

@[simp] theorem relativeFrameSmoothEquiv_apply (U V : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : framedSmoothSections V sector) (p : PlanePoint) :
    (relativeFrameSmoothEquiv U V sector ψ).val.val p = U (ψ.val.val p) := by
  change (U * V) (V.symm (ψ.val.val p)) = U (ψ.val.val p)
  simp

/-- The transported differential coefficient is an actual bounded spinor map. -/
def frameCoefficient (U : Spinor ≃ₗ[ℂ] Spinor) (A : Spinor →L[ℝ] Spinor) :
    Spinor →L[ℝ] Spinor :=
  ((realFrame U : Spinor →L[ℝ] Spinor).comp A).comp
    (realFrame U).symm.toContinuousLinearMap

@[simp] theorem frameCoefficient_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (A : Spinor →L[ℝ] Spinor) (s : Spinor) :
    frameCoefficient U A s = U (A (U.symm s)) := rfl

/-- A first-order operator with the conjugated Clifford coefficients. -/
def framedDirac (U : Spinor ≃ₗ[ℂ] Spinor) (ψ : PlanePoint → Spinor)
    (p : PlanePoint) : Spinor :=
  frameCoefficient U gammaX (fderiv ℝ ψ p (1, 0)) +
    frameCoefficient U gammaY (fderiv ℝ ψ p (0, 1))

/-- The intertwining equation follows from the real chain rule for the
specified frame, with no differential compatibility supplied as an input. -/
theorem framedDirac_intertwine (U : Spinor ≃ₗ[ℂ] Spinor)
    (ψ : PlanePoint → Spinor) (hψ : Differentiable ℝ ψ) (p : PlanePoint) :
    framedDirac U (fun x => U (ψ x)) p = U (dirac ψ p) := by
  have hd : fderiv ℝ (fun x => U (ψ x)) p =
      (realFrame U : Spinor →L[ℝ] Spinor).comp (fderiv ℝ ψ p) :=
    ((realFrame U).toContinuousLinearMap.hasFDerivAt.comp p (hψ p).hasFDerivAt).fderiv
  rw [framedDirac, hd]
  simp only [ContinuousLinearMap.comp_apply, realFrame_clm_apply,
    frameCoefficient_apply, U.symm_apply_apply, dirac, map_add]

/-- The framed differential operator has a proved smooth equivariant domain
and codomain, obtained by the explicit domain equivalences. -/
def framedDiracSmoothLinear (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    framedSmoothSections U sector →ₗ[ℝ] framedSmoothSections U (!sector) :=
  (frameSmoothEquiv U (!sector)).toLinearMap.comp
    ((diracSmoothLinear sector).comp (frameSmoothEquiv U sector).symm.toLinearMap)

/-- The transported domain operator evaluates to the displayed first-order
formula on every element of its actual smooth domain. -/
theorem framedDiracSmoothLinear_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : framedSmoothSections U sector) (p : PlanePoint) :
    (framedDiracSmoothLinear U sector ψ).val.val p =
      framedDirac U (ψ.val : PlanePoint → Spinor) p := by
  let χ := (frameSmoothEquiv U sector).symm ψ
  have h := framedDirac_intertwine U (χ.val : PlanePoint → Spinor)
    (smoothSection_differentiable sector χ) p
  have heq : (fun x => U (χ.val.val x)) = (ψ.val : PlanePoint → Spinor) := by
    funext x
    simp only [χ, frameSmoothEquiv_symm_apply, U.apply_symm_apply]
  rw [heq] at h
  exact h.symm

theorem framedDiracSmoothLinear_intertwine (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : smoothSections sector) :
    framedDiracSmoothLinear U sector (frameSmoothEquiv U sector ψ) =
      frameSmoothEquiv U (!sector) (diracSmoothLinear sector ψ) := by
  simp [framedDiracSmoothLinear]

/-- The complete family respects the orientation-twisted deck law. -/
theorem framedDirac_equivariant (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : framedSmoothSections U sector)
    (g : KleinDeckGroup) (p : PlanePoint) :
    framedDirac U (ψ.val : PlanePoint → Spinor) (deckAction g p) =
      framedMonodromy U (!sector) g
        (framedDirac U (ψ.val : PlanePoint → Spinor) p) := by
  rw [← framedDiracSmoothLinear_apply, ← framedDiracSmoothLinear_apply]
  exact (framedDiracSmoothLinear U sector ψ).val.property g p

/-- Ordered frame composition commutes with the actual domain operators. -/
theorem relativeFrameSmoothEquiv_dirac (U V : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : framedSmoothSections V sector) :
    framedDiracSmoothLinear (U * V) sector (relativeFrameSmoothEquiv U V sector ψ) =
      relativeFrameSmoothEquiv U V (!sector) (framedDiracSmoothLinear V sector ψ) := by
  simp [relativeFrameSmoothEquiv, framedDiracSmoothLinear]

/-! ## Transport of the volume-compensated operator -/

/-- The volume is conjugated together with the Dirac coefficients. -/
def framedVolumeAction (U : Spinor ≃ₗ[ℂ] Spinor) : Spinor →L[ℝ] Spinor :=
  frameCoefficient U InfoGeometry.Clifford.FreedKleinRepresentation.volumeAction

theorem framedVolumeAction_intertwine (U : Spinor ≃ₗ[ℂ] Spinor) (s : Spinor) :
    framedVolumeAction U (U s) =
      U (InfoGeometry.Clifford.FreedKleinRepresentation.volumeAction s) := by
  simp [framedVolumeAction, frameCoefficient_apply]

theorem framedVolumeAction_sq (U : Spinor ≃ₗ[ℂ] Spinor) (s : Spinor) :
    framedVolumeAction U (framedVolumeAction U s) = -s := by
  simp only [framedVolumeAction, frameCoefficient_apply, U.symm_apply_apply,
    InfoGeometry.Clifford.FreedKleinRepresentation.volumeAction_sq, map_neg,
    U.apply_symm_apply]

/-- The concrete reduced operator is the transported volume composed with the
transported differential operator; both factors use the same frame. -/
def framedSuspendedDirac (U : Spinor ≃ₗ[ℂ] Spinor)
    (ψ : PlanePoint → Spinor) (p : PlanePoint) : Spinor :=
  framedVolumeAction U (framedDirac U ψ p)

theorem framedSuspendedDirac_intertwine (U : Spinor ≃ₗ[ℂ] Spinor)
    (ψ : PlanePoint → Spinor) (hψ : Differentiable ℝ ψ) (p : PlanePoint) :
    framedSuspendedDirac U (fun x => U (ψ x)) p =
      U (InfoGeometry.Clifford.FreedKleinRepresentation.suspendedDirac ψ p) := by
  rw [framedSuspendedDirac, framedDirac_intertwine U ψ hψ p,
    framedVolumeAction_intertwine,
    InfoGeometry.Clifford.FreedKleinRepresentation.suspendedDirac_eq_volume_dirac]

/-- The reduced operator preserves each actual framed smooth sector. -/
def framedSuspendedDiracSmoothLinear (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    Module.End ℝ (framedSmoothSections U sector) :=
  (frameSmoothEquiv U sector).toLinearMap.comp
    ((InfoGeometry.Clifford.FreedKleinRepresentation.suspendedDiracSmoothLinear sector).comp
      (frameSmoothEquiv U sector).symm.toLinearMap)

theorem framedSuspendedDiracSmoothLinear_intertwine (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : smoothSections sector) :
    framedSuspendedDiracSmoothLinear U sector (frameSmoothEquiv U sector ψ) =
      frameSmoothEquiv U sector
        (InfoGeometry.Clifford.FreedKleinRepresentation.suspendedDiracSmoothLinear sector ψ) := by
  simp [framedSuspendedDiracSmoothLinear]

theorem framedSuspendedDiracSmoothLinear_apply (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : framedSmoothSections U sector) (p : PlanePoint) :
    (framedSuspendedDiracSmoothLinear U sector ψ).val.val p =
      framedSuspendedDirac U (ψ.val : PlanePoint → Spinor) p := by
  let χ := (frameSmoothEquiv U sector).symm ψ
  have h := framedSuspendedDirac_intertwine U (χ.val : PlanePoint → Spinor)
    (smoothSection_differentiable sector χ) p
  have heq : (fun x => U (χ.val.val x)) = (ψ.val : PlanePoint → Spinor) := by
    funext x
    simp only [χ, frameSmoothEquiv_symm_apply, U.apply_symm_apply]
  rw [heq] at h
  exact h.symm

/-- The same ordered domain diagram holds for the volume-compensated operator. -/
theorem relativeFrameSmoothEquiv_suspendedDirac (U V : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : framedSmoothSections V sector) :
    framedSuspendedDiracSmoothLinear (U * V) sector
        (relativeFrameSmoothEquiv U V sector ψ) =
      relativeFrameSmoothEquiv U V sector (framedSuspendedDiracSmoothLinear V sector ψ) := by
  simp [relativeFrameSmoothEquiv, framedSuspendedDiracSmoothLinear]

/-- The pointwise coordinates used by the concrete sector reduction commute
with frame transport precisely when the volume is transported as well. -/
theorem framed_sector_coordinates (U : Spinor ≃ₗ[ℂ] Spinor) (s t : Spinor) :
    (U s, -(framedVolumeAction U (U t))) =
      (U s, U (-InfoGeometry.Clifford.FreedKleinRepresentation.volumeAction t)) := by
  rw [framedVolumeAction_intertwine, map_neg]

/-! ## Associated quotients and doubled grading -/

/-- The fibre frame induces an actual map between the associated quotients. -/
def frameAssociated (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    AssociatedSpace (monodromy sector) → AssociatedSpace (framedMonodromy U sector) :=
  Quotient.map (fun x : PlanePoint × Spinor => (x.1, U x.2)) (by
    intro x y h
    obtain ⟨g, rfl⟩ := h
    refine ⟨g, ?_⟩
    apply Prod.ext
    · rfl
    · change U (monodromy sector g (U.symm (U x.2))) = U (monodromy sector g x.2)
      rw [U.symm_apply_apply])

/-- The inverse fibre frame respects the reverse associated-orbit relation. -/
def unframeAssociated (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    AssociatedSpace (framedMonodromy U sector) → AssociatedSpace (monodromy sector) :=
  Quotient.map (fun x : PlanePoint × Spinor => (x.1, U.symm x.2)) (by
    intro x y h
    obtain ⟨g, rfl⟩ := h
    refine ⟨g, ?_⟩
    apply Prod.ext
    · rfl
    · change monodromy sector g (U.symm x.2) =
        U.symm (U (monodromy sector g (U.symm x.2)))
      rw [U.symm_apply_apply])

/-- The associated quotient transport is an actual equivalence of carriers. -/
def frameAssociatedEquiv (U : Spinor ≃ₗ[ℂ] Spinor) (sector : Bool) :
    AssociatedSpace (monodromy sector) ≃ AssociatedSpace (framedMonodromy U sector) where
  toFun := frameAssociated U sector
  invFun := unframeAssociated U sector
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ (x.1, U.symm (U x.2)) = Quotient.mk _ x
      rw [U.symm_apply_apply]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ (x.1, U (U.symm x.2)) = Quotient.mk _ x
      rw [U.apply_symm_apply]

theorem frameAssociated_projects (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (q : AssociatedSpace (monodromy sector)) :
    bundleProjection (framedMonodromy U sector) (frameAssociated U sector q) =
      bundleProjection (monodromy sector) q := by
  induction q using Quotient.inductionOn
  rfl

/-- The quotient map and the actual equivariant section descent commute. -/
theorem frameAssociated_descendedSection (U : Spinor ≃ₗ[ℂ] Spinor)
    (sector : Bool) (ψ : equivariantSections (monodromy sector)) (q : DeckOrbitBase) :
    frameAssociated U sector (descendedSection (monodromy sector) ψ q) =
      descendedSection (framedMonodromy U sector) (frameSection U sector ψ) q := by
  induction q using Quotient.inductionOn
  rfl

abbrev FramedTotalSections (U : Spinor ≃ₗ[ℂ] Spinor) :=
  framedSmoothSections U false × framedSmoothSections U true

/-- The existing doubled smooth domain is identified with each framed domain. -/
def frameTotalEquiv (U : Spinor ≃ₗ[ℂ] Spinor) :
    TotalSections ≃ₗ[ℝ] FramedTotalSections U :=
  (frameSmoothEquiv U false).prodCongr (frameSmoothEquiv U true)

def framedGrading (U : Spinor ≃ₗ[ℂ] Spinor) : Module.End ℝ (FramedTotalSections U) where
  toFun ψ := (ψ.1, -ψ.2)
  map_add' ψ χ := by apply Prod.ext; rfl; exact neg_add ψ.2 χ.2
  map_smul' r ψ := by apply Prod.ext; rfl; exact (smul_neg r ψ.2).symm

def framedGradedDirac (U : Spinor ≃ₗ[ℂ] Spinor) :
    Module.End ℝ (FramedTotalSections U) where
  toFun ψ := (framedDiracSmoothLinear U true ψ.2, framedDiracSmoothLinear U false ψ.1)
  map_add' ψ χ := by apply Prod.ext <;> simp
  map_smul' r ψ := by apply Prod.ext <;> simp

theorem frameTotalEquiv_grading (U : Spinor ≃ₗ[ℂ] Spinor) (ψ : TotalSections) :
    frameTotalEquiv U (grading ψ) = framedGrading U (frameTotalEquiv U ψ) := by
  apply Prod.ext
  · rfl
  · exact map_neg (frameSmoothEquiv U true) ψ.2

theorem frameTotalEquiv_dirac (U : Spinor ≃ₗ[ℂ] Spinor) (ψ : TotalSections) :
    frameTotalEquiv U (gradedDirac ψ) =
      framedGradedDirac U (frameTotalEquiv U ψ) := by
  apply Prod.ext
  · exact (framedDiracSmoothLinear_intertwine U true ψ.2).symm
  · exact (framedDiracSmoothLinear_intertwine U false ψ.1).symm

theorem framedGrading_sq (U : Spinor ≃ₗ[ℂ] Spinor) :
    framedGrading U * framedGrading U = 1 := by
  apply LinearMap.ext
  intro ψ
  apply Prod.ext
  · rfl
  · exact neg_neg ψ.2

theorem framedGrading_dirac_anticommute (U : Spinor ≃ₗ[ℂ] Spinor) :
    framedGrading U * framedGradedDirac U =
      -(framedGradedDirac U * framedGrading U) := by
  apply LinearMap.ext
  intro ψ
  apply Prod.ext
  · change framedDiracSmoothLinear U true ψ.2 =
      -(framedDiracSmoothLinear U true (-ψ.2))
    rw [map_neg, neg_neg]
  · rfl

/-! ## An explicit smooth family in the particular Pin group -/

/-- A genuinely varying normalized positive vector. -/
def circleVector (t : ℝ) : Tangent := ![Real.cos t, Real.sin t]

theorem circleVector_normalized (t : ℝ) : positiveForm (circleVector t) = 1 := by
  simpa [positiveForm_apply, circleVector, pow_two, add_comm] using Real.sin_sq_add_cos_sq t

/-- Each family parameter gives an element of the actual normalized subgroup. -/
def circlePin (t : ℝ) : pin positiveForm :=
  pinVector positiveForm (circleVector t) (Or.inl (circleVector_normalized t))

/-- The family consists of square-one Pin reflections. -/
theorem circlePin_sq (t : ℝ) : circlePin t * circlePin t = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((circlePin t : (CliffordAlgebra positiveForm)ˣ) : CliffordAlgebra positiveForm) *
    ((circlePin t : (CliffordAlgebra positiveForm)ˣ) : CliffordAlgebra positiveForm) = 1
  rw [circlePin, pinVector_coe, CliffordAlgebra.ι_sq_scalar, circleVector_normalized, map_one]

abbrev circleFrame (t : ℝ) : Spinor ≃ₗ[ℂ] Spinor := pinFrame (circlePin t)

/-- The actual represented frame has the explicit trigonometric matrix. -/
theorem circleFrame_apply (t : ℝ) (s : Spinor) :
    circleFrame t s = Real.cos t • gammaX s + Real.sin t • gammaY s := by
  rw [pinFrame_apply]
  simp only [circlePin, pinVector_coe, positiveRepresentation_vector]
  ext i
  fin_cases i <;>
    simp [circleVector, vectorPlus, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      gammaX_apply, gammaY_apply, add_comm]

theorem circleFrame_sq (t : ℝ) : circleFrame t * circleFrame t = 1 := by
  rw [← map_mul pinFrame, circlePin_sq, map_one]

@[simp] theorem circleFrame_symm_apply (t : ℝ) (s : Spinor) :
    (circleFrame t).symm s = circleFrame t s := by
  apply (circleFrame t).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (congrArg (fun U : Spinor ≃ₗ[ℂ] Spinor => U s) (circleFrame_sq t)).symm

/-- The explicit family retains noncommutative matrix content. -/
theorem circleFrames_noncommute :
    ¬ Commute (circleFrame 0) (circleFrame (Real.pi / 2)) := by
  intro h
  have he := congrArg (fun U : Spinor ≃ₗ[ℂ] Spinor => U ![1, 0] 1) h.eq
  change circleFrame 0 (circleFrame (Real.pi / 2) ![1, 0]) 1 =
    circleFrame (Real.pi / 2) (circleFrame 0 ![1, 0]) 1 at he
  simp only [circleFrame_apply, Real.cos_zero, Real.sin_zero,
    Real.cos_pi_div_two, Real.sin_pi_div_two, one_smul, zero_smul,
    zero_add, add_zero] at he
  norm_num [gammaX_apply, gammaY_apply] at he

/-- Smoothness of evaluated frame transport is derived from the explicit
family formula. No continuity of an unspecified Pin parameter map is assumed. -/
theorem circleFrame_field_contDiff (ψ : PlanePoint → Spinor)
    (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (fun z : ℝ × PlanePoint => circleFrame z.1 (ψ z.2)) := by
  have hx : ContDiff ℝ ∞ (fun z : ℝ × PlanePoint => gammaX (ψ z.2)) :=
    gammaX.contDiff.comp (hψ.comp contDiff_snd)
  have hy : ContDiff ℝ ∞ (fun z : ℝ × PlanePoint => gammaY (ψ z.2)) :=
    gammaY.contDiff.comp (hψ.comp contDiff_snd)
  have hd := ((Real.contDiff_cos.comp contDiff_fst).smul hx).add
    ((Real.contDiff_sin.comp contDiff_fst).smul hy)
  refine contDiffOn_univ.mp (hd.contDiffOn.congr ?_)
  intro z _
  simpa only [Pi.smul_apply', Function.comp_apply] using circleFrame_apply z.1 (ψ z.2)

/-- The smoothly varying frame acts on the actual smooth section domain. -/
theorem circleSection_joint_contDiff (sector : Bool) (ψ : smoothSections sector) :
    ContDiff ℝ ∞ (fun z : ℝ × PlanePoint =>
      (frameSmoothEquiv (circleFrame z.1) sector ψ).val.val z.2) := by
  simpa only [frameSmoothEquiv_apply] using
    circleFrame_field_contDiff _ (smoothSection_contDiff sector ψ)

/-- In the constructed domain identification, the evaluated geometric
operator family is jointly smooth in parameter and base point. -/
theorem circleDirac_joint_contDiff (sector : Bool) (ψ : smoothSections sector) :
    ContDiff ℝ ∞ (fun z : ℝ × PlanePoint =>
      framedDirac (circleFrame z.1)
        ((frameSmoothEquiv (circleFrame z.1) sector ψ).val : PlanePoint → Spinor) z.2) := by
  have heq : (fun z : ℝ × PlanePoint =>
      framedDirac (circleFrame z.1)
        ((frameSmoothEquiv (circleFrame z.1) sector ψ).val : PlanePoint → Spinor) z.2) =
      (fun z : ℝ × PlanePoint => circleFrame z.1 (dirac (ψ.val : PlanePoint → Spinor) z.2)) := by
    funext z
    rw [frameSmoothEquiv_field]
    exact framedDirac_intertwine (circleFrame z.1) _
      (smoothSection_differentiable sector ψ) z.2
  rw [heq]
  exact circleFrame_field_contDiff _ (dirac_smooth _ (smoothSection_contDiff sector ψ))

/-- The volume-compensated concrete family is jointly smooth in parameter
and base point in its explicitly constructed domain coordinates. -/
theorem circleSuspendedDirac_joint_contDiff (sector : Bool) (ψ : smoothSections sector) :
    ContDiff ℝ ∞ (fun z : ℝ × PlanePoint =>
      framedSuspendedDirac (circleFrame z.1)
        ((frameSmoothEquiv (circleFrame z.1) sector ψ).val : PlanePoint → Spinor) z.2) := by
  have heq : (fun z : ℝ × PlanePoint =>
      framedSuspendedDirac (circleFrame z.1)
        ((frameSmoothEquiv (circleFrame z.1) sector ψ).val : PlanePoint → Spinor) z.2) =
      (fun z : ℝ × PlanePoint => circleFrame z.1
        (InfoGeometry.Clifford.FreedKleinRepresentation.suspendedDirac
          (ψ.val : PlanePoint → Spinor) z.2)) := by
    funext z
    rw [frameSmoothEquiv_field]
    exact framedSuspendedDirac_intertwine (circleFrame z.1) _
      (smoothSection_differentiable sector ψ) z.2
  rw [heq]
  exact circleFrame_field_contDiff _
    (InfoGeometry.Clifford.FreedKleinRepresentation.suspendedDirac_smooth _
      (smoothSection_contDiff sector ψ))

end InfoGeometry.Geometry.KleinPinFrameFamily

end
