import InfoGeometry.Lie.SplitOctonionEllClosedFlow
import InfoGeometry.Lie.SplitOctonionAxialKleinBridge

/-!
# The closed `ell` flow on the active Klein support

The projector-derived `ellFlowPhi` is a linear split-Zorn flow on the full
carrier.  This owner restricts it to the Drazin active support and transports
the already-proved native determinant isometry through the concrete Klein
linear equivalence.  It makes no multiplication-preservation claim.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllKleinFlow

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Lie.SplitOctonionAxialKleinBridge
open InfoGeometry.Lie.SplitOctonionAxialSupportGrading
open InfoGeometry.Lie.SplitOctonionAxialWittReduction
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.SplitOctonionEllTrifactor

abbrev CZ := CanonicalZorn
abbrev ActiveSector := LinearMap.range axialActiveSupport

/-- The closed `ell` flow commutes with the native active-support projection. -/
theorem ellFlowPhi_commutes_activeSupport (t : ℝ) (Z : CZ) :
    axialActiveSupport (ellFlowPhi t Z) =
      ellFlowPhi t (axialActiveSupport Z) := by
  rw [axialActiveSupport_apply, ellFlowPhi_coord, ellFlowPhi_coord,
    axialActiveSupport_apply]

/-- The stationary projector also commutes with the closed flow.  In fact its
image is fixed pointwise. -/
theorem ellFlowPhi_commutes_PZero (t : ℝ) (Z : CZ) :
    ellFlowPZero (ellFlowPhi t Z) =
      ellFlowPhi t (ellFlowPZero Z) := by
  rw [ellFlowPZero_coord, ellFlowPhi_coord,
    ellFlowPhi_on_PZero, ellFlowPZero_coord]

/-! ## Native Witt-pairing identities -/

/-- The positive root sector is totally isotropic for the raw determinant
polarization. -/
theorem ellFlowPPlus_det_polar_zero (X Y : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
          (ellFlowPPlus X + ellFlowPPlus Y) -
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (ellFlowPPlus X) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (ellFlowPPlus Y) = 0 := by
  rw [ellFlowPPlus_coord, ellFlowPPlus_coord]
  simp [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, realCrossProduct3,
    InfoGeometry.Canonical.ZornMatrix.dot]

/-- The negative root sector is totally isotropic for the raw determinant
polarization. -/
theorem ellFlowPMinus_det_polar_zero (X Y : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
          (ellFlowPMinus X + ellFlowPMinus Y) -
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (ellFlowPMinus X) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (ellFlowPMinus Y) = 0 := by
  rw [ellFlowPMinus_coord, ellFlowPMinus_coord]
  simp [InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, realCrossProduct3,
    InfoGeometry.Canonical.ZornMatrix.dot]

/-- Opposite root weights preserve their raw determinant cross-pairing under
the closed flow. -/
theorem ellFlowPhi_preserves_dual_root_polar
    (t : ℝ) (X Y : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
          (ellFlowPhi t (ellFlowPPlus X) +
            ellFlowPhi t (ellFlowPMinus Y)) -
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
          (ellFlowPhi t (ellFlowPPlus X)) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
            (ellFlowPhi t (ellFlowPMinus Y)) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
          (ellFlowPPlus X + ellFlowPMinus Y) -
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (ellFlowPPlus X) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (ellFlowPMinus Y) := by
  have h := ellFlowPhi_preserves_det_polarization t
    (ellFlowPPlus X) (ellFlowPMinus Y)
  rw [(ellFlowPhi t).map_add] at h
  exact h

/-- Restriction of the closed `ell` flow to the active support. -/
def ellFlowActive (t : ℝ) : ActiveSector ≃ₗ[ℝ] ActiveSector where
  toFun X :=
    ⟨ellFlowPhi t X.1, by
      rcases X.2 with ⟨Y, hY⟩
      refine ⟨ellFlowPhi t Y, ?_⟩
      rw [ellFlowPhi_commutes_activeSupport, hY]⟩
  invFun X :=
    ⟨ellFlowPhi (-t) X.1, by
      rcases X.2 with ⟨Y, hY⟩
      refine ⟨ellFlowPhi (-t) Y, ?_⟩
      rw [ellFlowPhi_commutes_activeSupport, hY]⟩
  map_add' X Y := by
    apply Subtype.ext
    exact (ellFlowPhi t).map_add X.1 Y.1
  map_smul' r X := by
    apply Subtype.ext
    exact (ellFlowPhi t).map_smul r X.1
  left_inv X := by
    apply Subtype.ext
    have h := congrArg (fun F : Module.End ℝ CZ => F X.1)
      (ellFlowPhi_neg_mul t)
    simpa [Module.End.mul_apply] using h
  right_inv X := by
    apply Subtype.ext
    have h := congrArg (fun F : Module.End ℝ CZ => F X.1)
      (ellFlowPhi_mul_neg t)
    simpa [Module.End.mul_apply] using h

@[simp] theorem ellFlowActive_zero (X : ActiveSector) :
    ellFlowActive 0 X = X := by
  apply Subtype.ext
  change ellFlowPhi 0 X.1 = X.1
  rw [ellFlowPhi_zero]
  rfl

theorem ellFlowActive_add (s t : ℝ) (X : ActiveSector) :
    ellFlowActive (s + t) X =
      ellFlowActive s (ellFlowActive t X) := by
  apply Subtype.ext
  change ellFlowPhi (s + t) X.1 =
    ellFlowPhi s (ellFlowPhi t X.1)
  have h := congrArg (fun F : Module.End ℝ CZ => F X.1)
    (ellFlowPhi_add s t)
  simpa [Module.End.mul_apply] using h

theorem ellFlowActive_inverse_left (t : ℝ) (X : ActiveSector) :
    ellFlowActive (-t) (ellFlowActive t X) = X := by
  rw [← ellFlowActive_add, neg_add_cancel, ellFlowActive_zero]

theorem ellFlowActive_inverse_right (t : ℝ) (X : ActiveSector) :
    ellFlowActive t (ellFlowActive (-t) X) = X := by
  rw [← ellFlowActive_add, add_neg_cancel, ellFlowActive_zero]

/-- The restricted closed `ell` flow preserves the transported Klein form. -/
theorem ellFlowActive_preserves_kleinForm (t : ℝ) (X : ActiveSector) :
    kleinForm (activeKleinLinearEquiv (ellFlowActive t X)) =
      kleinForm (activeKleinLinearEquiv X) := by
  rw [kleinForm_activeKleinLinearEquiv,
    kleinForm_activeKleinLinearEquiv]
  exact ellFlowPhi_preserves_det t X.1

/-- The restricted flow preserves the Klein null locus exactly. -/
theorem ellFlowActive_coordinateKleinForm_eq_zero_iff
    (t : ℝ) (X : ActiveSector) :
    kleinForm (activeKleinLinearEquiv (ellFlowActive t X)) = 0 ↔
      kleinForm (activeKleinLinearEquiv X) = 0 := by
  rw [ellFlowActive_preserves_kleinForm]

/-- The same exact null-locus preservation after transport to the literal
second exterior power of the four-coordinate carrier. -/
theorem ellFlowActive_kleinForm_eq_zero_iff (t : ℝ) (X : ActiveSector) :
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
        (activeExteriorLinearEquiv (ellFlowActive t X)) = 0 ↔
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.exteriorKleinForm
        (activeExteriorLinearEquiv X) = 0 := by
  rw [exteriorKleinForm_activeExterior,
    exteriorKleinForm_activeExterior]
  change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
      (ellFlowPhi t X.1) = 0 ↔
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X.1 = 0
  rw [ellFlowPhi_preserves_det]

/-- The restricted closed `ell` flow preserves the full active Klein
polarization, hence the transported incidence pairing as well as its null
cone. -/
theorem ellFlowActive_preserves_kleinPolar (t : ℝ) (X Y : ActiveSector) :
    activeKleinPolar (ellFlowActive t X) (ellFlowActive t Y) =
      activeKleinPolar X Y := by
  calc
    activeKleinPolar (ellFlowActive t X) (ellFlowActive t Y) =
        activeDetPolar (ellFlowActive t X) (ellFlowActive t Y) :=
      activeKleinLinearEquiv_preserves_polar _ _
    _ = activeDetPolar X Y := by
      unfold activeDetPolar
      have hsum := congrArg Subtype.val ((ellFlowActive t).map_add X Y)
      have hsum' : (ellFlowActive t X).1 + (ellFlowActive t Y).1 =
          (ellFlowActive t (X + Y)).1 := hsum.symm
      have hXY : (X + Y).1 = X.1 + Y.1 := rfl
      rw [hsum']
      change InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3
          (ellFlowPhi t (X + Y).1) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (ellFlowPhi t X.1) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (ellFlowPhi t Y.1) =
        InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 (X.1 + Y.1) -
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 X.1 -
            InfoGeometry.Algebra.Zorn.ZornMatrix.detZ realCrossProduct3 Y.1
      rw [ellFlowPhi_preserves_det, ellFlowPhi_preserves_det,
        ellFlowPhi_preserves_det]
      rw [← hXY]
    _ = activeKleinPolar X Y :=
      (activeKleinLinearEquiv_preserves_polar X Y).symm

end InfoGeometry.Lie.SplitOctonionEllKleinFlow
