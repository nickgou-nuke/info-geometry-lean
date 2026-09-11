import InfoGeometry.Canonical.MongeAmpereDualSheetBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Volume.DeterminantBundle
import Mathlib.Tactic

namespace InfoGeometry.Canonical.RestrictedVolumeCharacter

open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.TomitaTakesaki
open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Volume.Base
open InfoGeometry.Volume.DeterminantBundle
open Base

open Lean.Parser.Tactic in
/-- Automates the common doubled-space operator extensionality proof pattern. -/
macro "doubled_ext" : tactic =>
  `(tactic| (
      apply ContinuousLinearMap.ext
      intro u
      apply DoubledSpace.ext <;>
      simp [ContinuousLinearMap.comp_apply, to_doubled,
        spectralPlusProj_apply_eq_plusPoint, spectralMinusProj_apply_eq_minusPoint,
        TomitaTakesaki.modularSignEpsilon, spectral_epsilon, mul_smul]
    ))

section DiagonalOperators

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Independent sheetwise lift of a pair of base-carrier operators. -/
noncomputable def dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) : EndH :=
  (plusPointL (E := E)).comp (Aplus.comp (fst_L (E := E))) +
    (minusPointL (E := E)).comp (Aminus.comp (snd_L (E := E)))

omit [CompleteSpace E] in
@[simp] theorem dualSheetPairLift_apply_to_doubled
    (Aplus Aminus : E →L[ℝ] E) (x xi : E) :
    dualSheetPairLift (E := E) Aplus Aminus (to_doubled x xi : H₂)
      = to_doubled (Aplus x) (Aminus xi) := by
  apply DoubledSpace.ext <;>
    simp [dualSheetPairLift, plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
      ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem dualSheetLift_eq_dualSheetPairLift_same
    (A : E →L[ℝ] E) :
    dualSheetLift (E := E) A = dualSheetPairLift (E := E) A A := by
  rfl

omit [CompleteSpace E] in
@[simp] theorem plusBlockMap_dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) :
    plusBlockMap (E := E) (dualSheetPairLift (E := E) Aplus Aminus) = Aplus := by
  ext x
  simp [plusBlockMap, dualSheetPairLift, plusPointL, minusPointL, plusPoint, minusPoint,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem minusBlockMap_dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) :
    minusBlockMap (E := E) (dualSheetPairLift (E := E) Aplus Aminus) = Aminus := by
  ext x
  simp [minusBlockMap, dualSheetPairLift, plusPointL, minusPointL, plusPoint, minusPoint,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem plusToMinusBlockMap_dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) :
    plusToMinusBlockMap (E := E) (dualSheetPairLift (E := E) Aplus Aminus) = 0 := by
  ext x
  simp [plusToMinusBlockMap, dualSheetPairLift, plusPointL, minusPointL, plusPoint, minusPoint,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem minusToPlusBlockMap_dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) :
    minusToPlusBlockMap (E := E) (dualSheetPairLift (E := E) Aplus Aminus) = 0 := by
  ext x
  simp [minusToPlusBlockMap, dualSheetPairLift, plusPointL, minusPointL, plusPoint, minusPoint,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
theorem spectralPlusProj_comp_dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) :
    (spectralPlusProj (E := E)).comp (dualSheetPairLift (E := E) Aplus Aminus)
      = (dualSheetPairLift (E := E) Aplus Aminus).comp (spectralPlusProj (E := E)) := by
  unfold dualSheetPairLift
  doubled_ext

omit [CompleteSpace E] in
theorem spectralMinusProj_comp_dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) :
    (spectralMinusProj (E := E)).comp (dualSheetPairLift (E := E) Aplus Aminus)
      = (dualSheetPairLift (E := E) Aplus Aminus).comp (spectralMinusProj (E := E)) := by
  unfold dualSheetPairLift
  doubled_ext

omit [CompleteSpace E] in
@[simp] theorem plusProjectorFlux_dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) :
    plusProjectorFlux (E := E) (dualSheetPairLift (E := E) Aplus Aminus) = 0 := by
  unfold InfoGeometry.Canonical.BogoliubovProjectorFlux.plusProjectorFlux
  rw [spectralPlusProj_comp_dualSheetPairLift]
  simp

omit [CompleteSpace E] in
@[simp] theorem minusProjectorFlux_dualSheetPairLift
    (Aplus Aminus : E →L[ℝ] E) :
    minusProjectorFlux (E := E) (dualSheetPairLift (E := E) Aplus Aminus) = 0 := by
  unfold InfoGeometry.Canonical.BogoliubovProjectorFlux.minusProjectorFlux
  rw [spectralMinusProj_comp_dualSheetPairLift]
  simp

/-- Grading-diagonal scalar operator with independent plus/minus sheet weights. -/
noncomputable def dualSheetDiagonalScalarOp
    (rhoPlus rhoMinus : ℝ) : EndH :=
  dualSheetPairLift (E := E)
    (rhoPlus • (ContinuousLinearMap.id ℝ E))
    (rhoMinus • (ContinuousLinearMap.id ℝ E))

omit [CompleteSpace E] in
@[simp] theorem dualSheetDiagonalScalarOp_apply_to_doubled
    (rhoPlus rhoMinus : ℝ) (x xi : E) :
    dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus (to_doubled x xi : H₂)
      = to_doubled (rhoPlus • x) (rhoMinus • xi) := by
  rw [dualSheetDiagonalScalarOp]
  exact dualSheetPairLift_apply_to_doubled (E := E)
    (rhoPlus • (ContinuousLinearMap.id ℝ E))
    (rhoMinus • (ContinuousLinearMap.id ℝ E)) x xi

omit [CompleteSpace E] in
@[simp] theorem dualSheetDiagonalScalarOp_eq_smul_proj_add
    (rhoPlus rhoMinus : ℝ) :
    dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus
      = rhoPlus • (spectralPlusProj (E := E)) + rhoMinus • (spectralMinusProj (E := E)) := by
  unfold dualSheetDiagonalScalarOp dualSheetPairLift
  doubled_ext

omit [CompleteSpace E] in
@[simp] theorem plusBlockMap_dualSheetDiagonalScalarOp
    (rhoPlus rhoMinus : ℝ) :
    plusBlockMap (E := E) (dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus)
      = rhoPlus • (ContinuousLinearMap.id ℝ E) := by
  rw [dualSheetDiagonalScalarOp]
  exact plusBlockMap_dualSheetPairLift (E := E)
    (rhoPlus • (ContinuousLinearMap.id ℝ E))
    (rhoMinus • (ContinuousLinearMap.id ℝ E))

omit [CompleteSpace E] in
@[simp] theorem minusBlockMap_dualSheetDiagonalScalarOp
    (rhoPlus rhoMinus : ℝ) :
    minusBlockMap (E := E) (dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus)
      = rhoMinus • (ContinuousLinearMap.id ℝ E) := by
  rw [dualSheetDiagonalScalarOp]
  exact minusBlockMap_dualSheetPairLift (E := E)
    (rhoPlus • (ContinuousLinearMap.id ℝ E))
    (rhoMinus • (ContinuousLinearMap.id ℝ E))

omit [CompleteSpace E] in
@[simp] theorem plusToMinusBlockMap_dualSheetDiagonalScalarOp
    (rhoPlus rhoMinus : ℝ) :
    plusToMinusBlockMap (E := E) (dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus) = 0 := by
  rw [dualSheetDiagonalScalarOp]
  exact plusToMinusBlockMap_dualSheetPairLift (E := E)
    (rhoPlus • (ContinuousLinearMap.id ℝ E))
    (rhoMinus • (ContinuousLinearMap.id ℝ E))

omit [CompleteSpace E] in
@[simp] theorem minusToPlusBlockMap_dualSheetDiagonalScalarOp
    (rhoPlus rhoMinus : ℝ) :
    minusToPlusBlockMap (E := E) (dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus) = 0 := by
  rw [dualSheetDiagonalScalarOp]
  exact minusToPlusBlockMap_dualSheetPairLift (E := E)
    (rhoPlus • (ContinuousLinearMap.id ℝ E))
    (rhoMinus • (ContinuousLinearMap.id ℝ E))

omit [CompleteSpace E] in
@[simp] theorem plusProjectorFlux_dualSheetDiagonalScalarOp
    (rhoPlus rhoMinus : ℝ) :
    plusProjectorFlux (E := E) (dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus) = 0 := by
  rw [dualSheetDiagonalScalarOp]
  exact plusProjectorFlux_dualSheetPairLift (E := E)
    (rhoPlus • (ContinuousLinearMap.id ℝ E))
    (rhoMinus • (ContinuousLinearMap.id ℝ E))

omit [CompleteSpace E] in
@[simp] theorem minusProjectorFlux_dualSheetDiagonalScalarOp
    (rhoPlus rhoMinus : ℝ) :
    minusProjectorFlux (E := E) (dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus) = 0 := by
  rw [dualSheetDiagonalScalarOp]
  exact minusProjectorFlux_dualSheetPairLift (E := E)
    (rhoPlus • (ContinuousLinearMap.id ℝ E))
    (rhoMinus • (ContinuousLinearMap.id ℝ E))

omit [CompleteSpace E] in
@[simp] theorem dualSheetDiagonalScalarOp_same
    (rho : ℝ) :
    dualSheetDiagonalScalarOp (E := E) rho rho = rho • (ContinuousLinearMap.id ℝ H₂) := by
  unfold dualSheetDiagonalScalarOp dualSheetPairLift
  doubled_ext

omit [CompleteSpace E] in
@[simp] theorem dualSheetDiagonalScalarOp_one_one :
    dualSheetDiagonalScalarOp (E := E) 1 1 = ContinuousLinearMap.id ℝ H₂ := by
  rw [dualSheetDiagonalScalarOp_same (E := E) (rho := 1)]
  simp

omit [CompleteSpace E] in
@[simp] theorem dualSheetDiagonalScalarOp_one_neg_one :
    dualSheetDiagonalScalarOp (E := E) 1 (-1) = modularSignEpsilon (E := E) := by
  unfold dualSheetDiagonalScalarOp dualSheetPairLift
  doubled_ext

omit [CompleteSpace E] in
@[simp] theorem dualSheetDiagonalScalarOp_one_neg_one_eq_spectral_epsilon :
    dualSheetDiagonalScalarOp (E := E) 1 (-1) = spectral_epsilon (E := E) := by
  simpa [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon] using
    dualSheetDiagonalScalarOp_one_neg_one (E := E)

/-- Common Weyl scale shared by both sheets. -/
noncomputable def commonWeylScale (rhoPlus rhoMinus : ℝ) : ℝ :=
  (rhoPlus + rhoMinus) / 2

/-- Relative chiral scale measuring sheet imbalance. -/
noncomputable def relativeSheetScale (rhoPlus rhoMinus : ℝ) : ℝ :=
  (rhoPlus - rhoMinus) / 2

/-- Isotropic Weyl-gauge part of a grading-diagonal scalar operator. -/
noncomputable def isotropicWeylPart
    (rhoPlus rhoMinus : ℝ) : EndH :=
  commonWeylScale rhoPlus rhoMinus • (ContinuousLinearMap.id ℝ H₂)

/-- Relative `ε`-dilation part of a grading-diagonal scalar operator. -/
noncomputable def chiralDilationPart
    (rhoPlus rhoMinus : ℝ) : EndH :=
  relativeSheetScale rhoPlus rhoMinus • (modularSignEpsilon (E := E))

noncomputable def chiralDilationPartCore
    (rhoPlus rhoMinus : ℝ) : EndH :=
  relativeSheetScale rhoPlus rhoMinus • (spectral_epsilon (E := E))

omit [CompleteSpace E] in
@[simp] theorem chiralDilationPart_eq_core
    (rhoPlus rhoMinus : ℝ) :
    chiralDilationPart (E := E) rhoPlus rhoMinus
      = chiralDilationPartCore (E := E) rhoPlus rhoMinus := by
  simp [chiralDilationPart, chiralDilationPartCore]

@[simp] theorem commonWeylScale_add_relativeSheetScale
    (rhoPlus rhoMinus : ℝ) :
    commonWeylScale rhoPlus rhoMinus + relativeSheetScale rhoPlus rhoMinus = rhoPlus := by
  unfold commonWeylScale relativeSheetScale
  ring

@[simp] theorem commonWeylScale_sub_relativeSheetScale
    (rhoPlus rhoMinus : ℝ) :
    commonWeylScale rhoPlus rhoMinus - relativeSheetScale rhoPlus rhoMinus = rhoMinus := by
  unfold commonWeylScale relativeSheetScale
  ring

omit [CompleteSpace E] in
theorem dualSheetDiagonalScalarOp_eq_isotropicWeylPart_add_chiralDilationPart
    (rhoPlus rhoMinus : ℝ) :
    dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus
      = isotropicWeylPart (E := E) rhoPlus rhoMinus + chiralDilationPart (E := E) rhoPlus rhoMinus := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext
  · simp [dualSheetDiagonalScalarOp, dualSheetPairLift, isotropicWeylPart, chiralDilationPart,
      plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
      TomitaTakesaki.modularSignEpsilon, spectral_epsilon,
      commonWeylScale, relativeSheetScale]
    rw [← add_smul]
    have h : ((rhoPlus + rhoMinus) / 2 + (rhoPlus - rhoMinus) / 2) = rhoPlus := by ring
    rw [h]
  · simp [dualSheetDiagonalScalarOp, dualSheetPairLift, isotropicWeylPart, chiralDilationPart,
      plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
      TomitaTakesaki.modularSignEpsilon, spectral_epsilon,
      commonWeylScale, relativeSheetScale]
    rw [← sub_eq_add_neg, ← sub_smul]
    have h : ((rhoPlus + rhoMinus) / 2 - (rhoPlus - rhoMinus) / 2) = rhoMinus := by ring
    rw [h]

@[simp] theorem commonWeylScale_exp_pair
    (t : ℝ) :
    commonWeylScale (Real.exp t) (Real.exp (-t)) = Real.cosh t := by
  rw [(Real.cosh_add_sinh t).symm, (Real.cosh_sub_sinh t).symm]
  unfold commonWeylScale
  ring

@[simp] theorem relativeSheetScale_exp_pair
    (t : ℝ) :
    relativeSheetScale (Real.exp t) (Real.exp (-t)) = Real.sinh t := by
  rw [(Real.cosh_add_sinh t).symm, (Real.cosh_sub_sinh t).symm]
  unfold relativeSheetScale
  ring

theorem dualSheetDiagonalScalarOp_exp_pair_eq_epsilonBoost
    (t : ℝ) :
    dualSheetDiagonalScalarOp (E := E) (Real.exp t) (Real.exp (-t))
      = epsilonBoost (E := E) t := by
  rw [dualSheetDiagonalScalarOp_eq_isotropicWeylPart_add_chiralDilationPart,
    epsilonBoost_eq_cosh_add_sinh_eps]
  change commonWeylScale (Real.exp t) (Real.exp (-t)) • (ContinuousLinearMap.id ℝ H₂) +
      relativeSheetScale (Real.exp t) (Real.exp (-t)) • modularSignEpsilon (E := E) =
    Real.cosh t • (ContinuousLinearMap.id ℝ H₂) + Real.sinh t • modularSignEpsilon (E := E)
  simp

theorem dualSheetDiagonalScalarOp_exp_pair_eq_epsilonBoost_core
    (t : ℝ) :
    dualSheetDiagonalScalarOp (E := E) (Real.exp t) (Real.exp (-t))
      = Real.cosh t • (ContinuousLinearMap.id ℝ H₂)
        + Real.sinh t • spectral_epsilon (E := E) := by
  rw [dualSheetDiagonalScalarOp_exp_pair_eq_epsilonBoost (E := E) t]
  rw [epsilonBoost_eq_cosh_add_sinh_eps]
  change Real.cosh t • (ContinuousLinearMap.id ℝ H₂)
      + Real.sinh t • modularSignEpsilon (E := E)
    =
    Real.cosh t • (ContinuousLinearMap.id ℝ H₂)
      + Real.sinh t • spectral_epsilon (E := E)
  simp [TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon]

omit [CompleteSpace E] in
theorem dualSheetDiagonalScalarOp_weylGaugeRescale
    (sigma rhoPlus rhoMinus : ℝ) :
    dualSheetDiagonalScalarOp (E := E) (sigma * rhoPlus) (sigma * rhoMinus)
      = sigma • dualSheetDiagonalScalarOp (E := E) rhoPlus rhoMinus := by
  unfold dualSheetDiagonalScalarOp dualSheetPairLift
  doubled_ext

end DiagonalOperators

/-- Restricted sheetwise automorphism data for the split Weyl character. -/
structure RestrictedSheetEquiv
    (E : Type*) [AddCommGroup E] [Module ℝ E] where
  plus : E ≃ₗ[ℝ] E
  minus : E ≃ₗ[ℝ] E

namespace RestrictedSheetEquiv

section GroupStructure

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

instance : Mul (RestrictedSheetEquiv E) where
  mul g₁ g₂ :=
    { plus := g₁.plus.trans g₂.plus
      minus := g₁.minus.trans g₂.minus }

instance : One (RestrictedSheetEquiv E) where
  one :=
    { plus := LinearEquiv.refl ℝ E
      minus := LinearEquiv.refl ℝ E }

instance : Inv (RestrictedSheetEquiv E) where
  inv g :=
    { plus := g.plus.symm
      minus := g.minus.symm }

instance : Group (RestrictedSheetEquiv E) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc a b c := by
    cases a; cases b; cases c; rfl
  one_mul a := by
    cases a; rfl
  mul_one a := by
    cases a; rfl
  inv_mul_cancel a := by
    cases a with
    | mk plus minus =>
        change RestrictedSheetEquiv.mk (plus.symm.trans plus) (minus.symm.trans minus) =
            RestrictedSheetEquiv.mk (LinearEquiv.refl ℝ E) (LinearEquiv.refl ℝ E)
        simp

end GroupStructure

section RestrictedCharacter

variable {E : Type*}
variable [AddCommGroup E] [Module ℝ E]

/-- Common Weyl-gauge rescaling by the same base automorphism on both sheets. -/
def weylGaugeRescale
    (w : E ≃ₗ[ℝ] E) (g : RestrictedSheetEquiv E) : RestrictedSheetEquiv E where
  plus := w.trans g.plus
  minus := w.trans g.minus

/-- Scalar Weyl rescaling by a nonzero real dilation. -/
noncomputable def weylGaugeRescaleByScalar
    (sigma : ℝ) (hsigma : sigma ≠ 0) (g : RestrictedSheetEquiv E) : RestrictedSheetEquiv E :=
  weylGaugeRescale (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) sigma hsigma) g

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Plus-sheet Weyl scale carried by the determinant line. -/
noncomputable def plusSheetVolumeScale (g : RestrictedSheetEquiv E) : ℝ :=
  volumeScale g.plus

/-- Minus-sheet Weyl scale carried by the determinant line. -/
noncomputable def minusSheetVolumeScale (g : RestrictedSheetEquiv E) : ℝ :=
  volumeScale g.minus

/-- Split Weyl character storing the separate plus/minus determinant scales. -/
noncomputable def splitWeylCharacter (g : RestrictedSheetEquiv E) : ℝ × ℝ :=
  (plusSheetVolumeScale g, minusSheetVolumeScale g)

/-- Gauge-invariant ratio of the plus/minus sheet volume characters. -/
noncomputable def restrictedVolumeCharacter (g : RestrictedSheetEquiv E) : ℝˣ :=
  VolumeHom g.plus * (VolumeHom g.minus)⁻¹

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrictedVolumeCharacter_one :
    restrictedVolumeCharacter (1 : RestrictedSheetEquiv E) = 1 := by
  change VolumeHom (LinearEquiv.refl ℝ E) * (VolumeHom (LinearEquiv.refl ℝ E))⁻¹ = 1
  simp [VolumeHom]

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrictedVolumeCharacter_mul (g₁ g₂ : RestrictedSheetEquiv E) :
    restrictedVolumeCharacter (g₁ * g₂) =
      restrictedVolumeCharacter g₁ * restrictedVolumeCharacter g₂ := by
  cases g₁ with
  | mk plus₁ minus₁ =>
      cases g₂ with
      | mk plus₂ minus₂ =>
          change VolumeHom (plus₁.trans plus₂) * (VolumeHom (minus₁.trans minus₂))⁻¹ =
              (VolumeHom plus₁ * (VolumeHom minus₁)⁻¹) *
                (VolumeHom plus₂ * (VolumeHom minus₂)⁻¹)
          simp [VolumeHom, LinearEquiv.det_trans, mul_assoc, mul_left_comm, mul_comm]

/-- The restricted volume character as a formal group homomorphism to `ℝˣ`. -/
noncomputable def restrictedVolumeCharacterHom : RestrictedSheetEquiv E →* ℝˣ where
  toFun := restrictedVolumeCharacter
  map_one' := restrictedVolumeCharacter_one
  map_mul' := restrictedVolumeCharacter_mul

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrictedVolumeCharacter_inv (g : RestrictedSheetEquiv E) :
    restrictedVolumeCharacter g⁻¹ = (restrictedVolumeCharacter g)⁻¹ := by
  cases g with
  | mk plus minus =>
      change VolumeHom plus.symm * (VolumeHom minus.symm)⁻¹ =
          (VolumeHom plus * (VolumeHom minus)⁻¹)⁻¹
      simp [VolumeHom, mul_comm]

/-- Positive scalar shadow of the gauge-invariant sheet ratio. -/
noncomputable def restrictedVolumeScale (g : RestrictedSheetEquiv E) : ℝ :=
  plusSheetVolumeScale g / minusSheetVolumeScale g

/-- Common Weyl-gauge volume potential carried by both sheets together. -/
noncomputable def weylGaugeVolumePotential (g : RestrictedSheetEquiv E) : ℝ :=
  plusSheetVolumeScale g * minusSheetVolumeScale g

/-- Relative-volume-preserving means the sheet ratio is trivial. -/
def IsRelativeVolumePreserving (g : RestrictedSheetEquiv E) : Prop :=
  restrictedVolumeCharacter g = 1

/-- Weyl-gauge-balanced means both sheet automorphisms agree. -/
def IsWeylGaugeBalanced (g : RestrictedSheetEquiv E) : Prop :=
  g.plus = g.minus

omit [FiniteDimensional ℝ E] in
@[simp] theorem volumeScale_pos (f : E ≃ₗ[ℝ] E) : 0 < volumeScale f := by
  unfold volumeScale
  exact abs_pos.mpr (Units.ne_zero _)

omit [FiniteDimensional ℝ E] in
@[simp] theorem volumeScale_trans (f g : E ≃ₗ[ℝ] E) :
    volumeScale (f.trans g) = volumeScale g * volumeScale f := by
  unfold volumeScale VolumeHom
  simp [LinearEquiv.det_trans, abs_mul, mul_comm]

omit [FiniteDimensional ℝ E] in
@[simp] theorem splitWeylCharacter_fst (g : RestrictedSheetEquiv E) :
    (splitWeylCharacter g).1 = plusSheetVolumeScale g := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem splitWeylCharacter_snd (g : RestrictedSheetEquiv E) :
    (splitWeylCharacter g).2 = minusSheetVolumeScale g := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrictedVolumeCharacter_weylGaugeRescale
    (w : E ≃ₗ[ℝ] E) (g : RestrictedSheetEquiv E) :
    restrictedVolumeCharacter (weylGaugeRescale w g) = restrictedVolumeCharacter g := by
  cases g
  unfold restrictedVolumeCharacter weylGaugeRescale VolumeHom
  simp [LinearEquiv.det_trans]
  group

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrictedVolumeCharacter_weylGaugeRescaleByScalar
    (sigma : ℝ) (hsigma : sigma ≠ 0) (g : RestrictedSheetEquiv E) :
    restrictedVolumeCharacter (weylGaugeRescaleByScalar sigma hsigma g)
      = restrictedVolumeCharacter g := by
  rw [weylGaugeRescaleByScalar]
  exact restrictedVolumeCharacter_weylGaugeRescale
    (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) sigma hsigma) g

omit [FiniteDimensional ℝ E] in
theorem restrictedVolumeScale_eq_abs_character
    (g : RestrictedSheetEquiv E) :
    restrictedVolumeScale g = |((restrictedVolumeCharacter g : ℝˣ) : ℝ)| := by
  cases g
  unfold restrictedVolumeScale restrictedVolumeCharacter plusSheetVolumeScale minusSheetVolumeScale
  unfold volumeScale VolumeHom
  simp [div_eq_mul_inv, abs_mul, abs_inv]

omit [FiniteDimensional ℝ E] in
@[simp] theorem restrictedVolumeScale_weylGaugeRescale
    (w : E ≃ₗ[ℝ] E) (g : RestrictedSheetEquiv E) :
    restrictedVolumeScale (weylGaugeRescale w g) = restrictedVolumeScale g := by
  rw [restrictedVolumeScale_eq_abs_character, restrictedVolumeScale_eq_abs_character,
    restrictedVolumeCharacter_weylGaugeRescale]

omit [FiniteDimensional ℝ E] in
theorem restrictedVolumeCharacter_eq_one_of_weylGaugeBalanced
    {g : RestrictedSheetEquiv E}
    (hBal : IsWeylGaugeBalanced g) :
    restrictedVolumeCharacter g = 1 := by
  cases g with
  | mk plus minus =>
      simp [IsWeylGaugeBalanced] at hBal
      subst minus
      unfold restrictedVolumeCharacter VolumeHom
      simp

end FiniteDimensional
end RestrictedCharacter

end RestrictedSheetEquiv

end InfoGeometry.Canonical.RestrictedVolumeCharacter
