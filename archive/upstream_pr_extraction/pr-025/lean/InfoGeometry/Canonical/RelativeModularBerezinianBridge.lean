import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Canonical.RestrictedVolumeCharacter
import InfoGeometry.Geometry.KreinAsHessian
import InfoGeometry.Algebraic.SplitSuperGeometry
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import InfoGeometry.Meta.Architecture

/-!
# Relative Modular Berezinian Bridge

Bridge from the finite diagonal relative modular operator owner to the existing
restricted-sheet and Cartan Berezinian surfaces.

The owner remains `relativeModularOperator` and its scalar shadows in
`RelativeModularOperator.lean`. This file only realizes the plus/minus modular
operators as sheet automorphisms on `Fin n → ℝ` and identifies the resulting
restricted-volume and Berezinian readouts with the modular supervolume shadow.
-/

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.RelativeModularBerezinianBridge

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RestrictedVolumeCharacter
open InfoGeometry.Algebraic.SplitSignature
open InfoGeometry.Geometry
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal
open InfoGeometry.Volume.Base
open scoped InnerProductSpace

section Finite

variable {n : ℕ} [Nonempty (Fin n)]

local notation "Efin" => (Fin n → ℝ)

private theorem relativeModularOperator_det_isUnit
    (q q0 : PositiveRay (Fin n)) :
    IsUnit ((relativeModularOperator (n := n) q q0).det) := by
  classical
  apply isUnit_iff_ne_zero.mpr
  simpa [relativeModularVolumeShadow] using
    ne_of_gt (relativeModularVolumeShadow_pos (n := n) q q0)

/-- Finite modular operator realized as a genuine sheet automorphism. -/
@[rep_depth operator]
noncomputable def relativeModularSheetEquiv
    (q q0 : PositiveRay (Fin n)) : Efin ≃ₗ[ℝ] Efin :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n))
    (relativeModularOperator (n := n) q q0)
    (relativeModularOperator_det_isUnit (n := n) q q0)

theorem relativeModularSheetEquiv_toLinearMap
    (q q0 : PositiveRay (Fin n)) :
    ((relativeModularSheetEquiv (n := n) q q0 : Efin ≃ₗ[ℝ] Efin) : Efin →ₗ[ℝ] Efin)
      = Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
          (relativeModularOperator (n := n) q q0) := by
  rfl

theorem relativeModularSheetEquiv_det_coe_eq_volumeShadow
    (q q0 : PositiveRay (Fin n)) :
    ((LinearEquiv.det (relativeModularSheetEquiv (n := n) q q0)) : ℝ)
      = relativeModularVolumeShadow (n := n) q q0 := by
  rw [LinearEquiv.coe_det]
  rw [relativeModularSheetEquiv_toLinearMap]
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  rw [LinearMap.toMatrix_toLin]
  unfold relativeModularVolumeShadow
  rfl

/-- The doubled-sheet restricted character carried by plus/minus modular operators. -/
@[rep_depth operator]
noncomputable def relativeModularRestrictedSheetEquiv
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    RestrictedSheetEquiv Efin where
  plus := relativeModularSheetEquiv (n := n) qPlus q0Plus
  minus := relativeModularSheetEquiv (n := n) qMinus q0Minus

theorem relativeModularRestrictedSheetEquiv_character_coe_eq_berezinianShadow
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    (((RestrictedSheetEquiv.restrictedVolumeCharacter (E := Efin)
        (relativeModularRestrictedSheetEquiv (n := n) qPlus q0Plus qMinus q0Minus)) : ℝˣ) : ℝ)
      = relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus := by
  unfold RestrictedSheetEquiv.restrictedVolumeCharacter
    relativeModularRestrictedSheetEquiv relativeModularBerezinianShadow Base.VolumeHom
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv,
    relativeModularSheetEquiv_det_coe_eq_volumeShadow]

/--
The restricted-volume scalar on the doubled-sheet side is exactly the
Berezinian-style supervolume shadow of the modular operator owner.
-/
@[rep_depth transport, capstone]
theorem relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_berezinianShadow
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    RestrictedSheetEquiv.restrictedVolumeScale (E := Efin)
      (relativeModularRestrictedSheetEquiv (n := n) qPlus q0Plus qMinus q0Minus)
      = relativeModularBerezinianShadow (n := n) qPlus q0Plus qMinus q0Minus := by
  rw [RestrictedSheetEquiv.restrictedVolumeScale_eq_abs_character]
  rw [relativeModularRestrictedSheetEquiv_character_coe_eq_berezinianShadow]
  exact abs_of_pos (relativeModularBerezinianShadow_pos (n := n) qPlus q0Plus qMinus q0Minus)

/--
The negative logarithmic restricted-volume readout is exactly the modular
supervolume potential.
-/
@[rep_depth thermo, capstone]
theorem neg_log_relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_supervolumePotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    -Real.log
        (RestrictedSheetEquiv.restrictedVolumeScale (E := Efin)
          (relativeModularRestrictedSheetEquiv (n := n) qPlus q0Plus qMinus q0Minus))
      = relativeModularSupervolumePotential (n := n) qPlus q0Plus qMinus q0Minus := by
  rw [relativeModularRestrictedSheetEquiv_restrictedVolumeScale_eq_berezinianShadow]
  rfl

end Finite

section KreinHessianLift

variable {n : ℕ} [Nonempty (Fin n)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/--
Concrete quadratic operatorial lift of the finite relative modular supervolume
potential.

The finite Berezinian/supervolume potential anchors the value at the vacuum
`0`; the operatorial fluctuation is the repo-native indefinite quadratic
Krein potential.  This is the concrete lane where the second derivative is
proved, not merely carried as a hypothesis.
-/
@[rep_depth operator]
noncomputable def relativeModularSupervolumeKreinQuadraticPotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) (v : H₂) : ℝ :=
  relativeModularSupervolumePotential (n := n) qPlus q0Plus qMinus q0Minus
    + krein_potential (E := E) v

/-- Gradient of the concrete quadratic supervolume lift. -/
@[rep_depth operator]
noncomputable def relativeModularSupervolumeKreinGradient
    (_qPlus _q0Plus _qMinus _q0Minus : PositiveRay (Fin n)) (v : H₂) : H₂ :=
  krein_grad (E := E) v

/-- Constant Hessian operator of the concrete quadratic supervolume lift. -/
@[rep_depth operator]
noncomputable def relativeModularSupervolumeKreinHessian
    (_qPlus _q0Plus _qMinus _q0Minus : PositiveRay (Fin n)) : H₂ →L[ℝ] H₂ :=
  krein_hessian (E := E)

/-- The anchored quadratic lift has the finite supervolume value at the vacuum. -/
@[rep_depth operator]
theorem relativeModularSupervolumeKreinQuadraticPotential_zero
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) :
    relativeModularSupervolumeKreinQuadraticPotential
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus 0 =
      relativeModularSupervolumePotential (n := n) qPlus q0Plus qMinus q0Minus := by
  simp [relativeModularSupervolumeKreinQuadraticPotential,
    krein_potential, krein_form, InfoGeometry.Krein.hessian_indefinite_form,
    InfoGeometry.Krein.KreinSpace.kreinInner]

/-- The concrete quadratic supervolume lift differentiates to the Krein gradient. -/
@[rep_depth operator]
theorem hasFDerivAt_relativeModularSupervolumeKreinQuadraticPotential
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) (u : H₂) :
    HasFDerivAt
      (relativeModularSupervolumeKreinQuadraticPotential
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus)
      (InnerProductSpace.toDual ℝ H₂
        (relativeModularSupervolumeKreinGradient
          (n := n) (E := E) qPlus q0Plus qMinus q0Minus u))
      u := by
  let c : ℝ :=
    relativeModularSupervolumePotential (n := n) qPlus q0Plus qMinus q0Minus
  have hConst : HasFDerivAt (fun _ : H₂ => c) (0 : H₂ →L[ℝ] ℝ) u :=
    hasFDerivAt_const c u
  have hKrein := hasFDerivAt_krein_potential (E := E) u
  have hSum := hConst.add hKrein
  simpa [relativeModularSupervolumeKreinQuadraticPotential,
    relativeModularSupervolumeKreinGradient, c] using hSum

/--
The gradient of the concrete quadratic supervolume lift has constant derivative
equal to the Krein Hessian operator.
-/
@[rep_depth operator]
theorem hasFDerivAt_relativeModularSupervolumeKreinGradient
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) (u : H₂) :
    HasFDerivAt
      (relativeModularSupervolumeKreinGradient
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus)
      (relativeModularSupervolumeKreinHessian
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus)
      u := by
  simpa [relativeModularSupervolumeKreinGradient,
    relativeModularSupervolumeKreinHessian] using
    hasFDerivAt_krein_grad (E := E) u

/--
The Hessian bilinear readout of the concrete quadratic supervolume lift is the
Krein inner/Hessian form.
-/
@[rep_depth operator]
theorem relativeModularSupervolumeKreinHessian_bilin_eq_krein_form
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) (u v : H₂) :
    inner ℝ
        (relativeModularSupervolumeKreinHessian
          (n := n) (E := E) qPlus q0Plus qMinus q0Minus u) v =
      krein_form (E := E) u v := by
  rfl

/--
Concrete second-derivative packet: the anchored relative modular supervolume
potential has finite Berezinian value at the vacuum, Krein gradient as first
variation, and constant Krein Hessian as second variation.
-/
@[rep_depth operator]
theorem relativeModularSupervolume_concrete_secondDerivative_Krein_packet
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n)) (u v : H₂) :
    relativeModularSupervolumeKreinQuadraticPotential
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus 0 =
      relativeModularSupervolumePotential (n := n) qPlus q0Plus qMinus q0Minus
      ∧ HasFDerivAt
          (relativeModularSupervolumeKreinQuadraticPotential
            (n := n) (E := E) qPlus q0Plus qMinus q0Minus)
          (InnerProductSpace.toDual ℝ H₂
            (relativeModularSupervolumeKreinGradient
              (n := n) (E := E) qPlus q0Plus qMinus q0Minus u))
          u
      ∧ HasFDerivAt
          (relativeModularSupervolumeKreinGradient
            (n := n) (E := E) qPlus q0Plus qMinus q0Minus)
          (relativeModularSupervolumeKreinHessian
            (n := n) (E := E) qPlus q0Plus qMinus q0Minus)
          u
      ∧ inner ℝ
          (relativeModularSupervolumeKreinHessian
            (n := n) (E := E) qPlus q0Plus qMinus q0Minus u) v =
        krein_form (E := E) u v
      ∧ inner ℝ
          (relativeModularSupervolumeKreinHessian
            (n := n) (E := E) qPlus q0Plus qMinus q0Minus u) v =
        inner ℝ
          (relativeModularSupervolumeKreinHessian
            (n := n) (E := E) qPlus q0Plus qMinus q0Minus v) u := by
  exact
    ⟨relativeModularSupervolumeKreinQuadraticPotential_zero
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus,
      hasFDerivAt_relativeModularSupervolumeKreinQuadraticPotential
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus u,
      hasFDerivAt_relativeModularSupervolumeKreinGradient
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus u,
      relativeModularSupervolumeKreinHessian_bilin_eq_krein_form
        (n := n) (E := E) qPlus q0Plus qMinus q0Minus u v,
      by
        rw [relativeModularSupervolumeKreinHessian_bilin_eq_krein_form
          (n := n) (E := E) qPlus q0Plus qMinus q0Minus u v]
        rw [relativeModularSupervolumeKreinHessian_bilin_eq_krein_form
          (n := n) (E := E) qPlus q0Plus qMinus q0Minus v u]
        exact krein_form_symm (E := E) u v⟩

section HestenesRealDoubled

/--
Real doubled/Hestenes coordinate form of the concrete supervolume Hessian:
the Krein Hessian readout is exactly the split `(1,1)` bilinear form.
-/
@[rep_depth operator]
theorem relativeModularSupervolumeKreinHessian_realDoubled_eq_hestenes_splitB11
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n))
    (x ξ y η : ℝ) :
    inner ℝ
        (relativeModularSupervolumeKreinHessian
          (n := n) (E := ℝ) qPlus q0Plus qMinus q0Minus
          (InfoGeometry.Krein.to_doubled x ξ))
        (InfoGeometry.Krein.to_doubled y η)
      = InfoGeometry.Clifford.splitB11 (x, ξ) (y, η) := by
  rw [relativeModularSupervolumeKreinHessian_bilin_eq_krein_form]
  exact krein_form_to_doubled_real x ξ y η

/--
Diagonal Hestenes readout of the concrete supervolume Hessian: the self-pairing
is the split quadratic form `splitQ11`.
-/
@[rep_depth operator]
theorem relativeModularSupervolumeKreinHessian_realDoubled_diag_eq_hestenes_splitQ11
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n))
    (x ξ : ℝ) :
    inner ℝ
        (relativeModularSupervolumeKreinHessian
          (n := n) (E := ℝ) qPlus q0Plus qMinus q0Minus
          (InfoGeometry.Krein.to_doubled x ξ))
        (InfoGeometry.Krein.to_doubled x ξ)
      = InfoGeometry.Clifford.splitQ11 (x, ξ) := by
  rw [relativeModularSupervolumeKreinHessian_realDoubled_eq_hestenes_splitB11]
  simp [InfoGeometry.Clifford.splitQ11_apply, InfoGeometry.Clifford.splitB11_apply]

/--
The concrete supervolume lift in real doubled Hestenes coordinates is the finite
relative modular supervolume plus one half of the split quadratic form.
-/
@[rep_depth operator]
theorem relativeModularSupervolumeKreinQuadraticPotential_realDoubled_eq_hestenes_splitQ11
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n))
    (x ξ : ℝ) :
    relativeModularSupervolumeKreinQuadraticPotential
        (n := n) (E := ℝ) qPlus q0Plus qMinus q0Minus
        (InfoGeometry.Krein.to_doubled x ξ)
      =
        relativeModularSupervolumePotential (n := n) qPlus q0Plus qMinus q0Minus
          + (1 / 2 : ℝ) * InfoGeometry.Clifford.splitQ11 (x, ξ) := by
  simp [relativeModularSupervolumeKreinQuadraticPotential]

/--
Packed Hestenes/real-doubled translation of the concrete Pauli-audit lane:
quadratic potential, bilinear Hessian readout, and diagonal quadratic readout.
-/
@[rep_depth operator]
theorem relativeModularSupervolume_Hestenes_realDoubled_packet
    (qPlus q0Plus qMinus q0Minus : PositiveRay (Fin n))
    (x ξ y η : ℝ) :
    relativeModularSupervolumeKreinQuadraticPotential
        (n := n) (E := ℝ) qPlus q0Plus qMinus q0Minus
        (InfoGeometry.Krein.to_doubled x ξ)
      =
        relativeModularSupervolumePotential (n := n) qPlus q0Plus qMinus q0Minus
          + (1 / 2 : ℝ) * InfoGeometry.Clifford.splitQ11 (x, ξ)
      ∧ inner ℝ
          (relativeModularSupervolumeKreinHessian
            (n := n) (E := ℝ) qPlus q0Plus qMinus q0Minus
            (InfoGeometry.Krein.to_doubled x ξ))
          (InfoGeometry.Krein.to_doubled y η)
        = InfoGeometry.Clifford.splitB11 (x, ξ) (y, η)
      ∧ inner ℝ
          (relativeModularSupervolumeKreinHessian
            (n := n) (E := ℝ) qPlus q0Plus qMinus q0Minus
            (InfoGeometry.Krein.to_doubled x ξ))
          (InfoGeometry.Krein.to_doubled x ξ)
        = InfoGeometry.Clifford.splitQ11 (x, ξ) := by
  exact
    ⟨relativeModularSupervolumeKreinQuadraticPotential_realDoubled_eq_hestenes_splitQ11
        (n := n) qPlus q0Plus qMinus q0Minus x ξ,
      relativeModularSupervolumeKreinHessian_realDoubled_eq_hestenes_splitB11
        (n := n) qPlus q0Plus qMinus q0Minus x ξ y η,
      relativeModularSupervolumeKreinHessian_realDoubled_diag_eq_hestenes_splitQ11
        (n := n) qPlus q0Plus qMinus q0Minus x ξ⟩

end HestenesRealDoubled

/--
Proof-carrying lift from finite relative modular supervolume to the operatorial
Krein Hessian lane.

The analytic second variation of the Type-III/operatorial lift is not inferred
from the finite diagonal model.  A concrete modular-flow model must provide the
`secondVariation_eq_kreinInner` field, which says that its second variation is
the repo-native Krein Hessian form.  This structure then exposes the theorem
surface needed by Sinkhorn/Perelman-style metric consumers without pretending
to have constructed a trace-density Taylor series.
-/
@[rep_depth operator]
structure RelativeModularSupervolumeKreinHessianLift where
  qPlus : PositiveRay (Fin n)
  q0Plus : PositiveRay (Fin n)
  qMinus : PositiveRay (Fin n)
  q0Minus : PositiveRay (Fin n)
  /-- Projector/cut selecting the regular thermodynamic lane. -/
  drazinCut : H₂ →L[ℝ] H₂
  /-- Modular adjoint flow used to define the analytic continuation lane. -/
  modularAdjointFlow : ℝ → H₂ → H₂
  /-- Base point of the operatorial lift. -/
  basepoint : H₂
  /-- Lifted potential on the active regular lane. -/
  liftedSupervolumePotential : H₂ → ℝ
  /-- Bilinear second-variation readout of the lifted potential. -/
  secondVariation : H₂ → H₂ → ℝ
  /-- Metric used by downstream Sinkhorn/Perelman flow surfaces. -/
  sinkhornPerelmanMetric : H₂ → H₂ → ℝ
  /-- The lifted base value agrees with the finite modular supervolume owner. -/
  lifted_base_eq_relativeModularSupervolumePotential :
    liftedSupervolumePotential basepoint =
      relativeModularSupervolumePotential
        (n := n) qPlus q0Plus qMinus q0Minus
  /--
  The analytic second variation is the Krein Hessian form.
  This is the explicit noncommutative/operatorial hypothesis supplied by the
  modular-flow model.
  -/
  secondVariation_eq_kreinInner :
    ∀ u v : H₂, secondVariation u v = krein_form (E := E) u v
  /-- Downstream flow metric is exactly the second-variation readout. -/
  sinkhornPerelmanMetric_eq_secondVariation :
    ∀ u v : H₂, sinkhornPerelmanMetric u v = secondVariation u v

namespace RelativeModularSupervolumeKreinHessianLift

variable (C : RelativeModularSupervolumeKreinHessianLift (n := n) (E := E))

/-- The lifted base potential is the finite relative modular supervolume potential. -/
@[rep_depth operator]
theorem lifted_base_eq_supervolumePotential :
    C.liftedSupervolumePotential C.basepoint =
      relativeModularSupervolumePotential
        (n := n) C.qPlus C.q0Plus C.qMinus C.q0Minus :=
  C.lifted_base_eq_relativeModularSupervolumePotential

/--
The second variation of the lifted relative modular supervolume potential is
the repo-native Krein Hessian bilinear form.
-/
@[rep_depth operator]
theorem secondVariation_eq_symmetric_kreinInner (u v : H₂) :
    C.secondVariation u v = krein_form (E := E) u v :=
  C.secondVariation_eq_kreinInner u v

/-- The second-variation readout is symmetric because the Krein Hessian form is symmetric. -/
@[rep_depth operator]
theorem secondVariation_symmetric (u v : H₂) :
    C.secondVariation u v = C.secondVariation v u := by
  rw [C.secondVariation_eq_symmetric_kreinInner u v]
  rw [C.secondVariation_eq_symmetric_kreinInner v u]
  exact krein_form_symm (E := E) u v

/-- The downstream Sinkhorn/Perelman metric is the same Krein Hessian form. -/
@[rep_depth operator]
theorem sinkhornPerelmanMetric_eq_kreinInner (u v : H₂) :
    C.sinkhornPerelmanMetric u v = krein_form (E := E) u v := by
  rw [C.sinkhornPerelmanMetric_eq_secondVariation u v]
  exact C.secondVariation_eq_symmetric_kreinInner u v

/-- The downstream Sinkhorn/Perelman metric is symmetric on this lifted lane. -/
@[rep_depth operator]
theorem sinkhornPerelmanMetric_symmetric (u v : H₂) :
    C.sinkhornPerelmanMetric u v = C.sinkhornPerelmanMetric v u := by
  rw [C.sinkhornPerelmanMetric_eq_kreinInner u v]
  rw [C.sinkhornPerelmanMetric_eq_kreinInner v u]
  exact krein_form_symm (E := E) u v

/--
Packed Pauli-audit theorem: finite supervolume base value, second variation as
Krein Hessian, and Sinkhorn/Perelman metric compatibility.
-/
@[rep_depth operator]
theorem relativeModularSupervolume_secondVariation_Krein_packet
    (u v : H₂) :
    C.liftedSupervolumePotential C.basepoint =
        relativeModularSupervolumePotential
          (n := n) C.qPlus C.q0Plus C.qMinus C.q0Minus
      ∧ C.secondVariation u v = krein_form (E := E) u v
      ∧ C.secondVariation u v = C.secondVariation v u
      ∧ C.sinkhornPerelmanMetric u v = krein_form (E := E) u v
      ∧ C.sinkhornPerelmanMetric u v = C.sinkhornPerelmanMetric v u :=
  ⟨C.lifted_base_eq_supervolumePotential,
    C.secondVariation_eq_symmetric_kreinInner u v,
    C.secondVariation_symmetric u v,
    C.sinkhornPerelmanMetric_eq_kreinInner u v,
    C.sinkhornPerelmanMetric_symmetric u v⟩

/--
Compatibility shadow for the modular supervolume lane in split supergeometry
language.

The modular carrier remains the operatorial/Krein one; this is only a rename
layer exposing the new parity/supertrace vocabulary.
-/
structure SplitModularSupervolumeShadow where
  supervolumePotential : ℝ
  logBerezinianReg : ℝ
  parityTrace : ℝ
  parityTrace_eq_logBerezinian :
    parityTrace = logBerezinianReg

namespace SplitModularSupervolumeShadow

@[simp]
theorem parityTrace_eq_logBerezinianReg
    (S : SplitModularSupervolumeShadow) :
    S.parityTrace = S.logBerezinianReg :=
  S.parityTrace_eq_logBerezinian

end SplitModularSupervolumeShadow

end RelativeModularSupervolumeKreinHessianLift

end KreinHessianLift

end InfoGeometry.Canonical.RelativeModularBerezinianBridge
