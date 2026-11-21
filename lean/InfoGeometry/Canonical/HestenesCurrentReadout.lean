/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesClPlus14
import InfoGeometry.Riemannian.CartanMetric

/-!
# Calibrated scalar and time readout in the native real spacetime algebra

The existing `InfoGeometry.Riemannian.hTrace_cl` is the scalar readout: it
composes Mathlib's Clifford/exterior linear equivalence with the exterior
augmentation. We reuse that owner rather than introducing another scalar-part
definition. Its value on a product of two included vectors is the associated
bilinear form of the actual quadratic form `Q14` of signature `(+---)`.

Right multiplication by the actual timelike Clifford generator `gamma 0`
therefore gives a real linear functional whose value on `ι14 v` is exactly
`v 0`. Neither the Clifford product nor the vector inclusion is replaced by
coordinatewise scalar multiplication. No full Clifford basis, matrix
representation, current positivity, or dynamics is assumed here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesCurrentReadout

open HestenesCl14
open InfoGeometry.Riemannian

/-- The existing scalar readout has the normalization of a scalar coefficient. -/
@[simp] theorem scalar_algebraMap (r : ℝ) :
    hTrace_cl Q14 (algebraMap ℝ Cl14 r) = r := by
  change (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℝ V14 →ₐ[ℝ] ℝ)
    (CliffordAlgebra.equivExterior Q14 (algebraMap ℝ Cl14 r)) = r
  simp [CliffordAlgebra.equivExterior, ExteriorAlgebra.algebraMapInv]

@[simp] theorem scalar_zero : hTrace_cl Q14 (0 : Cl14) = 0 :=
  map_zero (hTrace_cl Q14)

@[simp] theorem scalar_one : hTrace_cl Q14 (1 : Cl14) = 1 := by
  simpa only [map_one] using scalar_algebraMap 1

theorem scalar_add (X Y : Cl14) :
    hTrace_cl Q14 (X + Y) = hTrace_cl Q14 X + hTrace_cl Q14 Y :=
  map_add (hTrace_cl Q14) X Y

theorem scalar_smul (r : ℝ) (X : Cl14) :
    hTrace_cl Q14 (r • X) = r * hTrace_cl Q14 X :=
  map_smul (hTrace_cl Q14) r X

/-- Every included vector has zero scalar coefficient. -/
@[simp] theorem scalar_iota (v : V14) : hTrace_cl Q14 (ι14 v) = 0 := by
  change (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℝ V14 →ₐ[ℝ] ℝ)
    (CliffordAlgebra.equivExterior Q14 (ι14 v)) = 0
  simp [CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm_ι,
    ExteriorAlgebra.algebraMapInv]

/-- Clifford multiplication contributes precisely the native contraction term
to the scalar coefficient of a product of two vectors. -/
theorem scalar_iota_mul_iota (v w : V14) :
    hTrace_cl Q14 (ι14 v * ι14 w) = QuadraticMap.associated Q14 v w := by
  change (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra ℝ V14 →ₐ[ℝ] ℝ)
    (CliffordAlgebra.changeForm
      (CliffordAlgebra.changeForm.associated_neg_proof (Q := Q14))
      (ι14 v * ι14 w)) = QuadraticMap.associated Q14 v w
  rw [CliffordAlgebra.changeForm_ι_mul_ι, map_sub, map_mul]
  simp [ExteriorAlgebra.algebraMapInv]

/-- Polarization computes the full Lorentzian pairing on the existing carrier. -/
theorem associated_Q14_apply (v w : V14) :
    QuadraticMap.associated Q14 v w =
      v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3 := by
  have hp := congrArg (fun B : LinearMap.BilinForm ℝ V14 => B v w)
    (QuadraticMap.two_nsmul_associated ℝ Q14)
  simp only [two_smul, LinearMap.add_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar] at hp
  have hq : Q14 (v + w) - Q14 v - Q14 w =
      2 * (v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3) := by
    simp [Q14_apply, qCoeff, Fin.sum_univ_succ]
    ring
  rw [hq] at hp
  linarith only [hp]

/-- Explicit scalar coefficient of an ordered native Clifford product. -/
theorem scalar_iota_mul_iota_coordinates (v w : V14) :
    hTrace_cl Q14 (ι14 v * ι14 w) =
      v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3 := by
  rw [scalar_iota_mul_iota, associated_Q14_apply]

/-- Time readout uses right Clifford multiplication by the existing `gamma 0`. -/
def timeCoefficient : Cl14 →ₗ[ℝ] ℝ :=
  (hTrace_cl Q14).comp (LinearMap.mulRight ℝ (gamma 0))

theorem timeCoefficient_apply (X : Cl14) :
    timeCoefficient X = hTrace_cl Q14 (X * gamma 0) := rfl

@[simp] theorem timeCoefficient_zero : timeCoefficient (0 : Cl14) = 0 :=
  map_zero timeCoefficient

theorem timeCoefficient_add (X Y : Cl14) :
    timeCoefficient (X + Y) = timeCoefficient X + timeCoefficient Y :=
  map_add timeCoefficient X Y

theorem timeCoefficient_smul (r : ℝ) (X : Cl14) :
    timeCoefficient (r • X) = r * timeCoefficient X :=
  map_smul timeCoefficient r X

theorem timeCoefficient_sub (X Y : Cl14) :
    timeCoefficient (X - Y) = timeCoefficient X - timeCoefficient Y :=
  map_sub timeCoefficient X Y

/-- Calibration on every spacetime vector, not merely on basis generators. -/
@[simp] theorem timeCoefficient_iota (v : V14) :
    timeCoefficient (ι14 v) = v 0 := by
  change hTrace_cl Q14 (ι14 v * ι14 (basisVec 0)) = v 0
  rw [scalar_iota_mul_iota_coordinates]
  simp [basisVec]

/-- The same calibration as an identity between native linear maps. -/
theorem timeCoefficient_comp_iota :
    timeCoefficient.comp ι14 = coord4 0 := by
  exact LinearMap.ext timeCoefficient_iota

/-- The timelike generator has coefficient one; every spacelike generator has zero. -/
@[simp] theorem timeCoefficient_gamma (i : Fin 4) :
    timeCoefficient (gamma i) = if i = 0 then 1 else 0 := by
  rw [gamma, timeCoefficient_iota]
  simp [basisVec, eq_comm]

/-- A scalar has no time-vector coefficient. -/
@[simp] theorem timeCoefficient_one : timeCoefficient (1 : Cl14) = 0 := by
  change hTrace_cl Q14 (1 * gamma 0) = 0
  rw [one_mul]
  exact scalar_iota (basisVec 0)

/-- The calibrated time readout is a nonzero functional. -/
theorem timeCoefficient_ne_zero : timeCoefficient ≠ 0 := by
  intro h
  have hg := congrArg (fun f : Cl14 →ₗ[ℝ] ℝ => f (gamma 0)) h
  norm_num at hg

end InfoGeometry.Canonical.HestenesCurrentReadout

end
