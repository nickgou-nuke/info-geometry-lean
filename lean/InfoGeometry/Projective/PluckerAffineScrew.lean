/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.KleinQuadricPlucker
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.DualNumber

/-!
# Affine Plücker lines and the canonical screw decomposition

The existing six Plücker coordinates are read as direction
`(p01,p02,p03)` and moment `(p23,-p13,p12)`. For each nonzero real direction
`d`, the moment space is linearly equivalent to the product of the plane
orthogonal to `d` and the real pitch coordinate. The inverse sends `(p,h)`
to `p × d + h d`; the forward map constructs the perpendicular axis point.

These are Euclidean affine-line and screw statements in real dimension three.
The projective choice of scale and orientation, a tangent-bundle topology,
and a Lorentzian twistor or physical mass interpretation are separate data.
-/

noncomputable section

namespace InfoGeometry.Projective.PluckerAffineScrew

open Matrix
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.KleinQuadricPlucker.Plucker6
open scoped Matrix

abbrev Vec3 := Fin 3 → ℝ

/-- The direction/moment convention for the existing Plücker carrier. -/
def directionMomentEquiv : Plucker6 ℝ ≃ Vec3 × Vec3 where
  toFun P := (![P.p01, P.p02, P.p03], ![P.p23, -P.p13, P.p12])
  invFun x := ⟨x.1 0, x.1 1, x.1 2, x.2 2, -x.2 1, x.2 0⟩
  left_inv P := by cases P; simp
  right_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp

/-- The Klein equation is the direction/moment pairing in this convention. -/
theorem kleinQ_directionMoment (d m : Vec3) :
    kleinQ (directionMomentEquiv.symm (d, m)) = d ⬝ᵥ m := by
  simp [directionMomentEquiv, kleinQ, dotProduct, Fin.sum_univ_three]

/-- The moment is the cross product of an actual affine point with its direction. -/
theorem affineLine_plucker (p d : Vec3) :
    pluckerLine ⟨1, p 0, p 1, p 2⟩ ⟨0, d 0, d 1, d 2⟩ =
      directionMomentEquiv.symm (d, p ⨯₃ d) := by
  apply Plucker6.ext <;> simp [pluckerLine, directionMomentEquiv, cross_apply]

/-- Native kernel submodule of the covector given by dot product with `d`. -/
def normalPlane (d : Vec3) : Submodule ℝ Vec3 :=
  LinearMap.ker (dotProductBilin ℝ ℝ d)

@[simp] theorem mem_normalPlane (d p : Vec3) :
    p ∈ normalPlane d ↔ d ⬝ᵥ p = 0 := Iff.rfl

/-- Pitch is a linear functional of the moment for fixed direction.
Its geometric use below assumes `d ≠ 0`. -/
def pitch (d : Vec3) : Vec3 →ₗ[ℝ] ℝ :=
  (d ⬝ᵥ d)⁻¹ • dotProductBilin ℝ ℝ d

theorem pitch_apply (d m : Vec3) :
    pitch d m = (d ⬝ᵥ m) / (d ⬝ᵥ d) := by
  simp [pitch, div_eq_mul_inv, mul_comm]

/-- The canonical point of the screw axis in the plane orthogonal to `d`. -/
def axisFoot (d : Vec3) : Vec3 →ₗ[ℝ] normalPlane d :=
  ((d ⬝ᵥ d)⁻¹ • crossProduct d).codRestrict (normalPlane d) (by
    intro m
    simp [normalPlane, LinearMap.mem_ker])

@[simp] theorem axisFoot_coe (d m : Vec3) :
    (axisFoot d m : Vec3) = (d ⬝ᵥ d)⁻¹ • (d ⨯₃ m) := rfl

theorem direction_normSq_ne_zero {d : Vec3} (hd : d ≠ 0) : d ⬝ᵥ d ≠ 0 := by
  simpa using hd

/-- The axial component is exactly the obstruction to a pure line moment. -/
theorem axisFoot_cross (d m : Vec3) (hd : d ≠ 0) :
    (axisFoot d m : Vec3) ⨯₃ d = m - pitch d m • d := by
  have hn := direction_normSq_ne_zero hd
  rw [axisFoot_coe, LinearMap.map_smul₂, cross_cross_eq_smul_sub_smul,
    smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]
  simp [pitch, dotProduct_comm, smul_smul]

/-- The reconstructed moment has the specified pitch. -/
theorem pitch_reconstruct (d p : Vec3) (h : ℝ) (hd : d ≠ 0) :
    pitch d (p ⨯₃ d + h • d) = h := by
  have hn := direction_normSq_ne_zero hd
  simp [pitch, dotProduct_add, dot_cross_self, mul_left_comm, hn]

/-- Reconstruction recovers the specified perpendicular axis point. -/
theorem axisFoot_reconstruct (d : Vec3) (p : normalPlane d) (h : ℝ)
    (hd : d ≠ 0) :
    axisFoot d ((p : Vec3) ⨯₃ d + h • d) = p := by
  have hn := direction_normSq_ne_zero hd
  have hp : (p : Vec3) ⬝ᵥ d = 0 := by
    rw [dotProduct_comm]
    exact p.property
  apply Subtype.ext
  simp [axisFoot_coe, map_add, map_smul, cross_self,
    cross_cross_eq_smul_sub_smul', hp, smul_smul, hn]

/-- The full fixed-direction moment space, with explicit forward and inverse maps.
No existence or inverse law is supplied as an assumption. -/
def screwDecomposition (d : Vec3) (hd : d ≠ 0) :
    Vec3 ≃ₗ[ℝ] normalPlane d × ℝ where
  toFun m := (axisFoot d m, pitch d m)
  invFun x := (x.1 : Vec3) ⨯₃ d + x.2 • d
  left_inv m := by
    change (axisFoot d m : Vec3) ⨯₃ d + pitch d m • d = m
    rw [axisFoot_cross d m hd]
    abel
  right_inv x := by
    apply Prod.ext
    · exact axisFoot_reconstruct d x.1 x.2 hd
    · exact pitch_reconstruct d x.1 x.2 hd
  map_add' m n := by simp
  map_smul' a m := by simp

/-- A moment determines a unique perpendicular axis point and pitch. -/
theorem existsUnique_axis_pitch (d m : Vec3) (hd : d ≠ 0) :
    ∃! x : normalPlane d × ℝ, (x.1 : Vec3) ⨯₃ d + x.2 • d = m := by
  refine ⟨screwDecomposition d hd m, ?_, ?_⟩
  · exact (screwDecomposition d hd).symm_apply_apply m
  · intro x hx
    exact (screwDecomposition d hd).symm.injective
      (hx.trans ((screwDecomposition d hd).symm_apply_apply m).symm)

/-- Exactly the zero-pitch screws lie on the Klein quadric when `d ≠ 0`. -/
theorem pitch_eq_zero_iff_klein (d m : Vec3) (hd : d ≠ 0) :
    pitch d m = 0 ↔ kleinQ (directionMomentEquiv.symm (d, m)) = 0 := by
  rw [pitch_apply, kleinQ_directionMoment]
  simp [direction_normSq_ne_zero hd]

/-- The nonzero-direction Klein locus consists precisely of actual affine lines. -/
theorem klein_iff_exists_affine_point (d m : Vec3) (hd : d ≠ 0) :
    kleinQ (directionMomentEquiv.symm (d, m)) = 0 ↔ ∃ p : Vec3, p ⨯₃ d = m := by
  constructor
  · intro h
    refine ⟨axisFoot d m, ?_⟩
    rw [axisFoot_cross d m hd, (pitch_eq_zero_iff_klein d m hd).mpr h,
      zero_smul, sub_zero]
  · rintro ⟨p, rfl⟩
    rw [kleinQ_directionMoment]
    exact dot_cross_self p d

/-- Active translation by `t` preserves the pitch, including the totalized `d = 0` case. -/
theorem pitch_translation (d m t : Vec3) :
    pitch d (m + t ⨯₃ d) = pitch d m := by
  simp [pitch, dotProduct_add]

/-- Pitch is independent of the nonzero projective scale of a screw. -/
theorem pitch_scale (d m : Vec3) (a : ℝ) (hd : d ≠ 0) (ha : a ≠ 0) :
    pitch (a • d) (a • m) = pitch d m := by
  rw [pitch_apply, pitch_apply]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp [ha, direction_normSq_ne_zero hd]

/-- The perpendicular axis point also survives common projective rescaling. -/
theorem axisFoot_scale (d m : Vec3) (a : ℝ) (hd : d ≠ 0) (ha : a ≠ 0) :
    (axisFoot (a • d) (a • m) : Vec3) = (axisFoot d m : Vec3) := by
  change ((a • d) ⬝ᵥ (a • d))⁻¹ • ((a • d) ⨯₃ (a • m)) =
    (d ⬝ᵥ d)⁻¹ • (d ⨯₃ m)
  rw [LinearMap.map_smul₂, map_smul]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_smul]
  congr 1
  field_simp [ha, direction_normSq_ne_zero hd]

/-- Translation shifts the axis point by the component of `t` orthogonal to `d`. -/
theorem axisFoot_translation (d m t : Vec3) (hd : d ≠ 0) :
    (axisFoot d (m + t ⨯₃ d) : Vec3) =
      (axisFoot d m : Vec3) + t - pitch d t • d := by
  have hn := direction_normSq_ne_zero hd
  change (d ⬝ᵥ d)⁻¹ • (d ⨯₃ (m + t ⨯₃ d)) =
    (d ⬝ᵥ d)⁻¹ • (d ⨯₃ m) + t - pitch d t • d
  simp only [map_add, cross_cross_eq_smul_sub_smul',
    smul_add, smul_sub, smul_smul, inv_mul_cancel₀ hn, one_smul]
  simp [pitch, dotProduct_comm, sub_eq_add_neg, add_assoc]

/-- The real dual-number encoding uses Mathlib's genuine square-zero extension. -/
def dualVector (d m : Vec3) : Fin 3 → DualNumber ℝ :=
  fun i => TrivSqZeroExt.inl (d i) + TrivSqZeroExt.inr (m i)

/-- The dual dot square, not the square of a pure quaternion, records the Klein defect. -/
theorem dualVector_dot_self (d m : Vec3) :
    dualVector d m ⬝ᵥ dualVector d m =
      TrivSqZeroExt.inl (d ⬝ᵥ d) + TrivSqZeroExt.inr (2 * (d ⬝ᵥ m)) := by
  apply TrivSqZeroExt.ext <;>
    simp [dualVector, dotProduct, Fin.sum_univ_three]
  ring

/-- Unit dual vectors encode exactly the unit-direction Klein locus. -/
theorem dualVector_dot_self_eq_one_iff (d m : Vec3) :
    dualVector d m ⬝ᵥ dualVector d m = 1 ↔
      d ⬝ᵥ d = 1 ∧ kleinQ (directionMomentEquiv.symm (d, m)) = 0 := by
  rw [dualVector_dot_self, kleinQ_directionMoment]
  constructor
  · intro h
    have hfst := congrArg TrivSqZeroExt.fst h
    have hsnd := congrArg TrivSqZeroExt.snd h
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.fst_one] at hfst
    simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add, TrivSqZeroExt.snd_one] at hsnd
    exact ⟨hfst, by linarith⟩
  · rintro ⟨hn, hk⟩
    apply TrivSqZeroExt.ext <;> simp [hn, hk]

end InfoGeometry.Projective.PluckerAffineScrew
