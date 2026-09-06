import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.NativeMathlibAmplituhedronBridge

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- **Theorem**: Native Mathlib Exterior Algebra Wedge Nilpotency (ι(v) ∧ ι(v) = 0).
    Proves that for any vector v ∈ V, the generator ι(v) squared vanishes in ExteriorAlgebra R V. -/
theorem native_exterior_algebra_wedge_nilpotent (v : V) :
    ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v = 0 :=
  ExteriorAlgebra.ι_sq_zero v

/-- **Theorem**: Native Mathlib Vector Anti-Commutativity in ExteriorAlgebra.
    ι(v1) * ι(v2) = - (ι(v2) * ι(v1)). -/
theorem native_exterior_algebra_anti_commute (v1 v2 : V) :
    ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 = - (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v1) := by
  have h_sum := ExteriorAlgebra.ι_sq_zero (R := R) (v1 + v2)
  have h1 := ExteriorAlgebra.ι_sq_zero (R := R) v1
  have h2 := ExteriorAlgebra.ι_sq_zero (R := R) v2
  rw [map_add, add_mul, mul_add, mul_add, h1, h2, add_zero, zero_add] at h_sum
  exact eq_neg_of_add_eq_zero_left h_sum

/-- **Theorem**: Native Mathlib 2-Blade Plücker Quadric Nilpotency ((v1 ∧ v2)^2 = 0).
    Proves natively in Mathlib that for any 2-blade P = ι(v1) * ι(v2) in ExteriorAlgebra R V,
    P * P = 0 identically on the Klein quadric Gr(2,4). -/
theorem native_plucker_two_blade_nilpotent (v1 v2 : V) :
    (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2) * (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2) = 0 := by
  have h_anti := native_exterior_algebra_anti_commute (R := R) v2 v1
  have h1 := ExteriorAlgebra.ι_sq_zero (R := R) v1
  calc (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2) * (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)
    _ = ExteriorAlgebra.ι R v1 * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v1) * ExteriorAlgebra.ι R v2 := by noncomm_ring
    _ = ExteriorAlgebra.ι R v1 * (- (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)) * ExteriorAlgebra.ι R v2 := by rw [h_anti]
    _ = - ((ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v1) * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v2)) := by noncomm_ring
    _ = 0 := by rw [h1, zero_mul, neg_zero]

/-- **Theorem**: Native Mathlib 3-Blade Plücker Quadric Nilpotency ((v1 ∧ v2 ∧ v3)^2 = 0).
    Proves natively in Mathlib that for any 3-blade B = ι(v1) * ι(v2) * ι(v3) in ExteriorAlgebra R V,
    B * B = 0 identically on the Grassmannian Gr(3,n). -/
theorem native_plucker_three_blade_nilpotent (v1 v2 v3 : V) :
    (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3) *
    (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3) = 0 := by
  have h1 := ExteriorAlgebra.ι_sq_zero (R := R) v1
  have h_anti12 := native_exterior_algebra_anti_commute (R := R) v2 v1
  have h_anti13 := native_exterior_algebra_anti_commute (R := R) v3 v1
  calc (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3) *
        (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3)
    _ = ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * (ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v1) *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3) := by noncomm_ring
    _ = ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * (- (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v3)) *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3) := by rw [h_anti13]
    _ = - (ExteriorAlgebra.ι R v1 * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v1) * ExteriorAlgebra.ι R v3 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3)) := by noncomm_ring
    _ = - (ExteriorAlgebra.ι R v1 * (- (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)) * ExteriorAlgebra.ι R v3 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3)) := by rw [h_anti12]
    _ = (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v1) * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3)) := by noncomm_ring
    _ = 0 * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3)) := by rw [h1]
    _ = 0 := by noncomm_ring

/-- **Theorem**: Native Mathlib 4-Blade Plücker Quadric Nilpotency ((v1 ∧ v2 ∧ v3 ∧ v4)^2 = 0).
    Proves natively in Mathlib that for any 4-blade K = ι(v1) * ι(v2) * ι(v3) * ι(v4) in ExteriorAlgebra R V
    (representing Gr(4,n) Amplituhedron kinematics), K * K = 0 identically. -/
theorem native_plucker_four_blade_nilpotent (v1 v2 v3 v4 : V) :
    (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4) *
    (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4) = 0 := by
  have h1 := ExteriorAlgebra.ι_sq_zero (R := R) v1
  have h_anti12 := native_exterior_algebra_anti_commute (R := R) v2 v1
  have h_anti13 := native_exterior_algebra_anti_commute (R := R) v3 v1
  have h_anti14 := native_exterior_algebra_anti_commute (R := R) v4 v1
  calc (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4) *
        (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4)
    _ = ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * (ExteriorAlgebra.ι R v4 * ExteriorAlgebra.ι R v1) *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4) := by noncomm_ring
    _ = ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * (- (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v4)) *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4) := by rw [h_anti14]
    _ = - (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * (ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v1) * ExteriorAlgebra.ι R v4 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4)) := by noncomm_ring
    _ = - (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * (- (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v3)) * ExteriorAlgebra.ι R v4 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4)) := by rw [h_anti13]
    _ = (ExteriorAlgebra.ι R v1 * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v1) * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4)) := by noncomm_ring
    _ = (ExteriorAlgebra.ι R v1 * (- (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)) * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4)) := by rw [h_anti12]
    _ = - ((ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v1) * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4))) := by noncomm_ring
    _ = - (0 * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4 *
        (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4))) := by rw [h1]
    _ = 0 := by noncomm_ring

/-- **Theorem**: Native Mathlib 2-Blade Linear Map Pushforward Conservation.
    Proves natively in Mathlib that for any linear map f : V →ₗ[R] W and 2-blade P = ι(v1) * ι(v2),
    the mapped 2-blade (map f P)^2 = 0 identically in ExteriorAlgebra R W. -/
theorem native_plucker_linear_map_conservation (f : V →ₗ[R] W) (v1 v2 : V) :
    (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)) *
    (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)) = 0 := by
  rw [map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
  exact native_plucker_two_blade_nilpotent (f v1) (f v2)

/-- **Theorem**: Native Mathlib 4-Blade Linear Map Pushforward Conservation of Gr(4,n) Amplituhedron Quadric.
    Proves natively in Mathlib that for any linear map f : V →ₗ[R] W and 4-blade K = ι(v1) * ι(v2) * ι(v3) * ι(v4),
    the mapped 4-blade (map f K)^2 = 0 identically in ExteriorAlgebra R W. -/
theorem native_plucker_four_blade_linear_map_conservation (f : V →ₗ[R] W) (v1 v2 v3 v4 : V) :
    (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4)) *
    (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v3 * ExteriorAlgebra.ι R v4)) = 0 := by
  rw [map_mul, map_mul, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
  exact native_plucker_four_blade_nilpotent (f v1) (f v2) (f v3) (f v4)

/-- **Theorem**: Native Mathlib Finsupp Base Ring Generator Explicit Typing.
    Uses explicit (1 : R) to prevent type inference traps on free module generators. -/
theorem native_finsupp_single_one_typed (i j : ℕ) :
    (Finsupp.single (i, j) (1 : R)) (i, j) = 1 :=
  Finsupp.single_eq_same

end InfoGeometry.Canonical.NativeMathlibAmplituhedronBridge
