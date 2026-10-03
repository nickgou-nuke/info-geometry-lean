import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Exterior-algebra generators and decomposable blades

The owner-level facts here are alternation of the universal exterior
generators, square-zero of decomposable positive-grade blades, naturality
under linear maps, and a typed `Finsupp.single` evaluation. These algebraic
facts do not identify an exterior square-zero equation with a Klein
decomposability condition, a Minkowski mass shell, or an amplituhedron.

An earlier conjunction called a master amplituhedron synthesis merely
collected these unrelated facts. Its intended useful content remains in the
individual theorems below; no theorem connecting those separate carriers is
asserted.
-/

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

/-- The square of a decomposable exterior 2-vector vanishes.  The proof uses
    the repeated exterior generators and their alternating product.  When the
    carrier is four-dimensional, this identity reads as the Klein/Plücker
    equation under the coordinate identification; this theorem itself is an
    exterior-algebra statement for arbitrary `V`, not a momentum mass-shell
    assertion. -/
theorem native_plucker_two_blade_nilpotent (v1 v2 : V) :
    (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2) * (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2) = 0 := by
  have h_anti := native_exterior_algebra_anti_commute (R := R) v2 v1
  have h1 := ExteriorAlgebra.ι_sq_zero (R := R) v1
  calc (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2) * (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)
    _ = ExteriorAlgebra.ι R v1 * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v1) * ExteriorAlgebra.ι R v2 := by noncomm_ring
    _ = ExteriorAlgebra.ι R v1 * (- (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)) * ExteriorAlgebra.ι R v2 := by rw [h_anti]
    _ = - ((ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v1) * (ExteriorAlgebra.ι R v2 * ExteriorAlgebra.ι R v2)) := by noncomm_ring
    _ = 0 := by rw [h1, zero_mul, neg_zero]

/-- The square of a decomposable exterior 3-vector vanishes, by alternation
    and the repeated generators.  This is not the Klein quadric equation (which
    is a degree-two Plücker relation for 2-vectors), nor an octonion
    associator identity. -/
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

/-- Every positive-grade decomposable element generated by `ιMulti` has
    square zero in the exterior algebra. This is a uniform finite-grade
    exterior-product theorem; it does not say that arbitrary bivectors square
    to zero, nor does it identify the exterior square with a Minkowski shell. -/
theorem native_decomposable_exterior_blade_square_zero
    (n : ℕ) (v : Fin (n + 1) → V) :
    ExteriorAlgebra.ιMulti R (n + 1) v * ExteriorAlgebra.ιMulti R (n + 1) v = 0 := by
  let doubled : Fin ((n + 1) + (n + 1)) → V := Fin.append v v
  have hzero : ExteriorAlgebra.ιMulti R ((n + 1) + (n + 1)) doubled = 0 := by
    apply AlternatingMap.map_eq_zero_of_eq
        (ExteriorAlgebra.ιMulti R ((n + 1) + (n + 1))) doubled
        (i := Fin.castAdd (n + 1) (0 : Fin (n + 1)))
        (j := Fin.natAdd (n + 1) (0 : Fin (n + 1)))
    · simp only [doubled, Fin.append_left, Fin.append_right]
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
  have hprod : ExteriorAlgebra.ιMulti R ((n + 1) + (n + 1)) doubled =
      ExteriorAlgebra.ιMulti R (n + 1) v * ExteriorAlgebra.ιMulti R (n + 1) v := by
    calc
      _ = (List.ofFn fun i => ExteriorAlgebra.ι R (doubled i)).prod :=
        ExteriorAlgebra.ιMulti_apply doubled
      _ = (List.ofFn fun i => ExteriorAlgebra.ι R (v i)).prod *
          (List.ofFn fun i => ExteriorAlgebra.ι R (v i)).prod := by
        rw [List.ofFn_add, List.prod_append]
        simp only [doubled, Fin.append_left', Fin.append_right]
      _ = _ := by rfl
  rw [← hprod, hzero]

/-- **Theorem**: Native Mathlib 2-Blade Linear Map Pushforward Conservation.
    Proves natively in Mathlib that for any linear map f : V →ₗ[R] W and 2-blade P = ι(v1) * ι(v2),
    the mapped 2-blade (map f P)^2 = 0 identically in ExteriorAlgebra R W. -/
theorem native_plucker_linear_map_conservation (f : V →ₗ[R] W) (v1 v2 : V) :
    (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)) *
    (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v1 * ExteriorAlgebra.ι R v2)) = 0 := by
  rw [map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
  exact native_plucker_two_blade_nilpotent (f v1) (f v2)

/-- **Theorem**: Native Mathlib Finsupp Base Ring Generator Explicit Typing.
    Uses explicit (1 : R) to prevent type inference traps on free module generators. -/
theorem native_finsupp_single_one_typed (i j : ℕ) :
    (Finsupp.single (i, j) (1 : R)) (i, j) = 1 :=
  Finsupp.single_eq_same

end InfoGeometry.Canonical.NativeMathlibAmplituhedronBridge
