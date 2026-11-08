import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic

/-!
# Alternating exterior blades

This file works in Mathlib's associative exterior algebra over an arbitrary
commutative ring. Its products are exterior products of vector generators:
they are not Clifford products, split-octonion products, or nonassociative
associators. In particular, the square-zero result below is the forward
identity for a decomposable bivector; it is not a Minkowski mass-shell
condition. The four-dimensional converse to decomposability is owned by
`InfoGeometry.Projective.ExteriorPowerPluckerBridge`, and the Minkowski
mass-shell readout by `InfoGeometry.Physics.FourVectorDiracReadout`. The
3-blades and 4-blades here are alternating products in an associative algebra;
they are not octonion associators, Jacobiators, or R-flux tensors.
-/
namespace InfoGeometry.GrassmannianTower

variable (R : Type*) [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

open ExteriorAlgebra

def blade_two (u v : V) : ExteriorAlgebra R V :=
  ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v

/-- Multiplying a decomposable exterior bivector by its second generator
vanishes because that generator occurs twice in the alternating product. -/
theorem blade_two_mul_repeated_right_zero (u v : V) :
    blade_two R u v * ExteriorAlgebra.ι R v = 0 := by
  dsimp [blade_two]
  calc
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v =
        ExteriorAlgebra.ι R u *
          (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v) := by
          simp only [mul_assoc]
    _ = ExteriorAlgebra.ι R u * 0 := by rw [ExteriorAlgebra.ι_sq_zero]
    _ = 0 := by simp

/-- Multiplying a decomposable exterior bivector on the left by its first
generator vanishes because that generator occurs twice. -/
theorem blade_two_mul_repeated_left_zero (u v : V) :
    ExteriorAlgebra.ι R u * blade_two R u v = 0 := by
  dsimp [blade_two]
  calc
    ExteriorAlgebra.ι R u *
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) =
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R u) *
          ExteriorAlgebra.ι R v := by
          simp only [mul_assoc]
    _ = 0 * ExteriorAlgebra.ι R v := by rw [ExteriorAlgebra.ι_sq_zero]
    _ = 0 := by simp

/-! A `blade_three` is an exterior product of three vector generators. Its
alternation is the defining Grassmann sign rule, not a non-associative defect. -/
def blade_three (u v w : V) : ExteriorAlgebra R V :=
  ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w

theorem blade_three_repeated_first_generator_zero (u v : V) :
    blade_three R u u v = 0 := by
  dsimp [blade_three]
  have h : ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R u *
      ExteriorAlgebra.ι R v =
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R u) *
        ExteriorAlgebra.ι R v := by simp only [mul_assoc]
  rw [h, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem blade_three_repeated_last_generator_zero (u v : V) :
    blade_three R u v v = 0 := by
  dsimp [blade_three]
  rw [mul_assoc, ExteriorAlgebra.ι_sq_zero, mul_zero]

theorem blade_three_swap_first_two (u v w : V) :
    blade_three R u v w = - blade_three R v u w := by
  dsimp [blade_three]
  have hswap : ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v =
      -(ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u) := by
    exact eq_neg_of_add_eq_zero_left
      (ExteriorAlgebra.ι_add_mul_swap (R := R) u v)
  rw [hswap, neg_mul]

/-- Swapping the last two generators of a 3-blade reverses its orientation.
Together with `blade_three_swap_first_two`, this gives the adjacent
transpositions generating the full alternating action on three inputs. -/
theorem blade_three_swap_last_two (u v w : V) :
    blade_three R u v w = - blade_three R u w v := by
  dsimp [blade_three]
  have hswap : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
      -(ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v) := by
    exact eq_neg_of_add_eq_zero_left
      (ExteriorAlgebra.ι_add_mul_swap (R := R) v w)
  calc
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
        ExteriorAlgebra.ι R u *
          (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w) := by
            rw [mul_assoc]
    _ = ExteriorAlgebra.ι R u *
        (-(ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v)) := by rw [hswap]
    _ = -(ExteriorAlgebra.ι R u *
        (ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R v)) := by rw [mul_neg]
    _ = -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R w *
        ExteriorAlgebra.ι R v) := by rw [mul_assoc]

/-- The transposition of the first and third inputs is odd. This follows by
composing the two adjacent transpositions, so the exterior-algebra sign rule
does not require a separate coordinate convention. -/
theorem blade_three_swap_first_last (u v w : V) :
    blade_three R u v w = - blade_three R w v u := by
  calc
    blade_three R u v w = -(blade_three R v u w) :=
      blade_three_swap_first_two R u v w
    _ = - (-(blade_three R v w u)) := by
      rw [blade_three_swap_last_two R v u w]
    _ = -(blade_three R w v u) := by
      rw [blade_three_swap_first_two R v w u]
      simp

/-- Repeating the first and last generator in a 3-blade gives zero. The
adjacent swap moves the repeated generator to the last two positions, where
`ι_sq_zero` applies; this proof is valid in arbitrary characteristic. -/
theorem blade_three_repeated_first_last_zero (u v : V) :
    blade_three R u v u = 0 := by
  rw [blade_three_swap_first_two R u v u]
  rw [blade_three_repeated_last_generator_zero R v u]
  simp

def blade_four (u v w z : V) : ExteriorAlgebra R V :=
  blade_three R u v w * ExteriorAlgebra.ι R z

/-- Swapping the first two generators of a 4-blade reverses its orientation. -/
theorem blade_four_swap_first_two (u v w z : V) :
    blade_four R u v w z = - blade_four R v u w z := by
  dsimp [blade_four]
  rw [blade_three_swap_first_two R u v w, neg_mul]

/-- Swapping the middle two generators of a 4-blade reverses its orientation. -/
theorem blade_four_swap_middle_two (u v w z : V) :
    blade_four R u v w z = - blade_four R u w v z := by
  dsimp [blade_four]
  rw [blade_three_swap_last_two R u v w, neg_mul]

/-- Swapping the last two generators of a 4-blade reverses its orientation. -/
theorem blade_four_swap_last_two (u v w z : V) :
    blade_four R u v w z = - blade_four R u v z w := by
  dsimp [blade_four, blade_three]
  have hswap : ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R z =
      -(ExteriorAlgebra.ι R z * ExteriorAlgebra.ι R w) := by
    exact eq_neg_of_add_eq_zero_left
      (ExteriorAlgebra.ι_add_mul_swap (R := R) w z)
  calc
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v *
        ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R z =
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
          (ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R z) := by
            simp only [mul_assoc]
    _ = (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
        (-(ExteriorAlgebra.ι R z * ExteriorAlgebra.ι R w)) := by rw [hswap]
    _ = -((ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
        (ExteriorAlgebra.ι R z * ExteriorAlgebra.ι R w)) := by rw [mul_neg]
    _ = -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v *
        ExteriorAlgebra.ι R z * ExteriorAlgebra.ι R w) := by
          simp only [mul_assoc]

theorem blade_four_repeated_generator_zero (u v w : V) :
    blade_four R u v w w = 0 := by
  dsimp [blade_four, blade_three]
  have h : ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v *
      ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R w =
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
        (ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R w) := by
    simp only [mul_assoc]
  rw [h, ExteriorAlgebra.ι_sq_zero, mul_zero]

theorem blade_four_repeated_first_two_zero (u v w : V) :
    blade_four R u u v w = 0 := by
  dsimp [blade_four, blade_three]
  have h : ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R u *
      ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R u) *
        (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w) := by
    simp only [mul_assoc]
  rw [h, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem blade_four_repeated_middle_two_zero (u v w : V) :
    blade_four R u v v w = 0 := by
  dsimp [blade_four, blade_three]
  calc
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v *
        ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w =
        ExteriorAlgebra.ι R u *
          (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v) *
            ExteriorAlgebra.ι R w := by simp only [mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

theorem blade_four_repeated_first_third_zero (u v w : V) :
    blade_four R u v u w = 0 := by
  rw [blade_four_swap_first_two R u v u w,
    blade_four_repeated_middle_two_zero R v u w]
  simp

theorem blade_four_repeated_first_last_zero (u v w : V) :
    blade_four R u v w u = 0 := by
  rw [blade_four_swap_first_two R u v w u,
    blade_four_swap_middle_two R v u w u,
    blade_four_repeated_generator_zero R v w u]
  simp

theorem blade_four_repeated_second_last_zero (u v w : V) :
    blade_four R u v w v = 0 := by
  rw [blade_four_swap_middle_two R u v w v,
    blade_four_repeated_generator_zero R u w v]
  simp

/-- The exterior square of a nonempty decomposable blade vanishes in every
finite grade. The duplicated list of generators has a repeated index, so its
alternating image is zero; `ιMulti` identifies that image with the product of
the original blade by itself. This is an exterior-algebra identity, not a
Plücker presentation or a metric nullity statement. -/
theorem decomposable_exterior_blade_square_zero
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

end InfoGeometry.GrassmannianTower
