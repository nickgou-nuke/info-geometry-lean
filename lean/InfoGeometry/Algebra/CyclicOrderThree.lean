import Mathlib.Algebra.Module.End
import Mathlib.Tactic

namespace InfoGeometry.Algebra.CyclicOrderThree

section Additive

variable {Scalar Space : Type*} [CommRing Scalar] [AddCommGroup Space] [Module Scalar Space]
variable (rotation : Module.End Scalar Space)

def orbitSum : Module.End Scalar Space :=
  LinearMap.id + rotation + rotation.comp rotation

def boundary : Module.End Scalar Space := LinearMap.id - rotation

@[simp] theorem orbitSum_apply (vector : Space) :
    orbitSum rotation vector = vector + rotation vector + rotation (rotation vector) := rfl

@[simp] theorem boundary_apply (vector : Space) :
    boundary rotation vector = vector - rotation vector := rfl

variable (hcycle : ∀ vector, rotation (rotation (rotation vector)) = vector)

include hcycle in
theorem orbitSum_fixed (vector : Space) :
    rotation (orbitSum rotation vector) = orbitSum rotation vector := by
  simp only [orbitSum_apply, map_add, hcycle]
  abel

include hcycle in
theorem orbitSum_rotation (vector : Space) :
    orbitSum rotation (rotation vector) = orbitSum rotation vector := by
  simp only [orbitSum_apply, hcycle]
  abel

include hcycle in
theorem orbitSum_boundary (vector : Space) :
    orbitSum rotation (boundary rotation vector) = 0 := by
  rw [boundary_apply, map_sub, orbitSum_rotation rotation hcycle, sub_self]

include hcycle in
theorem boundary_orbitSum (vector : Space) :
    boundary rotation (orbitSum rotation vector) = 0 := by
  rw [boundary_apply, orbitSum_fixed rotation hcycle, sub_self]

theorem orbitSum_of_fixed (vector : Space) (hfixed : rotation vector = vector) :
    orbitSum rotation vector = (3 : Scalar) • vector := by
  simp only [orbitSum_apply, hfixed]
  module

include hcycle in
theorem orbitSum_square (vector : Space) :
    orbitSum rotation (orbitSum rotation vector) = (3 : Scalar) • orbitSum rotation vector :=
  orbitSum_of_fixed rotation _ (orbitSum_fixed rotation hcycle vector)

end Additive

section Averaging

variable {Scalar Space : Type*} [Field Scalar] [CharZero Scalar]
variable [AddCommGroup Space] [Module Scalar Space]
variable (rotation : Module.End Scalar Space)
variable (hcycle : ∀ vector, rotation (rotation (rotation vector)) = vector)

def reynolds : Module.End Scalar Space := (3 : Scalar)⁻¹ • orbitSum rotation

omit [CharZero Scalar] in
@[simp] theorem reynolds_apply (vector : Space) :
    reynolds rotation vector = (3 : Scalar)⁻¹ • orbitSum rotation vector := rfl

include hcycle in
omit [CharZero Scalar] in
theorem reynolds_fixed (vector : Space) :
    rotation (reynolds rotation vector) = reynolds rotation vector := by
  rw [reynolds_apply, map_smul, orbitSum_fixed rotation hcycle]

theorem reynolds_of_fixed (vector : Space) (hfixed : rotation vector = vector) :
    reynolds rotation vector = vector := by
  rw [reynolds_apply, orbitSum_of_fixed rotation vector hfixed, smul_smul]
  norm_num

include hcycle in
theorem reynolds_idempotent :
    (reynolds rotation).comp (reynolds rotation) = reynolds rotation := by
  ext vector
  exact reynolds_of_fixed rotation _ (reynolds_fixed rotation hcycle vector)

include hcycle in
theorem range_reynolds :
    LinearMap.range (reynolds rotation) = LinearMap.ker (boundary rotation) := by
  ext vector
  constructor
  · rintro ⟨source, rfl⟩
    change reynolds rotation source - rotation (reynolds rotation source) = 0
    rw [reynolds_fixed rotation hcycle, sub_self]
  · intro hfixed
    have hequal : rotation vector = vector := (sub_eq_zero.mp hfixed).symm
    exact ⟨vector, reynolds_of_fixed rotation vector hequal⟩

theorem boundary_primitive (vector : Space) :
    boundary rotation ((3 : Scalar)⁻¹ • ((2 : Scalar) • vector + rotation vector)) =
      vector - reynolds rotation vector := by
  simp only [boundary_apply, map_smul, map_add, reynolds_apply, orbitSum_apply]
  module

include hcycle in
theorem ker_reynolds :
    LinearMap.ker (reynolds rotation) = LinearMap.range (boundary rotation) := by
  ext vector
  constructor
  · intro hzero
    refine ⟨(3 : Scalar)⁻¹ • ((2 : Scalar) • vector + rotation vector), ?_⟩
    rw [boundary_primitive, show reynolds rotation vector = 0 from hzero, sub_zero]
  · rintro ⟨source, rfl⟩
    change reynolds rotation (boundary rotation source) = 0
    rw [reynolds_apply, orbitSum_boundary rotation hcycle, smul_zero]

include hcycle in
theorem orbitSum_eq_zero_iff_boundary (vector : Space) :
    orbitSum rotation vector = 0 ↔ ∃ source, boundary rotation source = vector := by
  constructor
  · intro hzero
    have hmem : vector ∈ LinearMap.ker (reynolds rotation) := by
      change (3 : Scalar)⁻¹ • orbitSum rotation vector = 0
      rw [hzero, smul_zero]
    rw [ker_reynolds rotation hcycle] at hmem
    exact hmem
  · rintro ⟨source, rfl⟩
    exact orbitSum_boundary rotation hcycle source

end Averaging

end InfoGeometry.Algebra.CyclicOrderThree
