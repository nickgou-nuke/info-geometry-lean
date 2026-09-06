import Mathlib
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Endomorphism-level tripotent trifactor projectors

Kernel/range identifications for tripotent endomorphisms.

Specializes the element-level projectors from
`InfoGeometry.Physics.Algebra.TripotentPeirceProjectors` to
`Module.End ℝ V` and proves the three spectral range identifications.
-/

noncomputable section

namespace InfoGeometry.Physics.Algebra

section EndTripotent

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (T : Module.End ℝ V) (hT : T ^ 3 = T)

def endProjZero : Module.End ℝ V := projZero T
def endProjPos : Module.End ℝ V := projPos T
def endProjNeg : Module.End ℝ V := projNeg T

include hT

theorem endT_eq_projPos_sub_projNeg :
    T = endProjPos T - endProjNeg T := by
  apply LinearMap.ext
  intro x
  change T x = (projPos T - projNeg T) x
  rw [projPos_sub_projNeg]

theorem endT_sq_eq_projPos_add_projNeg :
    T * T = endProjPos T + endProjNeg T := by
  apply LinearMap.ext
  intro x
  change (T * T) x = (projPos T + projNeg T) x
  rw [projPos_add_projNeg]

theorem endProj_sum_eq_id :
    endProjPos T + endProjZero T + endProjNeg T = 1 := by
  change projPos T + projZero T + projNeg T = 1
  simpa [endProjPos, endProjZero, endProjNeg] using (proj_sum_eq_id (T := T))

theorem endProjPos_mul_endProjNeg_eq_zero :
    endProjPos T * endProjNeg T = 0 := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  simpa [endProjPos, endProjNeg] using (projPos_mul_projNeg_eq_zero (T := T) hT')

theorem endProjNeg_mul_endProjPos_eq_zero :
    endProjNeg T * endProjPos T = 0 := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  simpa [endProjPos, endProjNeg] using (projNeg_mul_projPos_eq_zero (T := T) hT')

theorem endProjPos_mul_endProjZero_eq_zero :
    endProjPos T * endProjZero T = 0 := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  simpa [endProjPos, endProjZero] using (projPos_mul_projZero_eq_zero (T := T) hT')

theorem endProjZero_mul_endProjPos_eq_zero :
    endProjZero T * endProjPos T = 0 := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  simpa [endProjPos, endProjZero] using (projZero_mul_projPos_eq_zero (T := T) hT')

theorem endProjNeg_mul_endProjZero_eq_zero :
    endProjNeg T * endProjZero T = 0 := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  simpa [endProjNeg, endProjZero] using (projNeg_mul_projZero_eq_zero (T := T) hT')

theorem endProjZero_mul_endProjNeg_eq_zero :
    endProjZero T * endProjNeg T = 0 := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  simpa [endProjNeg, endProjZero] using (projZero_mul_projNeg_eq_zero (T := T) hT')

theorem endProjPos_range_eq_ker_sub_one :
    LinearMap.range (endProjPos T) = LinearMap.ker (T - 1) := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  apply le_antisymm
  · rw [LinearMap.range_le_ker_iff]
    change (T - 1) * endProjPos T = 0
    calc
      (T - 1) * endProjPos T = T * endProjPos T - endProjPos T := by
        noncomm_ring
      _ = endProjPos T - endProjPos T := by
        simp [endProjPos, mul_projPos hT']
      _ = 0 := by simp
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [LinearMap.mem_range]
    refine ⟨x, ?_⟩
    have hxT : T x = x := by
      have h : T x + -x = 0 := by simpa [sub_eq_add_neg] using hx
      simpa using (eq_neg_of_add_eq_zero_left h)
    change (1 / 2 : ℝ) • (T (T x) + T x) = x
    rw [hxT]
    simp [hxT]
    module

theorem endProjNeg_range_eq_ker_add_one :
    LinearMap.range (endProjNeg T) = LinearMap.ker (T + 1) := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  apply le_antisymm
  · rw [LinearMap.range_le_ker_iff]
    change (T + 1) * endProjNeg T = 0
    calc
      (T + 1) * endProjNeg T = T * endProjNeg T + endProjNeg T := by
        noncomm_ring
      _ = -endProjNeg T + endProjNeg T := by
        simp [endProjNeg, mul_projNeg hT']
      _ = 0 := by simp
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [LinearMap.mem_range]
    refine ⟨x, ?_⟩
    have hxT : T x = -x := by
      have h : T x + x = 0 := by simpa using hx
      exact eq_neg_of_add_eq_zero_left h
    change (1 / 2 : ℝ) • (T (T x) - T x) = x
    have hxx : T (T x) = x := by
      calc
        T (T x) = T (-x) := by rw [hxT]
        _ = -T x := map_neg T x
        _ = -(-x) := by rw [hxT]
        _ = x := neg_neg x
    rw [hxx, hxT]
    module

theorem endProjPos_range_eq_eigenspace :
    LinearMap.range (endProjPos T) = Module.End.eigenspace T 1 := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  apply le_antisymm
  · rintro X ⟨Y, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    have h := congrArg (fun F : Module.End ℝ V => F Y) (mul_projPos hT')
    simpa [Module.End.mul_apply, endProjPos] using h
  · intro X hX
    rw [Module.End.mem_eigenspace_iff] at hX
    have hX' : T X = X := by simpa using hX
    rw [LinearMap.mem_range]
    refine ⟨X, ?_⟩
    change (1 / 2 : ℝ) • (T (T X) + T X) = X
    have hXX : T (T X) = X := by
      calc
        T (T X) = T X := congrArg T hX'
        _ = X := hX'
    rw [hXX, hX']
    module

theorem endProjNeg_range_eq_eigenspace :
    LinearMap.range (endProjNeg T) = Module.End.eigenspace T (-1) := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  apply le_antisymm
  · rintro X ⟨Y, rfl⟩
    rw [Module.End.mem_eigenspace_iff]
    have h := congrArg (fun F : Module.End ℝ V => F Y) (mul_projNeg hT')
    simpa [Module.End.mul_apply, endProjNeg] using h
  · intro X hX
    rw [Module.End.mem_eigenspace_iff] at hX
    have hX' : T X = -X := by simpa using hX
    rw [LinearMap.mem_range]
    refine ⟨X, ?_⟩
    change (1 / 2 : ℝ) • (T (T X) - T X) = X
    have hXX : T (T X) = X := by
      calc
        T (T X) = T (-X) := by rw [hX']
        _ = -T X := map_neg T X
        _ = -(-X) := by rw [hX']
        _ = X := neg_neg X
    rw [hXX, hX']
    module

theorem endProjZero_range_eq_ker :
    LinearMap.range (endProjZero T) = LinearMap.ker T := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  apply le_antisymm
  · rw [LinearMap.range_le_ker_iff]
    change T * endProjZero T = 0
    unfold endProjZero projZero
    calc
      T * (1 - T * T) = T - T * (T * T) := by rw [mul_sub, mul_one]
      _ = 0 := by rw [← mul_assoc, hT']; simp
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [LinearMap.mem_range]
    refine ⟨x, ?_⟩
    change x - T (T x) = x
    rw [hx, map_zero, sub_zero]

end EndTripotent

end InfoGeometry.Physics.Algebra
