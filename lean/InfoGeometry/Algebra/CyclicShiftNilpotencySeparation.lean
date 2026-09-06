import InfoGeometry.Algebra.FourthRootSpectralProjectors

/-!
# Cyclic grading covariance does not imply nilpotency

The same four spectral sectors admit both an invertible cyclic shift and a
nilpotent truncated shift. All operators act on the native function module
`Fin 4 → ℂ`. Their projectors are the constructed Fourier polynomials, not
an independent postulated family.
-/

noncomputable section

namespace InfoGeometry.Algebra.CyclicShiftNilpotencySeparation

open InfoGeometry.Algebra.FourthRootSpectralProjectors

abbrev FourState := Fin 4 → ℂ

def coordinateClock : Module.End ℂ FourState where
  toFun x := fun i => root4 i * x i
  map_add' x y := by funext i; simp [mul_add]
  map_smul' c x := by funext i; simp [smul_eq_mul]; ring

def cycle : Module.End ℂ FourState where
  toFun x := ![x 3, x 0, x 1, x 2]
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' c x := by funext i; fin_cases i <;> rfl

def truncatedShift : Module.End ℂ FourState where
  toFun x := ![0, x 0, x 1, x 2]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' c x := by funext i; fin_cases i <;> simp

/-- A total successor permutation, not a truncated successor. -/
def nextSector : Fin 4 → Fin 4 := ![1, 2, 3, 0]

theorem coordinateClock_fourth : coordinateClock ^ 4 = 1 := by
  ext x i
  fin_cases i <;>
    norm_num [coordinateClock, root4, pow_succ, Module.End.mul_apply] <;> ring

/-- Native Fourier polynomial readback as an actual coordinate projector. -/
theorem coordinateProjector_apply (k : Fin 4) (x : FourState) (i : Fin 4) :
    projector coordinateClock k x i = if i = k then x i else 0 := by
  rw [projector_apply]
  fin_cases k <;> fin_cases i <;>
    norm_num [coordinateClock, root4, pow_succ, smul_eq_mul] <;> ring

theorem cyclic_projector_covariance (k : Fin 4) :
    cycle * projector coordinateClock k =
      projector coordinateClock (nextSector k) * cycle := by
  ext x i
  change cycle (projector coordinateClock k x) i =
    projector coordinateClock (nextSector k) (cycle x) i
  rw [coordinateProjector_apply]
  fin_cases k <;> fin_cases i <;>
    simp [cycle, nextSector, coordinateProjector_apply]

/-- The invertible shift satisfies the same grading covariance. -/
theorem cycle_fourth : cycle ^ 4 = 1 := by
  ext x i
  fin_cases i <;> simp [cycle, pow_succ, Module.End.mul_apply]

theorem cycle_fourth_ne_zero : cycle ^ 4 ≠ 0 := by
  rw [cycle_fourth]
  exact one_ne_zero

/-- Thus the attachment's covariance does not prove the asserted nilpotency. -/
theorem covariance_without_nilpotency :
    (∀ k, cycle * projector coordinateClock k =
      projector coordinateClock (nextSector k) * cycle) ∧ cycle ^ 4 ≠ 0 :=
  ⟨cyclic_projector_covariance, cycle_fourth_ne_zero⟩

theorem truncated_projector_covariance (k : Fin 4) :
    truncatedShift * projector coordinateClock k =
      projector coordinateClock (nextSector k) * truncatedShift := by
  ext x i
  change truncatedShift (projector coordinateClock k x) i =
    projector coordinateClock (nextSector k) (truncatedShift x) i
  rw [coordinateProjector_apply]
  fin_cases k <;> fin_cases i <;>
    simp [truncatedShift, nextSector, coordinateProjector_apply]

/-- Nilpotency is derived from the actual zero boundary at the top sector. -/
theorem truncatedShift_fourth : truncatedShift ^ 4 = 0 := by
  ext x i
  fin_cases i <;> simp [truncatedShift, pow_succ, Module.End.mul_apply]

/-- The third power is nonzero, so this is a genuine length-four truncated chain. -/
theorem truncatedShift_cube_ne_zero : truncatedShift ^ 3 ≠ 0 := by
  intro h
  have h3 := congrArg (fun T : Module.End ℂ FourState => T ![1, 0, 0, 0] 3) h
  norm_num [truncatedShift, pow_succ, Module.End.mul_apply] at h3

theorem clock_shift_relation :
    coordinateClock * cycle = Complex.I • (cycle * coordinateClock) := by
  ext x i
  fin_cases i <;>
    norm_num [coordinateClock, cycle, root4, smul_eq_mul, Module.End.mul_apply] <;> ring

end InfoGeometry.Algebra.CyclicShiftNilpotencySeparation
