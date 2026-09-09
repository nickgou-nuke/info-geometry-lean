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

theorem coordinateClock_apply (x : FourState) (i : Fin 4) :
    coordinateClock x i = root4 i * x i := rfl

theorem coordinateClock_pow_apply (n : ℕ) (x : FourState) (i : Fin 4) :
    (coordinateClock ^ n) x i = (root4 i ^ n) * x i := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, coordinateClock_apply, pow_succ]
    ring

def fourierCoeff (k i : Fin 4) : ℂ :=
  (1 / 4 : ℂ) * (1 + root4 k ^ 3 * root4 i + root4 k ^ 2 * root4 i ^ 2 + root4 k * root4 i ^ 3)

theorem fourierCoeff_eq (k i : Fin 4) :
    fourierCoeff k i = if i = k then 1 else 0 := by
  fin_cases k <;> fin_cases i <;> (
    dsimp [fourierCoeff, root4]
    simp only [pow_succ]
    apply Complex.ext <;> norm_num
  )

@[simp] theorem nextSector_zero : nextSector 0 = 1 := rfl
@[simp] theorem nextSector_one : nextSector 1 = 2 := rfl
@[simp] theorem nextSector_two : nextSector 2 = 3 := rfl
@[simp] theorem nextSector_three : nextSector 3 = 0 := rfl

@[simp] theorem cycle_zero (x : FourState) : cycle x 0 = x 3 := rfl
@[simp] theorem cycle_one (x : FourState) : cycle x 1 = x 0 := rfl
@[simp] theorem cycle_two (x : FourState) : cycle x 2 = x 1 := rfl
@[simp] theorem cycle_three (x : FourState) : cycle x 3 = x 2 := rfl

@[simp] theorem truncatedShift_zero (x : FourState) : truncatedShift x 0 = 0 := rfl
@[simp] theorem truncatedShift_one (x : FourState) : truncatedShift x 1 = x 0 := rfl
@[simp] theorem truncatedShift_two (x : FourState) : truncatedShift x 2 = x 1 := rfl
@[simp] theorem truncatedShift_three (x : FourState) : truncatedShift x 3 = x 2 := rfl

theorem coordinateClock_fourth : coordinateClock ^ 4 = 1 := by
  apply LinearMap.ext
  intro x
  ext i
  rw [coordinateClock_pow_apply, root4_pow_four, one_mul, Module.End.one_apply]

/-- Native Fourier polynomial readback as an actual coordinate projector. -/
theorem coordinateProjector_apply (k : Fin 4) (x : FourState) (i : Fin 4) :
    projector coordinateClock k x i = if i = k then x i else 0 := by
  have h_proj : projector coordinateClock k x i = fourierCoeff k i * x i := by
    dsimp [projector, fourierCoeff]
    simp only [coordinateClock_pow_apply, coordinateClock_apply]
    ring
  rw [h_proj, fourierCoeff_eq]
  split_ifs <;> ring

theorem cyclic_projector_covariance (k : Fin 4) :
    cycle * projector coordinateClock k =
      projector coordinateClock (nextSector k) * cycle := by
  apply LinearMap.ext
  intro x
  ext i
  change cycle (projector coordinateClock k x) i =
    projector coordinateClock (nextSector k) (cycle x) i
  fin_cases k <;> fin_cases i <;> simp [-projector_apply, coordinateProjector_apply]

/-- The invertible shift satisfies the same grading covariance. -/
theorem cycle_fourth : cycle ^ 4 = 1 := by
  apply LinearMap.ext
  intro x
  ext i
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
  apply LinearMap.ext
  intro x
  ext i
  change truncatedShift (projector coordinateClock k x) i =
    projector coordinateClock (nextSector k) (truncatedShift x) i
  fin_cases k <;> fin_cases i <;> simp [-projector_apply, coordinateProjector_apply]

/-- Nilpotency is derived from the actual zero boundary at the top sector. -/
theorem truncatedShift_fourth : truncatedShift ^ 4 = 0 := by
  apply LinearMap.ext
  intro x
  ext i
  fin_cases i <;> simp [truncatedShift, pow_succ, Module.End.mul_apply]

/-- The third power is nonzero, so this is a genuine length-four truncated chain. -/
theorem truncatedShift_cube_ne_zero : truncatedShift ^ 3 ≠ 0 := by
  intro h
  have h3 := congrArg (fun T : Module.End ℂ FourState => T ![1, 0, 0, 0] 3) h
  simp [truncatedShift, pow_succ, Module.End.mul_apply] at h3

theorem clock_shift_relation :
    coordinateClock * cycle = Complex.I • (cycle * coordinateClock) := by
  apply LinearMap.ext
  intro x
  ext i
  fin_cases i <;> (
    simp [coordinateClock_apply, smul_eq_mul, Module.End.mul_apply, ← mul_assoc, Complex.I_mul_I]
  )

end InfoGeometry.Algebra.CyclicShiftNilpotencySeparation
