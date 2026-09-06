import Mathlib
import InfoGeometry.Physics.SplitOctonionBraidSU3

namespace InfoGeometry.Canonical.ZornCircularTrialityBasis

noncomputable section

open InfoGeometry.Physics.SplitOctonionBraidSU3

attribute [local simp] Matrix.vecHead Matrix.vecTail Matrix.cons_val_zero
  Matrix.cons_val_one Matrix.cons_val_two Matrix.cons_val_succ

abbrev Vec3C := Fin 3 → ℂ

def rotate3C (u : Vec3C) : Vec3C := ![u 1, u 2, u 0]

def cZero : Vec3C := fun _ => 1

def cPlus (ω : ℂ) : Vec3C :=
  fun i => if i = 0 then 1 else if i = 1 then ω else ω ^ 2

def cMinus (ω : ℂ) : Vec3C :=
  fun i => if i = 0 then 1 else if i = 1 then ω ^ 2 else ω

def dotC (u v : Vec3C) : ℂ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

theorem rotate3C_cZero : rotate3C cZero = cZero := by
  funext i
  fin_cases i <;> simp [rotate3C, cZero]

theorem rotate3C_cPlus (ω : ℂ) (hω : ω ^ 3 = 1) :
    rotate3C (cPlus ω) = ω • cPlus ω := by
  funext i
  fin_cases i
  · simp [rotate3C, cPlus, pow_two]
  · simp [rotate3C, cPlus, pow_two]
  · simp [rotate3C, cPlus]
    calc
      (1 : ℂ) = ω ^ 3 := hω.symm
      _ = ω * ω ^ 2 := by ring

theorem rotate3C_cMinus (ω : ℂ) (hω : ω ^ 3 = 1) :
    rotate3C (cMinus ω) = ω ^ 2 • cMinus ω := by
  funext i
  fin_cases i
  · simp [rotate3C, cMinus]
  · simp [rotate3C, cMinus]
    calc
      ω = ω ^ 4 := by
        rw [show ω ^ 4 = ω * ω ^ 3 by ring, hω]
        ring
      _ = ω ^ 2 * ω ^ 2 := by ring
  · simp [rotate3C, cMinus]
    calc
      1 = ω ^ 3 := hω.symm
      _ = ω ^ 2 * ω := by ring

theorem cZero_dot_cZero : dotC cZero cZero = 3 := by
  simp [dotC, cZero]
  norm_num

theorem cPlus_dot_cMinus (ω : ℂ) (hω : ω ^ 3 = 1) :
    dotC (cPlus ω) (cMinus ω) = 3 := by
  have h₁ : ω * ω ^ 2 = 1 := by
    rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω]
  have h₂ : ω ^ 2 * ω = 1 := by
    rw [show ω ^ 2 * ω = ω ^ 3 by ring, hω]
  simp [dotC, cPlus, cMinus, h₁, h₂]
  norm_num

theorem cMinus_dot_cPlus (ω : ℂ) (hω : ω ^ 3 = 1) :
    dotC (cMinus ω) (cPlus ω) = 3 := by
  simpa [dotC, cPlus, cMinus, mul_comm, mul_left_comm, mul_assoc] using
    cPlus_dot_cMinus ω hω

theorem cPlus_dot_cPlus (ω : ℂ) (hω : 1 + ω + ω ^ 2 = 0) :
    dotC (cPlus ω) (cPlus ω) = 0 := by
  have hquad : ω ^ 2 + ω + 1 = 0 := by linear_combination hω
  have hcube : ω ^ 3 = 1 := by
    calc
      ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
      _ = 1 := by rw [hquad]; ring
  dsimp [dotC, cPlus]
  calc
    1 * 1 + ω * ω + ω ^ 2 * ω ^ 2 =
        1 + ω * ω + ω ^ 2 * ω ^ 2 := by ring
    _ = 1 + ω ^ 2 + ω ^ 4 := by ring
    _ = 1 + ω ^ 2 + ω * ω ^ 3 := by
      rw [show ω ^ 4 = ω * ω ^ 3 by ring]
    _ = 1 + ω ^ 2 + ω := by rw [hcube]; ring
    _ = 0 := by linear_combination hω

theorem cMinus_dot_cMinus (ω : ℂ) (hω : 1 + ω + ω ^ 2 = 0) :
    dotC (cMinus ω) (cMinus ω) = 0 := by
  have hquad : ω ^ 2 + ω + 1 = 0 := by linear_combination hω
  have hcube : ω ^ 3 = 1 := by
    calc
      ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
      _ = 1 := by rw [hquad]; ring
  dsimp [dotC, cMinus]
  calc
    1 * 1 + ω ^ 2 * ω ^ 2 + ω * ω =
        1 + ω ^ 2 * ω ^ 2 + ω * ω := by ring
    _ = 1 + ω ^ 2 + ω ^ 4 := by ring
    _ = 1 + ω ^ 2 + ω * ω ^ 3 := by
      rw [show ω ^ 4 = ω * ω ^ 3 by ring]
    _ = 1 + ω ^ 2 + ω := by rw [hcube]; ring
    _ = 0 := by linear_combination hω

theorem cross3_cZero_cPlus (ω : ℂ) (hω : 1 + ω + ω ^ 2 = 0) :
    cross3 cZero (cPlus ω) = (ω ^ 2 - ω) • cPlus ω := by
  have hquad : ω ^ 2 + ω + 1 = 0 := by linear_combination hω
  have hcube : ω ^ 3 = 1 := by
    calc
      ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
      _ = 1 := by rw [hquad]; ring
  funext i
  fin_cases i
  · simp [cross3, cZero, cPlus]
  · simp [cross3, cZero, cPlus]
    rw [show (ω ^ 2 - ω) * ω = ω ^ 3 - ω ^ 2 by ring, hcube]
  · simp [cross3, cZero, cPlus]
    rw [show (ω ^ 2 - ω) * ω ^ 2 = ω ^ 4 - ω ^ 3 by ring]
    rw [show ω ^ 4 = ω * ω ^ 3 by ring, hcube]
    ring

theorem cross3_cZero_cMinus (ω : ℂ) (hω : 1 + ω + ω ^ 2 = 0) :
    cross3 cZero (cMinus ω) = (ω - ω ^ 2) • cMinus ω := by
  have hquad : ω ^ 2 + ω + 1 = 0 := by linear_combination hω
  have hcube : ω ^ 3 = 1 := by
    calc
      ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
      _ = 1 := by rw [hquad]; ring
  funext i
  fin_cases i
  · simp [cross3, cZero, cMinus]
  · simp [cross3, cZero, cMinus]
    rw [show (ω - ω ^ 2) * ω ^ 2 = ω ^ 3 - ω ^ 4 by ring]
    rw [show ω ^ 4 = ω * ω ^ 3 by ring, hcube]
    ring
  · simp [cross3, cZero, cMinus]
    rw [show (ω - ω ^ 2) * ω = ω ^ 2 - ω ^ 3 by ring, hcube]

theorem cross3_cPlus_cMinus (ω : ℂ) (hω : 1 + ω + ω ^ 2 = 0) :
    cross3 (cPlus ω) (cMinus ω) = (ω ^ 2 - ω) • cZero := by
  have hquad : ω ^ 2 + ω + 1 = 0 := by linear_combination hω
  have hcube : ω ^ 3 = 1 := by
    calc
      ω ^ 3 = (ω - 1) * (ω ^ 2 + ω + 1) + 1 := by ring
      _ = 1 := by rw [hquad]; ring
  have hfour : ω ^ 4 = ω := by
    rw [show ω ^ 4 = ω * ω ^ 3 by ring, hcube]
    ring
  funext i
  fin_cases i
  · simp [cross3, cPlus, cMinus, cZero]
    rw [show ω ^ 2 * ω ^ 2 = ω ^ 4 by ring, hfour]
    rw [show ω * ω = ω ^ 2 by ring]
  · simp [cross3, cPlus, cMinus, cZero]
  · simp [cross3, cPlus, cMinus, cZero]

end
end InfoGeometry.Canonical.ZornCircularTrialityBasis
