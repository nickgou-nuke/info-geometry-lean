import Mathlib
import proofs.SiliconPhotonicChipCoefficients

/-!
# Two-Port Scattering Coefficients and J-Unitary Constraints

A finite `2 × 2` real scattering interface

`S = [[t, rL], [rR, t]]`

with Krein metric `J = diag(1,-1)`.  The exact `J`-unitarity condition
`Sᵀ J S = J` imposes not only the two flux equations

`T - R_R = 1`, `T - R_L = 1`,

but also the off-diagonal reciprocity constraint `t * (rL - rR) = 0`.  Thus,
for nonzero transmission, a real `J`-unitary two-port of this symmetric form has
`rL = rR`.
-/

noncomputable section

open Matrix Real

namespace InfoGeometry.GrandUnification.TwoPortScatteringCoefficients

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Two-port real scattering matrix with common transmission and left/right reflections. -/
def twoPortS (t rL rR : ℝ) : M2R :=
  !![t, rL; rR, t]

/-- Krein metric for a two-port gain/loss interface. -/
def JMetric : M2R :=
  !![1, 0; 0, -1]

/-- Real transpose version of J-unitarity. -/
def IsJUnitaryTwoPort (t rL rR : ℝ) : Prop :=
  (twoPortS t rL rR).transpose * JMetric * twoPortS t rL rR = JMetric

/-- Ordinary Euclidean nonunitary defect `D = SᵀS - I`. -/
def twoPortDefect (t rL rR : ℝ) : M2R :=
  (twoPortS t rL rR).transpose * twoPortS t rL rR - (1 : M2R)

/-- Left reflection intensity. -/
def leftReflectance (rL : ℝ) : ℝ := rL ^ 2

/-- Right reflection intensity. -/
def rightReflectance (rR : ℝ) : ℝ := rR ^ 2

/-- Transmission intensity. -/
def transmittance (t : ℝ) : ℝ := t ^ 2

/-- Explicit J-unitarity matrix for a two-port interface. -/
theorem twoPort_junitary_matrix_formula (t rL rR : ℝ) :
    (twoPortS t rL rR).transpose * JMetric * twoPortS t rL rR =
      !![t ^ 2 - rR ^ 2, t * rL - rR * t;
         rL * t - t * rR, rL ^ 2 - t ^ 2] := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [twoPortS, JMetric, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- J-unitarity is exactly the two flux equations plus the off-diagonal reciprocity constraint. -/
theorem isJUnitaryTwoPort_iff (t rL rR : ℝ) :
    IsJUnitaryTwoPort t rL rR ↔
      t ^ 2 - rR ^ 2 = 1 ∧
      rL ^ 2 - t ^ 2 = -1 ∧
      t * rL - rR * t = 0 ∧
      rL * t - t * rR = 0 := by
  unfold IsJUnitaryTwoPort
  rw [twoPort_junitary_matrix_formula]
  constructor
  · intro h
    constructor
    · simpa [JMetric] using congrFun (congrFun h 0) 0
    constructor
    · simpa [JMetric] using congrFun (congrFun h 1) 1
    constructor
    · simpa [JMetric] using congrFun (congrFun h 0) 1
    · simpa [JMetric] using congrFun (congrFun h 1) 0
  · intro h
    rcases h with ⟨h00, h11, h01, h10⟩
    ext i j
    all_goals fin_cases i
    all_goals fin_cases j
    all_goals simp [JMetric, h00, h11, h01, h10]

/-- Nonzero transmission forces reciprocal left/right reflection in this real two-port model. -/
theorem left_eq_right_of_junitary_of_transmission_ne_zero
    {t rL rR : ℝ} (hJu : IsJUnitaryTwoPort t rL rR) (ht : t ≠ 0) :
    rL = rR := by
  have h := (isJUnitaryTwoPort_iff t rL rR).mp hJu
  have hoff : t * (rL - rR) = 0 := by
    simpa [mul_sub, mul_comm, mul_left_comm, mul_assoc] using h.2.2.1
  rcases mul_eq_zero.mp hoff with ht0 | hdiff
  · exact False.elim (ht ht0)
  · exact sub_eq_zero.mp hdiff

/-- J-unitarity yields the right-port flux law `T - R_R = 1`. -/
theorem right_flux_law_of_junitary {t rL rR : ℝ} (hJu : IsJUnitaryTwoPort t rL rR) :
    transmittance t - rightReflectance rR = 1 := by
  exact (isJUnitaryTwoPort_iff t rL rR).mp hJu |>.1

/-- J-unitarity yields the left-port flux law `T - R_L = 1`. -/
theorem left_flux_law_of_junitary {t rL rR : ℝ} (hJu : IsJUnitaryTwoPort t rL rR) :
    transmittance t - leftReflectance rL = 1 := by
  have h := (isJUnitaryTwoPort_iff t rL rR).mp hJu |>.2.1
  calc
    transmittance t - leftReflectance rL = -(rL ^ 2 - t ^ 2) := by
      unfold transmittance leftReflectance
      ring
    _ = 1 := by
      rw [h]
      norm_num

/-- Explicit Euclidean nonunitary defect matrix. -/
theorem twoPortDefect_formula (t rL rR : ℝ) :
    twoPortDefect t rL rR =
      !![t ^ 2 + rR ^ 2 - 1, t * rL + rR * t;
         rL * t + t * rR, rL ^ 2 + t ^ 2 - 1] := by
  ext i j
  all_goals fin_cases i
  all_goals fin_cases j
  all_goals simp [twoPortDefect, twoPortS, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- The hyperbolic chip coefficients instantiate a reciprocal J-unitary two-port. -/
theorem hyperbolic_twoPort_junitary (α : ℝ) :
    IsJUnitaryTwoPort (Real.cosh α) (Real.sinh α) (Real.sinh α) := by
  rw [isJUnitaryTwoPort_iff]
  constructor
  · exact Real.cosh_sq_sub_sinh_sq α
  constructor
  · have h := Real.cosh_sq_sub_sinh_sq α
    calc
      Real.sinh α ^ 2 - Real.cosh α ^ 2 = -(Real.cosh α ^ 2 - Real.sinh α ^ 2) := by
        ring
      _ = -1 := by
        rw [h]
  constructor <;> ring

/-- Consolidated two-port coefficient package. -/
theorem twoPort_scattering_coefficients_synthesis :
    (∀ t rL rR : ℝ, IsJUnitaryTwoPort t rL rR ↔
      t ^ 2 - rR ^ 2 = 1 ∧
      rL ^ 2 - t ^ 2 = -1 ∧
      t * rL - rR * t = 0 ∧
      rL * t - t * rR = 0) ∧
    (∀ t rL rR : ℝ, IsJUnitaryTwoPort t rL rR → t ≠ 0 → rL = rR) ∧
    (∀ t rL rR : ℝ, IsJUnitaryTwoPort t rL rR → transmittance t - rightReflectance rR = 1) ∧
    (∀ t rL rR : ℝ, IsJUnitaryTwoPort t rL rR → transmittance t - leftReflectance rL = 1) ∧
    (∀ α : ℝ, IsJUnitaryTwoPort (Real.cosh α) (Real.sinh α) (Real.sinh α)) := by
  constructor
  · intro t rL rR
    exact isJUnitaryTwoPort_iff t rL rR
  constructor
  · intro t rL rR h ht
    exact left_eq_right_of_junitary_of_transmission_ne_zero h ht
  constructor
  · intro t rL rR h
    exact right_flux_law_of_junitary h
  constructor
  · intro t rL rR h
    exact left_flux_law_of_junitary h
  · intro α
    rw [isJUnitaryTwoPort_iff]
    constructor
    · exact Real.cosh_sq_sub_sinh_sq α
    constructor
    · have h := Real.cosh_sq_sub_sinh_sq α
      calc
        Real.sinh α ^ 2 - Real.cosh α ^ 2 = -(Real.cosh α ^ 2 - Real.sinh α ^ 2) := by
          ring
        _ = -1 := by
          rw [h]
    constructor <;> ring

end InfoGeometry.GrandUnification.TwoPortScatteringCoefficients
