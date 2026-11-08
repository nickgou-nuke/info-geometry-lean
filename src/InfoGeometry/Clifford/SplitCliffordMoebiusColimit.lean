import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped Matrix
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Krein
open KreinSpace

namespace InfoGeometry.Clifford.SplitCliffordMoebiusColimit

/-! ### 1. Split-Clifford substrate -/

abbrev Cl11 := CliffordAlgebra q11

/-! ### 2. CAR-normalized isotropic generators -/

/-- The corrected CAR-normalized null generators with `{u, v} = 1`, `u^2 = 0`, `v^2 = 0`. -/
noncomputable def u_null : Cl11 := (1 / 2 : ℝ) • (CliffordAlgebra.ι q11 (1, 0) + CliffordAlgebra.ι q11 (0, 1))
noncomputable def v_null : Cl11 := (1 / 2 : ℝ) • (CliffordAlgebra.ι q11 (1, 0) - CliffordAlgebra.ι q11 (0, 1))

theorem u_null_eq : u_null = CliffordAlgebra.ι q11 ((1 / 2 : ℝ), (1 / 2 : ℝ)) := by
  have h : ((1 / 2 : ℝ), (1 / 2 : ℝ)) = (1 / 2 : ℝ) • ((1 : ℝ), 0) + (1 / 2 : ℝ) • ((0 : ℝ), 1) := by
    ext <;> norm_num
  rw [h, map_add, map_smul, map_smul]
  exact smul_add (1 / 2 : ℝ) _ _

theorem v_null_eq : v_null = CliffordAlgebra.ι q11 ((1 / 2 : ℝ), (-(1 / 2 : ℝ))) := by
  have h : ((1 / 2 : ℝ), (-(1 / 2 : ℝ))) = (1 / 2 : ℝ) • ((1 : ℝ), 0) - (1 / 2 : ℝ) • ((0 : ℝ), 1) := by
    ext <;> norm_num
  rw [h, map_sub, map_smul, map_smul]
  exact smul_sub (1 / 2 : ℝ) _ _

theorem u_sq_zero : u_null * u_null = 0 := by
  rw [u_null_eq, CliffordAlgebra.ι_sq_scalar]
  simp [q11_apply]

theorem v_sq_zero : v_null * v_null = 0 := by
  rw [v_null_eq, CliffordAlgebra.ι_sq_scalar]
  simp [q11_apply]

theorem uv_car_anticomm : u_null * v_null + v_null * u_null = 1 := by
  rw [u_null_eq, v_null_eq]
  have hpolar : QuadraticMap.polar q11 ((1 / 2 : ℝ), (1 / 2 : ℝ)) ((1 / 2 : ℝ), (-(1 / 2 : ℝ))) = 1 := by
    simp [QuadraticMap.polar, q11_apply]
    norm_num
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := q11) ((1 / 2 : ℝ), (1 / 2 : ℝ)) ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))
  rw [hpolar, map_one] at h
  exact h

/-! ### 3. Doubled Krein carrier and twists -/

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem j_involutive (v : DoubledSpace E) : modular_j (modular_j v) = v := by
  have h := ContinuousLinearMap.ext_iff.mp (modular_j_involution E) v
  exact h

theorem epsilon_involutive (v : DoubledSpace E) : spectral_epsilon (spectral_epsilon v) = v := by
  have h := ContinuousLinearMap.ext_iff.mp (spectral_epsilon_involution E) v
  exact h

theorem j_epsilon_anticomm (v : DoubledSpace E) :
    modular_j (spectral_epsilon v) = -spectral_epsilon (modular_j v) := by
  have h := ContinuousLinearMap.ext_iff.mp (modular_j_spectral_epsilon_anticommute E) v
  exact h

end InfoGeometry.Clifford.SplitCliffordMoebiusColimit
