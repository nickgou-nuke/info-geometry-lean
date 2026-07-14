import Mathlib
import InfoGeometry.Algebra.HypercomplexTriad

/-!
# InfoGeometry.Canonical.ModularLorentzBoost

Concrete `2 × 2` modular-boost commutator identities on the hypercomplex triad.

No wrappers. No `sorry`.
-/

namespace ModularLorentzBoost

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Modular boost generator in the current triad basis. -/
noncomputable def K : M2R := E

@[simp]
theorem K_eval : K = !![(1 : ℝ), 0; 0, -1] := by
  rfl

/-- Infinitesimal modular scaling on the parabolic boundary. -/
theorem modular_commutator_N :
    K * N - N * K = (2 : ℝ) • N := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [K, N, E, Matrix.mul_apply, Fin.sum_univ_two]

/-- Infinitesimal modular scaling on the transpose boundary. -/
noncomputable def Nt : M2R := !![0, 0; 1, 0]

@[simp]
theorem Nt_eq_transpose : Nt = Nᵀ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Nt, N, Matrix.transpose_apply]

theorem modular_commutator_Nt :
    K * Nt - Nt * K = (-2 : ℝ) • Nt := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [K, Nt, E, Matrix.mul_apply, Fin.sum_univ_two]

theorem modular_commutator_N_transpose :
    K * Nᵀ - Nᵀ * K = (-2 : ℝ) • Nᵀ := by
  simpa [Nt_eq_transpose] using modular_commutator_Nt

/-- Finite modular flow (diagonal boost scaling). -/
noncomputable def modularFlow (u : ℝ) : M2R := !![u, 0; 0, u⁻¹]

/-- Finite modular flow scales `N` by `u²`. -/
theorem finite_modular_flow_N (u : ℝ) :
    modularFlow u * N * modularFlow u⁻¹ = (u ^ 2) • N := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [modularFlow, N, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end ModularLorentzBoost
