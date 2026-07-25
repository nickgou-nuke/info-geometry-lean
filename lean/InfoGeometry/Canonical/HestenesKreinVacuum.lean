import Mathlib.Tactic
import InfoGeometry.Algebra.HypercomplexTriad
import InfoGeometry.Canonical.ModularLorentzBoost
import InfoGeometry.Canonical.SplitCliffordSourceWickBase
import InfoGeometry.Canonical.SplitCliffordJordanWigner
import InfoGeometry.Canonical.WeylMobiusReflection

/-!
# InfoGeometry.Canonical.HestenesKreinVacuum

Krein-adjoint identities for the local `2×2` real split-Clifford mode.
-/

namespace InfoGeometry.Canonical.HestenesKreinVacuum

open Matrix
open InfoGeometry.Algebra.HypercomplexTriad
open InfoGeometry.Canonical.ModularLorentzBoost (K K_eval)
open InfoGeometry.Canonical.SplitCliffordSourceWickBase (a aDag)
open InfoGeometry.Canonical.SplitCliffordJordanWigner (P P_eq_diag)
open InfoGeometry.Canonical.WeylMobiusReflection

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-- Krein adjoint for metric operator `K`: `A⋆ = K * Aᵀ * K`. -/
noncomputable def kreinAdjoint (A : M2R) : M2R :=
  K * Aᵀ * K

/-- `K` is fixed by the Krein involution. -/
theorem krein_adjoint_K :
    kreinAdjoint K = K := by
  unfold kreinAdjoint
  have hKt : Kᵀ = K := by
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [K_eval, Matrix.transpose_apply]
  have hKK : K * K = (1 : M2R) := by
    simpa [K] using (E_sq : E * E = (1 : M2R))
  calc
    K * Kᵀ * K = K * K * K := by rw [hKt]
    _ = (1 : M2R) * K := by rw [hKK]
    _ = K := by simp

private theorem P_eq_K : P = K := by
  rw [P_eq_diag, K_eval]

private theorem a_eq_N : a = N := rfl

private theorem aDag_eq_N_transpose : aDag = Nᵀ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [aDag, N, Matrix.transpose_apply]

/-- `P` is Krein-self-adjoint. -/
theorem krein_adjoint_P :
    kreinAdjoint P = P := by
  simpa [P_eq_K] using (krein_adjoint_K : kreinAdjoint K = K)

/-- Under `K`, annihilation Krein-adjoint is `-a†`. -/
theorem krein_adjoint_annihilation :
    kreinAdjoint a = -aDag := by
  unfold kreinAdjoint
  rw [a_eq_N, aDag_eq_N_transpose]
  simpa [W_eq_K] using (weyl_conj_N_transpose : W * Nᵀ * W = -Nᵀ)

/-- Under `K`, creation Krein-adjoint is `-a`. -/
theorem krein_adjoint_creation :
    kreinAdjoint aDag = -a := by
  unfold kreinAdjoint
  rw [aDag_eq_N_transpose, Matrix.transpose_transpose, a_eq_N]
  simpa [W_eq_K] using (weyl_conj_N : W * N * W = -N)

end InfoGeometry.Canonical.HestenesKreinVacuum
