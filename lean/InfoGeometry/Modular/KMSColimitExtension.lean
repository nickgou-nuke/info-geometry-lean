import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Modular.Colimit

variable {A : ℕ → Type*} [∀ n, Ring (A n)] [∀ n, Algebra ℂ (A n)]
variable (iota : ∀ n, A n →ₐ[ℂ] A (n + 1))

def iota_seq (n : ℕ) : ∀ m, A n →ₐ[ℂ] A (n + m)
| 0 => AlgHom.id ℂ (A n)
| m + 1 => (iota (n + m)).comp (iota_seq n m)

variable {A_inf : Type*} [Ring A_inf] [Algebra ℂ A_inf]

theorem psi_comp_iota_seq
    (psi : ∀ n, A n →ₐ[ℂ] A_inf)
    (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
    (n m : ℕ) :
    (psi (n + m)).comp (iota_seq iota n m) = psi n := by
  induction' m with m ih
  · rfl
  · dsimp [iota_seq]
    rw [← AlgHom.comp_assoc]
    have hcomm : (psi (n + (m + 1))).comp (iota (n + m)) = psi (n + m) := by
      simpa [Nat.add_assoc] using psi_comm (n + m)
    rw [hcomm]
    exact ih

structure StagedKMSFamily (omega : ∀ n, A n →ₗ[ℂ] ℂ) : Prop where
  normalized : ∀ n, omega n 1 = 1
  compatible : ∀ n, (omega (n + 1)).comp (iota n).toLinearMap = omega n

theorem staged_state_m_step_compatibility
    {omega : ∀ n, A n →ₗ[ℂ] ℂ} (h_kms : StagedKMSFamily iota omega) (n m : ℕ) :
    (omega (n + m)).comp (iota_seq iota n m).toLinearMap = omega n := by
  induction' m with m ih
  · rfl
  · dsimp [iota_seq]
    rw [← LinearMap.comp_assoc]
    have h_one_step : (omega (n + (m + 1))).comp (iota (n + m)).toLinearMap = omega (n + m) := by
      simpa [Nat.add_assoc] using h_kms.compatible (n + m)
    rw [h_one_step]
    exact ih

/-- The canonical state evaluation on local elements at stage n. -/
def colimitStateAtStage (omega : ∀ n, A n →ₗ[ℂ] ℂ) (n : ℕ) (x : A n) : ℂ :=
  omega n x

/-- 
  MASTER THEOREM (Colimit KMS State Invariance):
  Evaluating the colimit state on an element x ∈ A_n embedded at any higher stage (n + m)
  yields identically the stage n state expectation value: ω_{n+m}(ι_{n, m}(x)) = ω_n(x).
-/
theorem colimit_state_staged_invariance
    {omega : ∀ n, A n →ₗ[ℂ] ℂ} (h_kms : StagedKMSFamily iota omega)
    (n m : ℕ) (x : A n) :
    colimitStateAtStage omega (n + m) (iota_seq iota n m x) =
      colimitStateAtStage omega n x := by
  dsimp [colimitStateAtStage]
  have h_comp := staged_state_m_step_compatibility iota h_kms n m
  have h_eval := congr_arg (fun (f : A n →ₗ[ℂ] ℂ) => f x) h_comp
  exact h_eval

end InfoGeometry.Modular.Colimit

end noncomputable section
