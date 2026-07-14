import Mathlib
import InfoGeometry.Clifford.Cl11TensorTower

noncomputable section

open scoped TensorProduct DirectSum Matrix Kronecker
open Matrix

namespace JordanWignerBridge

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix

/-- Base creation operator `a^\dagger = !![0, 1; 0, 0]`. -/
def a_dagger_base : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 1; 0, 0]

/-- Base annihilation operator `a = !![0, 0; 1, 0]`. -/
def a_base : Matrix (Fin 2) (Fin 2) ℝ := !![(0 : ℝ), 0; 1, 0]

/-- The single-site Jordan-Wigner creation operator at exactly the stage where it is introduced. -/
noncomputable def jw_u_new (k : ℕ) : MatStage (k + 1) :=
  (globalChirality k) ⊗ₖ a_dagger_base

/-- The single-site Jordan-Wigner annihilation operator at exactly the stage where it is introduced. -/
noncomputable def jw_v_new (k : ℕ) : MatStage (k + 1) :=
  (globalChirality k) ⊗ₖ a_base

/-- Embed a matrix from stage `k` to stage `k + d` by appending `d` identities. -/
noncomputable def embedToStage (k : ℕ) (A : MatStage k) : (d : ℕ) → MatStage (k + d)
| 0 => A
| d + 1 => matStageEmbed (k + d) (embedToStage k A d)

/-- The creation operator for site `k` at stage `k + 1 + d`. -/
noncomputable def jw_u (k d : ℕ) : MatStage (k + 1 + d) :=
  embedToStage (k + 1) (jw_u_new k) d

/-- The annihilation operator for site `k` at stage `k + 1 + d`. -/
noncomputable def jw_v (k d : ℕ) : MatStage (k + 1 + d) :=
  embedToStage (k + 1) (jw_v_new k) d

/-- By definition, `matStageEmbed` on an embedded generator yields the generator at the next stage. -/
theorem matStageEmbed_jw_u (k d : ℕ) :
    matStageEmbed (k + 1 + d) (jw_u k d) = jw_u k (d + 1) := by
  rfl

theorem matStageEmbed_jw_v (k d : ℕ) :
    matStageEmbed (k + 1 + d) (jw_v k d) = jw_v k (d + 1) := by
  rfl

end JordanWignerBridge
