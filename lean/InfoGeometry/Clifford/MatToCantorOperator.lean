import Mathlib
import InfoGeometry.Clifford.JordanWignerCAR

noncomputable section

namespace InfoGeometry.Clifford.MatToCantorOperator

open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR

/-- Real finite Cantor operator algebra at depth `n`: endomorphisms of the
real endpoint-function module indexed by the binary tower indices. -/
abbrev RealCantorOp (n : ℕ) := Module.End ℝ (Idx n → ℝ)

/-- The concrete matrix/operator algebra equivalence at finite depth. -/
noncomputable def matToCantor (n : ℕ) : MatStage n ≃ₐ[ℝ] RealCantorOp n :=
  Matrix.toLinAlgEquiv'

@[simp] theorem matToCantor_apply (n : ℕ) (A : MatStage n) :
    matToCantor n A = Matrix.toLin' A :=
  rfl

@[simp] theorem matToCantor_map_one (n : ℕ) :
    matToCantor n (1 : MatStage n) = (1 : RealCantorOp n) := by
  simp [matToCantor]

@[simp] theorem matToCantor_map_mul (n : ℕ) (A B : MatStage n) :
    matToCantor n (A * B) = matToCantor n A * matToCantor n B := by
  simp [matToCantor]

@[simp] theorem matToCantor_map_add (n : ℕ) (A B : MatStage n) :
    matToCantor n (A + B) = matToCantor n A + matToCantor n B := by
  simp [matToCantor]

@[simp] theorem matToCantor_map_smul (n : ℕ) (c : ℝ) (A : MatStage n) :
    matToCantor n (c • A) = c • matToCantor n A := by
  simp [matToCantor]

/-- The finite matrix/operator map is injective. -/
theorem matToCantor_injective (n : ℕ) : Function.Injective (matToCantor n) :=
  (matToCantor n).injective

/-- Operator-side transition, defined by transporting the matrix transition along
`matToCantor`. -/
noncomputable def cantorOpEmbed (n : ℕ) : RealCantorOp n →ₐ[ℝ] RealCantorOp (n + 1) :=
  (matToCantor (n + 1)).toAlgHom.comp ((stageEmbed n).comp (matToCantor n).symm.toAlgHom)

/-- The finite matrix/operator equivalences commute with one-step embeddings. -/
theorem cantorOpEmbed_matToCantor (n : ℕ) (A : MatStage n) :
    cantorOpEmbed n (matToCantor n A) = matToCantor (n + 1) (matStageEmbed n A) := by
  calc
    cantorOpEmbed n (matToCantor n A)
        = matToCantor (n + 1) (stageEmbed n ((matToCantor n).symm (matToCantor n A))) := rfl
    _ = matToCantor (n + 1) (matStageEmbed n A) := by
      have hsymm : (matToCantor n).symm (matToCantor n A) = A :=
        (matToCantor n).symm_apply_apply A
      rw [hsymm]
      rfl

/-- Creation CAR transported to the finite operator representation. -/
theorem matToCantor_jw_u_new_sq (k : ℕ) :
    matToCantor (k + 1) (jw_u_new k) * matToCantor (k + 1) (jw_u_new k) = 0 := by
  rw [← matToCantor_map_mul, jw_u_new_sq]
  simp

/-- Annihilation CAR transported to the finite operator representation. -/
theorem matToCantor_jw_v_new_sq (k : ℕ) :
    matToCantor (k + 1) (jw_v_new k) * matToCantor (k + 1) (jw_v_new k) = 0 := by
  rw [← matToCantor_map_mul, jw_v_new_sq]
  simp

/-- Same-site CAR anticommutator transported to the finite operator representation. -/
theorem matToCantor_jw_uv_anticomm_new (k : ℕ) :
    matToCantor (k + 1) (jw_u_new k) * matToCantor (k + 1) (jw_v_new k) +
      matToCantor (k + 1) (jw_v_new k) * matToCantor (k + 1) (jw_u_new k) = 1 := by
  rw [← matToCantor_map_mul, ← matToCantor_map_mul, ← matToCantor_map_add,
    jw_uv_anticomm_new]
  exact matToCantor_map_one (k + 1)

end InfoGeometry.Clifford.MatToCantorOperator
