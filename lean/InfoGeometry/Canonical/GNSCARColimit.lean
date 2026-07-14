import Mathlib
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.JordanWignerBridge
import InfoGeometry.Clifford.JordanWignerCAR

/-!
# GNS CAR Colimit

This file records the direct-limit representatives of the finite Jordan-Wigner
generators and the stagewise CAR readback they inherit from the matrix tower.

It does **not** assert a completed CAR representation on the direct limit, and
it does **not** construct a star/GNS action.  The honest claim here is only:

* the direct-limit representatives are well-defined;
* their squares and same-stage anticommutator are read off from the finite
  matrix theorems;
* the one-step stage embeddings preserve the chosen representatives.
-/

noncomputable section

namespace GNSCARColimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR

/-- The creation operator for mode `k` in the direct-limit algebra. -/
def limit_u (k : ℕ) : Limit :=
  ofStage (k + 1) (jw_u_new k)

/-- The annihilation operator for mode `k` in the direct-limit algebra. -/
def limit_v (k : ℕ) : Limit :=
  ofStage (k + 1) (jw_v_new k)

/-- The direct-limit creation representative squares to zero. -/
@[simp] theorem limit_u_sq_zero (k : ℕ) : limit_u k * limit_u k = 0 := by
  unfold limit_u
  rw [← ofStage_mul, jw_u_new_sq, ofStage_zero]

/-- The direct-limit annihilation representative squares to zero. -/
@[simp] theorem limit_v_sq_zero (k : ℕ) : limit_v k * limit_v k = 0 := by
  unfold limit_v
  rw [← ofStage_mul, jw_v_new_sq, ofStage_zero]

/-- The same-stage direct-limit mixed CAR relation is the identity. -/
@[simp] theorem limit_uv_anticomm (k : ℕ) :
    limit_u k * limit_v k + limit_v k * limit_u k = 1 := by
  unfold limit_u limit_v
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add, jw_uv_anticomm_new, ofStage_one]

/-- The one-step stage embedding carries the creation representative forward. -/
theorem limit_u_stage_embed (k : ℕ) :
    ofStage (k + 2) (matStageEmbed (k + 1) (jw_u_new k)) = limit_u k := by
  simpa [limit_u, stageEmbed_apply] using
    (ofStage_apply_bond (n := k + 1) (A := jw_u_new k))

/-- The one-step stage embedding carries the annihilation representative forward. -/
theorem limit_v_stage_embed (k : ℕ) :
    ofStage (k + 2) (matStageEmbed (k + 1) (jw_v_new k)) = limit_v k := by
  simpa [limit_v, stageEmbed_apply] using
    (ofStage_apply_bond (n := k + 1) (A := jw_v_new k))

/-- Stagewise CAR packet for the direct-limit representatives. -/
theorem limit_stagewise_car_packet (k : ℕ) :
    limit_u k * limit_u k = 0 ∧
    limit_v k * limit_v k = 0 ∧
    limit_u k * limit_v k + limit_v k * limit_u k = 1 := by
  refine ⟨limit_u_sq_zero k, ?_, limit_uv_anticomm k⟩
  exact limit_v_sq_zero k

end GNSCARColimit
