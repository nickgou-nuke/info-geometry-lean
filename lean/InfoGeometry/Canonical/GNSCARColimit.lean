import Mathlib.Tactic
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Clifford.JordanWignerBridge
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Canonical.Cl11JordanWignerDirectLimit
import InfoGeometry.Clifford.Cl11JordanWignerCARBridge
import InfoGeometry.Canonical.Cl11IndexedJordanWignerCrossSiteLimit

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

namespace InfoGeometry.Canonical.GNSCARColimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR
open InfoGeometry.Clifford.Cl11JordanWignerCARBridge

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

/-- The stabilized creation representative may be read at every later stage. -/
theorem limit_u_stage (k d : ℕ) :
    ofStage (k + 1 + d) (jw_u k d) = limit_u k := by
  simpa [InfoGeometry.Canonical.Cl11JordanWignerDirectLimit.jwUImage,
    limit_u] using
    (InfoGeometry.Canonical.Cl11JordanWignerDirectLimit.jwUImage_eq_base k d)

/-- The stabilized annihilation representative may be read at every later stage. -/
theorem limit_v_stage (k d : ℕ) :
    ofStage (k + 1 + d) (jw_v k d) = limit_v k := by
  simpa [InfoGeometry.Canonical.Cl11JordanWignerDirectLimit.jwVImage,
    limit_v] using
    (InfoGeometry.Canonical.Cl11JordanWignerDirectLimit.jwVImage_eq_base k d)

theorem limit_u_eq_uImage_last (k : ℕ) :
    limit_u k =
      InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.uImage
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
  unfold limit_u InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.uImage
  change ofStage (k + 1) (jw_u_new k) =
    ofStage (k + 1) (jwCreation (k + 1) ⟨k, Nat.lt_succ_self k⟩)
  rw [jwCreation_last_eq_jw_u_new]

theorem limit_v_eq_vImage_last (k : ℕ) :
    limit_v k =
      InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.vImage
        (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) := by
  unfold limit_v InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.vImage
  change ofStage (k + 1) (jw_v_new k) =
    ofStage (k + 1) (jwAnnihilation (k + 1) ⟨k, Nat.lt_succ_self k⟩)
  rw [jwAnnihilation_last_eq_jw_v_new]

private theorem ofStage_jwCreation_castLE (m n : ℕ) (h : m ≤ n) (k : Fin m) :
    ofStage n (jwCreation n (Fin.castLE h k)) = ofStage m (jwCreation m k) := by
  induction h with
  | refl => rfl
  | @step n h ih =>
      calc
        ofStage (n + 1) (jwCreation (n + 1) (Fin.castLE (Nat.le_succ_of_le h) k)) =
            ofStage (n + 1) (matStageEmbed n (jwCreation n (Fin.castLE h k))) := by
              rw [matStageEmbed_jwCreation]
              congr 2
        _ = ofStage n (jwCreation n (Fin.castLE h k)) :=
          ofStage_apply_bond n (jwCreation n (Fin.castLE h k))
        _ = ofStage m (jwCreation m k) := ih

private theorem ofStage_jwAnnihilation_castLE (m n : ℕ) (h : m ≤ n) (k : Fin m) :
    ofStage n (jwAnnihilation n (Fin.castLE h k)) = ofStage m (jwAnnihilation m k) := by
  induction h with
  | refl => rfl
  | @step n h ih =>
      calc
        ofStage (n + 1) (jwAnnihilation (n + 1) (Fin.castLE (Nat.le_succ_of_le h) k)) =
            ofStage (n + 1) (matStageEmbed n (jwAnnihilation n (Fin.castLE h k))) := by
              rw [matStageEmbed_jwAnnihilation]
              congr 2
        _ = ofStage n (jwAnnihilation n (Fin.castLE h k)) :=
          ofStage_apply_bond n (jwAnnihilation n (Fin.castLE h k))
        _ = ofStage m (jwAnnihilation m k) := ih

theorem limit_u_cross_site_anticommute {i j : ℕ} (hij : i ≠ j) :
    limit_u i * limit_u j + limit_u j * limit_u i = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hi : limit_u i = ofStage (j + 1)
        (u (j + 1) (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt h))
          (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)))) := by
      rw [limit_u_eq_uImage_last]
      simpa [u] using (ofStage_jwCreation_castLE (i + 1) (j + 1)
        (Nat.succ_le_succ (Nat.le_of_lt h)) (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))).symm
    have hj : limit_u j = ofStage (j + 1)
        (u (j + 1) (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))) := by
      rw [limit_u_eq_uImage_last,
        ← InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.uImage_castAdd
          (j + 1) 0 (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))]
      rfl
    rw [hi, hj]
    rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
    simpa [u] using congrArg (ofStage (j + 1))
      (InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute
        (j + 1)
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt h))
          (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)))
        (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) (by
          intro hij'
          have hv := congrArg Fin.val hij'
          simp at hv
          omega))
  · simpa [add_comm] using limit_u_cross_site_anticommute hij.symm

theorem limit_v_cross_site_anticommute {i j : ℕ} (hij : i ≠ j) :
    limit_v i * limit_v j + limit_v j * limit_v i = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hi : limit_v i = ofStage (j + 1)
        (v (j + 1) (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt h))
          (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)))) := by
      rw [limit_v_eq_vImage_last]
      simpa [v] using (ofStage_jwAnnihilation_castLE (i + 1) (j + 1)
        (Nat.succ_le_succ (Nat.le_of_lt h)) (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))).symm
    have hj : limit_v j = ofStage (j + 1)
        (v (j + 1) (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))) := by
      rw [limit_v_eq_vImage_last,
        ← InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit.vImage_castAdd
          (j + 1) 0 (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))]
      rfl
    rw [hi, hj]
    rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
    simpa [v] using congrArg (ofStage (j + 1))
      (InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.annihilation_cross_site_anticommute
        (j + 1)
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt h))
          (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)))
        (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) (by
          intro hij'
          have hv := congrArg Fin.val hij'
          simp at hv
          omega))
  · simpa [add_comm] using limit_v_cross_site_anticommute hij.symm

theorem limit_u_v_cross_site_anticommute {i j : ℕ} (hij : i ≠ j) :
    limit_u i * limit_v j + limit_v j * limit_u i = 0 := by
  let N := i + j + 2
  have hi : limit_u i = ofStage N
        (u N (Fin.castLE (by dsimp [N]; omega)
          (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)))) := by
    rw [limit_u_eq_uImage_last]
    simpa [u, N] using (ofStage_jwCreation_castLE (i + 1) N
      (by dsimp [N]; omega) (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1))).symm
  have hj : limit_v j = ofStage N
        (v N (Fin.castLE (by dsimp [N]; omega)
          (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)))) := by
    rw [limit_v_eq_vImage_last]
    simpa [v, N] using (ofStage_jwAnnihilation_castLE (j + 1) N
      (by dsimp [N]; omega) (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))).symm
  rw [hi, hj, ← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa [u, v, N] using congrArg (ofStage N)
      (InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_annihilation_cross_site_anticommute
        N
        (Fin.castLE (by dsimp [N]; omega)
          (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)))
        (Fin.castLE (by dsimp [N]; omega)
          (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))) (by
          intro hij'
          have hv := congrArg Fin.val hij'
          simp at hv
          exact hij (by simpa using hv)))

theorem limit_v_u_cross_site_anticommute {i j : ℕ} (hij : i ≠ j) :
    limit_v i * limit_u j + limit_u j * limit_v i = 0 := by
  simpa [add_comm] using limit_u_v_cross_site_anticommute hij.symm


end InfoGeometry.Canonical.GNSCARColimit
