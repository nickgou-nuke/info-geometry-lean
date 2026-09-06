import InfoGeometry.Arithmetic.PrimeMajoranaInfiniteCAR
import InfoGeometry.Clifford.JordanWignerCAR
import InfoGeometry.Clifford.Cl11TensorTowerLimit

set_option autoImplicit false

/-!
# Concrete fixed-site CAR in the `Cl(1,1)` direct limit

For a fixed Jordan--Wigner site `k`, the offset family `jw_u k d`,
`jw_v k d` is compatible under the tower embeddings.  This file instantiates
the repository's generic `ExteriorCARPair` direct-limit theorem for that
family.  The result is a genuine CAR statement for each fixed site image in
the algebraic direct-limit carrier.
-/

namespace InfoGeometry.Canonical.Cl11JordanWignerSiteCARLimit

noncomputable section

open InfoGeometry.Arithmetic.PrimeMajoranaCAR
open InfoGeometry.Arithmetic.PrimeMajoranaInfiniteCAR
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Clifford.JordanWignerCAR

abbrev Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

abbrev siteStage (k n : ℕ) : Type := MatStage (k + 1 + n)

def siteBond (k n : ℕ) : siteStage k n →+* siteStage k (n + 1) :=
  (stageEmbed (k + 1 + n)).toRingHom

def siteCone (k n : ℕ) : siteStage k n →+* Limit :=
  ofStage (k + 1 + n)

theorem site_u_square_zero (k n : ℕ) :
    jw_u k n * jw_u k n = 0 := by
  have h0 : jw_u k 0 * jw_u k 0 = 0 := by
    simpa [jw_u, embedToStage] using jw_u_new_sq k
  induction n with
  | zero => exact h0
  | succ n ih =>
      rw [← matStageEmbed_jw_u k n]
      simpa [stageEmbed_apply] using congrArg (stageEmbed (k + 1 + n)) ih

theorem site_v_square_zero (k n : ℕ) :
    jw_v k n * jw_v k n = 0 := by
  have h0 : jw_v k 0 * jw_v k 0 = 0 := by
    simpa [jw_v, embedToStage] using jw_v_new_sq k
  induction n with
  | zero => exact h0
  | succ n ih =>
      rw [← matStageEmbed_jw_v k n]
      simpa [stageEmbed_apply] using congrArg (stageEmbed (k + 1 + n)) ih

theorem site_uv_anticomm_one (k n : ℕ) :
    jw_u k n * jw_v k n + jw_v k n * jw_u k n = 1 := by
  have h0 : jw_u k 0 * jw_v k 0 + jw_v k 0 * jw_u k 0 = 1 := by
    simpa [jw_u, jw_v, embedToStage] using jw_uv_anticomm_new k
  induction n with
  | zero => exact h0
  | succ n ih =>
      rw [← matStageEmbed_jw_u k n, ← matStageEmbed_jw_v k n]
      have h := congrArg (stageEmbed (k + 1 + n)) ih
      simpa [stageEmbed_apply, map_add, map_mul] using h

def siteCARPair (k n : ℕ) : ExteriorCARPair (siteStage k n) where
  eps := jw_u k n
  iota := jw_v k n
  eps_sq_zero := site_u_square_zero k n
  iota_sq_zero := site_v_square_zero k n
  iota_eps_add_eps_iota := by
    simpa [add_comm] using site_uv_anticomm_one k n

theorem siteCARPair_eps_step (k n : ℕ) :
    siteBond k n (siteCARPair k n).eps = (siteCARPair k (n + 1)).eps := by
  simpa [siteBond, siteCARPair, stageEmbed_apply] using matStageEmbed_jw_u k n

theorem siteCARPair_iota_step (k n : ℕ) :
    siteBond k n (siteCARPair k n).iota = (siteCARPair k (n + 1)).iota := by
  simpa [siteBond, siteCARPair, stageEmbed_apply] using matStageEmbed_jw_v k n

theorem site_CAR_limit_image (k n : ℕ) :
    siteCone k n ((siteCARPair k n).eps) * siteCone k n ((siteCARPair k n).eps) = 0 ∧
    siteCone k n ((siteCARPair k n).iota) * siteCone k n ((siteCARPair k n).iota) = 0 ∧
    anticomm (siteCone k n ((siteCARPair k n).eps))
      (siteCone k n ((siteCARPair k n).iota)) = 1 := by
  have h := exteriorCARPair_limit_image_car
    (A := siteStage k) (L := Limit) (φ := siteBond k) (ι := siteCone k)
    (P := siteCARPair k) (siteCARPair_eps_step k) (siteCARPair_iota_step k) n
  exact h

end

end InfoGeometry.Canonical.Cl11JordanWignerSiteCARLimit
