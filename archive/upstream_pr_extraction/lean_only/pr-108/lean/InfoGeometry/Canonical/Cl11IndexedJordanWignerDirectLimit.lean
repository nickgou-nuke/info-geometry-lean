import InfoGeometry.Canonical.Cl11SequentialColimitSystemBridge
import InfoGeometry.Clifford.Cl11TensorTower

set_option autoImplicit false

/-!
# Indexed Jordan--Wigner strings and the `Cl(1,1)` direct limit

The indexed strings `u n k` and `v n k` are the finite-stage Jordan--Wigner
operators from `Cl11TensorTower`.  This file proves their actual cone
compatibility under appending an identity tensor factor.  It is the precise
finite-to-direct-limit prerequisite for multi-site CAR; no cross-site CAR law
is assumed here.
-/

namespace InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit

noncomputable section

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

abbrev Limit := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

def uImage {n : ℕ} (k : Fin n) : Limit :=
  ofStage n (u n k)

def vImage {n : ℕ} (k : Fin n) : Limit :=
  ofStage n (v n k)

theorem uImage_castSucc (n : ℕ) (k : Fin n) :
    ofStage (n + 1) (u (n + 1) k.castSucc) = uImage k := by
  rw [← matStageEmbed_u k]
  exact ofStage_apply_bond n (u n k)

theorem vImage_castSucc (n : ℕ) (k : Fin n) :
    ofStage (n + 1) (v (n + 1) k.castSucc) = vImage k := by
  rw [← matStageEmbed_v k]
  exact ofStage_apply_bond n (v n k)

theorem uImage_eq_stage_embed (n : ℕ) (k : Fin n) :
    uImage k = ofStage (n + 1) (u (n + 1) k.castSucc) := by
  exact (uImage_castSucc n k).symm

theorem vImage_eq_stage_embed (n : ℕ) (k : Fin n) :
    vImage k = ofStage (n + 1) (v (n + 1) k.castSucc) := by
  exact (vImage_castSucc n k).symm

end

end InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit
