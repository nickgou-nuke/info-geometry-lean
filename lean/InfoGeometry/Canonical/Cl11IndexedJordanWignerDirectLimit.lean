import InfoGeometry.Canonical.Cl11SequentialColimitSystemBridge
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR

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

theorem uImage_castAdd (n d : ℕ) (k : Fin n) :
    ofStage (n + d) (u (n + d) (Fin.castLE (Nat.le_add_right n d) k)) =
      uImage k := by
  induction d with
  | zero => rfl
  | succ d ih =>
      calc
        ofStage (n + Nat.succ d)
            (u (n + Nat.succ d) (Fin.castLE (Nat.le_add_right n (Nat.succ d)) k)) =
            ofStage ((n + d) + 1)
              (matStageEmbed (n + d)
                (u (n + d) (Fin.castLE (Nat.le_add_right n d) k))) := by
                  simp only [matStageEmbed_u]
                  congr 2
        _ = ofStage (n + d)
              (u (n + d) (Fin.castLE (Nat.le_add_right n d) k)) :=
          ofStage_apply_bond (n + d)
            (u (n + d) (Fin.castLE (Nat.le_add_right n d) k))
        _ = uImage k := ih

theorem vImage_castAdd (n d : ℕ) (k : Fin n) :
    ofStage (n + d) (v (n + d) (Fin.castLE (Nat.le_add_right n d) k)) =
      vImage k := by
  induction d with
  | zero => rfl
  | succ d ih =>
      calc
        ofStage (n + Nat.succ d)
            (v (n + Nat.succ d) (Fin.castLE (Nat.le_add_right n (Nat.succ d)) k)) =
            ofStage ((n + d) + 1)
              (matStageEmbed (n + d)
                (v (n + d) (Fin.castLE (Nat.le_add_right n d) k))) := by
                  simp only [matStageEmbed_v]
                  congr 2
        _ = ofStage (n + d)
              (v (n + d) (Fin.castLE (Nat.le_add_right n d) k)) :=
          ofStage_apply_bond (n + d)
            (v (n + d) (Fin.castLE (Nat.le_add_right n d) k))
        _ = vImage k := ih

theorem uImage_castAdd_cross_site_anticommute
    (n d : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (ofStage (n + d) (u (n + d) (Fin.castLE (Nat.le_add_right n d) i))) *
          (ofStage (n + d) (u (n + d) (Fin.castLE (Nat.le_add_right n d) j))) +
        (ofStage (n + d) (u (n + d) (Fin.castLE (Nat.le_add_right n d) j))) *
          (ofStage (n + d) (u (n + d) (Fin.castLE (Nat.le_add_right n d) i))) = 0 := by
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa [u] using congrArg (ofStage (n + d))
    (InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.creation_cross_site_anticommute
      (n + d) (Fin.castLE (Nat.le_add_right n d) i)
        (Fin.castLE (Nat.le_add_right n d) j) (by
          intro h
          apply hij
          apply Fin.ext
          simpa using congrArg Fin.val h))

theorem vImage_castAdd_cross_site_anticommute
    (n d : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (ofStage (n + d) (v (n + d) (Fin.castLE (Nat.le_add_right n d) i))) *
          (ofStage (n + d) (v (n + d) (Fin.castLE (Nat.le_add_right n d) j))) +
        (ofStage (n + d) (v (n + d) (Fin.castLE (Nat.le_add_right n d) j))) *
          (ofStage (n + d) (v (n + d) (Fin.castLE (Nat.le_add_right n d) i))) = 0 := by
  rw [← ofStage_mul, ← ofStage_mul, ← ofStage_add]
  simpa [v] using congrArg (ofStage (n + d))
    (InfoGeometry.Canonical.Cl11TensorTowerCrossSiteCAR.annihilation_cross_site_anticommute
      (n + d) (Fin.castLE (Nat.le_add_right n d) i)
        (Fin.castLE (Nat.le_add_right n d) j) (by
          intro h
          apply hij
          apply Fin.ext
          simpa using congrArg Fin.val h))

end

end InfoGeometry.Canonical.Cl11IndexedJordanWignerDirectLimit
