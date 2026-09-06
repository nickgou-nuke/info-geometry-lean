import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Canonical.Cl11ChiralCommutant

/-!
# The native stage-two `M₄(ℝ)` readout

This owner exposes the existing `TowerMatrix` algebra equivalence at stage two.
It deliberately does not introduce a second matrix carrier or identify the
abstract Clifford algebra with its executable matrix shadow.
-/

namespace InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl11ChiralCommutant

abbrev StageTwo := MatStage 2
abbrev M4R := Matrix (Fin 4) (Fin 4) ℝ

noncomputable def stageTwoToM4R : StageTwo ≃ₐ[ℝ] M4R :=
  TowerMatrix.matEquivFinPowTwo 2

theorem stageTwoToM4R_apply (A : StageTwo) :
    stageTwoToM4R A = TowerMatrix.matEquivFinPowTwo 2 A :=
  rfl

theorem stageTwoToM4R_mul (A B : StageTwo) :
    stageTwoToM4R (A * B) = stageTwoToM4R A * stageTwoToM4R B := by
  exact (stageTwoToM4R : StageTwo ≃ₐ[ℝ] M4R).map_mul A B

theorem stageTwoToM4R_one :
    stageTwoToM4R (1 : StageTwo) = (1 : M4R) := by
  exact (stageTwoToM4R : StageTwo ≃ₐ[ℝ] M4R).map_one

theorem stageTwo_card_index :
    Fintype.card (TowerMatrix.Idx 2) = 4 := by
  simpa using TowerMatrix.idx_card_pow_two 2

/-! The chiral sectors on the native stage are read through the existing
`M₄(ℝ)` equivalence; no second grading or stage carrier is introduced. -/
def stageTwoChiralEven (A : StageTwo) : Prop :=
  ChiralEven (stageTwoToM4R A)

def stageTwoChiralOdd (A : StageTwo) : Prop :=
  ChiralOdd (stageTwoToM4R A)

theorem stageTwoChiralEven_add {A B : StageTwo}
    (hA : stageTwoChiralEven A) (hB : stageTwoChiralEven B) :
    stageTwoChiralEven (A + B) := by
  unfold stageTwoChiralEven at hA hB ⊢
  change ChiralEven (stageTwoToM4R A + stageTwoToM4R B)
  exact chiralEven_add hA hB

theorem stageTwoChiralOdd_add {A B : StageTwo}
    (hA : stageTwoChiralOdd A) (hB : stageTwoChiralOdd B) :
    stageTwoChiralOdd (A + B) := by
  unfold stageTwoChiralOdd at hA hB ⊢
  change ChiralOdd (stageTwoToM4R A + stageTwoToM4R B)
  exact chiralOdd_add hA hB

theorem stageTwoChiralEven_neg {A : StageTwo}
    (hA : stageTwoChiralEven A) :
    stageTwoChiralEven (-A) := by
  unfold stageTwoChiralEven at hA ⊢
  change ChiralEven (-(stageTwoToM4R A))
  exact chiralEven_neg hA

theorem stageTwoChiralOdd_neg {A : StageTwo}
    (hA : stageTwoChiralOdd A) :
    stageTwoChiralOdd (-A) := by
  unfold stageTwoChiralOdd at hA ⊢
  change ChiralOdd (-(stageTwoToM4R A))
  exact chiralOdd_neg hA

theorem stageTwoChiralEven_mul_even {A B : StageTwo}
    (hA : stageTwoChiralEven A) (hB : stageTwoChiralEven B) :
    stageTwoChiralEven (A * B) := by
  unfold stageTwoChiralEven at hA hB ⊢
  simpa [stageTwoToM4R] using chiralEven_mul_even hA hB

theorem stageTwoChiralEven_mul_odd {A B : StageTwo}
    (hA : stageTwoChiralEven A) (hB : stageTwoChiralOdd B) :
    stageTwoChiralOdd (A * B) := by
  unfold stageTwoChiralEven at hA
  unfold stageTwoChiralOdd at hB ⊢
  simpa [stageTwoToM4R] using chiralEven_mul_odd hA hB

theorem stageTwoChiralOdd_mul_even {A B : StageTwo}
    (hA : stageTwoChiralOdd A) (hB : stageTwoChiralEven B) :
    stageTwoChiralOdd (A * B) := by
  unfold stageTwoChiralOdd at hA
  unfold stageTwoChiralEven at hB
  unfold stageTwoChiralOdd
  simpa [stageTwoToM4R] using chiralOdd_mul_even hA hB

theorem stageTwoChiralOdd_mul_odd {A B : StageTwo}
    (hA : stageTwoChiralOdd A) (hB : stageTwoChiralOdd B) :
    stageTwoChiralEven (A * B) := by
  unfold stageTwoChiralOdd at hA hB
  unfold stageTwoChiralEven
  simpa [stageTwoToM4R] using chiralOdd_mul_odd hA hB

end InfoGeometry.Canonical.Cl11StageTwoMatrixEquivalence
