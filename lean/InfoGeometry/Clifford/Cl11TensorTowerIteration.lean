import InfoGeometry.Algebra.IterativeExponentiation
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Iterative finite exponentiation in the `Cl(1,1)` tensor tower

This module records the non-analytic iteration principle for the matrix
`Cl(1,1)` tensor string.  A stage advance is the finite operation
`A ↦ A ⊗ₖ I₂`; advancing by `k` steps is primitive finite iteration of that
bonding map, implemented by the existing algebraic `bondMap`.

No Taylor series, infinite sum, analytic exponential, or completion is used.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.Cl11TensorTowerIteration

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas
open InfoGeometry.Algebra.SupergradedBracket

/-- Finite matrix stage in the iterated `Cl(1,1)` tensor string. -/
abbrev Stage (n : ℕ) : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Stage n

/-- The `k`-fold finite stage advance from stage `m` to stage `m+k`. -/
def iteratedStageEmbed (m k : ℕ) : Stage m →+* Stage (m + k) :=
  bondMap (Stage := Stage) InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m (m + k) (Nat.le_add_right m k)

@[simp]
theorem iteratedStageEmbed_zero (m : ℕ) :
    iteratedStageEmbed m 0 = RingHom.id (Stage m) := by
  simpa [iteratedStageEmbed] using
    bondMap_refl (Stage := Stage) InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m

/-- One finite iteration is the one-step tensor embedding. -/
theorem iteratedStageEmbed_one_apply (m : ℕ) (A : Stage m) :
    iteratedStageEmbed m 1 A = InfoGeometry.Clifford.Cl11TensorTower.stageEmbed m A := by
  have hmap :
      bondMap (Stage := Stage) InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m (m + 1) (Nat.le_add_right m 1) A =
        InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m A := by
    have hle : Nat.le_add_right m 1 = Nat.le_succ m := by
      rfl
    rw [hle]
    have hs := bondMap_succ (Stage := Stage) InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m m le_rfl
    have hφ :
        bondMap (Stage := Stage) InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m (m + 1) (Nat.le_succ m) =
          (InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m).comp (RingHom.id (Stage m)) := by
      simpa using hs
    simpa using congrArg (fun φ : Stage m →+* Stage (m + 1) => φ A) hφ
  simpa [iteratedStageEmbed, InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond] using hmap

/-- Iterated stage embedding preserves finite powers. -/
theorem iteratedStageEmbed_pow (m k r : ℕ) (A : Stage m) :
    iteratedStageEmbed m k (A ^ r) = iteratedStageEmbed m k A ^ r := by
  exact map_pow (iteratedStageEmbed m k) A r

/-- Iterated stage embedding preserves finite products. -/
theorem iteratedStageEmbed_mul (m k : ℕ) (A B : Stage m) :
    iteratedStageEmbed m k (A * B) = iteratedStageEmbed m k A * iteratedStageEmbed m k B := by
  exact map_mul (iteratedStageEmbed m k) A B

/-- Iterated stage embedding preserves finite sums. -/
theorem iteratedStageEmbed_add (m k : ℕ) (A B : Stage m) :
    iteratedStageEmbed m k (A + B) = iteratedStageEmbed m k A + iteratedStageEmbed m k B := by
  exact map_add (iteratedStageEmbed m k) A B

/-- Iterated stage embedding preserves superbrackets. -/
theorem iteratedStageEmbed_superBracket
    (px py : Bool) (m k : ℕ) (A B : Stage m) :
    iteratedStageEmbed m k (superBracket px py A B) =
      superBracket px py (iteratedStageEmbed m k A) (iteratedStageEmbed m k B) := by
  exact map_superBracket (iteratedStageEmbed m k) px py A B

/-- A finite superbracket identity transports through any finite number of tower steps. -/
theorem iteratedStageEmbed_superBracket_eq
    (px py : Bool) {m k : ℕ} {A B C : Stage m}
    (h : superBracket px py A B = C) :
    superBracket px py (iteratedStageEmbed m k A) (iteratedStageEmbed m k B) =
      iteratedStageEmbed m k C := by
  rw [← iteratedStageEmbed_superBracket, h]

/-- Canonical direct-limit images identify a finite element with any finite advance. -/
theorem ofStage_iteratedStageEmbed (m k : ℕ) (A : Stage m) :
    InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (m + k) (iteratedStageEmbed m k A) = InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage m A := by
  exact directLimitOf_bondMap (Stage := Stage) InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m (m + k)
    (Nat.le_add_right m k) A

/-- Superbracket identities transported by finite iteration are the same in the direct limit. -/
theorem ofStage_iteratedStageEmbed_superBracket_eq
    (px py : Bool) {m k : ℕ} {A B C : Stage m}
    (h : superBracket px py A B = C) :
    superBracket px py
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (m + k) (iteratedStageEmbed m k A))
        (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage (m + k) (iteratedStageEmbed m k B)) =
      InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage m C := by
  rw [ofStage_iteratedStageEmbed m k A, ofStage_iteratedStageEmbed m k B]
  rw [← map_superBracket (InfoGeometry.Clifford.Cl11TensorTowerLimit.ofStage m) px py A B, h]

end InfoGeometry.Clifford.Cl11TensorTowerIteration
