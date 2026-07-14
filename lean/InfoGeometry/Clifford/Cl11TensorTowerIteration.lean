import InfoGeometry.Algebra.IterativeExponentiation
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Clifford.Cl11MarkovJonesEngine
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

namespace Cl11TensorTowerIteration

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

/-- Normalized trace is stable under any finite number of tower steps. -/
theorem iteratedStageEmbed_normalizedTrace (m k : ℕ) (A : Stage m) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (m + k) (iteratedStageEmbed m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace m A := by
  simpa [iteratedStageEmbed, InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11MarkovTraceNet_apply]
    using
      (InfoGeometry.Clifford.Cl11MarkovJonesEngine.cl11_normalizedTrace_stable_embedMap
        m (m + k) (Nat.le_add_right m k) A)

/-- Iterated stage embedding preserves superbrackets. -/
theorem iteratedStageEmbed_superBracket
    (px py : Bool) (m k : ℕ) (A B : Stage m) :
    iteratedStageEmbed m k (superBracket px py A B) =
      superBracket px py (iteratedStageEmbed m k A) (iteratedStageEmbed m k B) := by
  exact map_superBracket (iteratedStageEmbed m k) px py A B

/-- Iterated stage embedding preserves the raw determinant by repeated squaring. -/
theorem iteratedStageEmbed_det (m k : ℕ) (A : Stage m) :
    Matrix.det (iteratedStageEmbed m k A) = Matrix.det A ^ (2 ^ k) := by
  induction k with
  | zero =>
      simp [iteratedStageEmbed]
  | succ k ih =>
      have hcomp :
          iteratedStageEmbed m (k + 1) A =
            iteratedStageEmbed (m + k) 1 (iteratedStageEmbed m k A) := by
        change
          bondMap InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m (m + (k + 1))
            (Nat.le_add_right m (k + 1)) A =
          bondMap InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond (m + k) ((m + k) + 1)
            (Nat.le_succ (m + k))
            (bondMap InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m (m + k)
              (Nat.le_add_right m k) A)
        exact bondMap_apply_trans (Stage := Stage)
          InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond
          m (m + k) (m + k + 1)
          (Nat.le_add_right m k) (Nat.le_succ (m + k)) A
      calc
        Matrix.det (iteratedStageEmbed m (k + 1) A)
            = Matrix.det (iteratedStageEmbed (m + k) 1 (iteratedStageEmbed m k A)) := by
                rw [hcomp]
        _ = Matrix.det (InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (m + k)
              (iteratedStageEmbed m k A)) := by
                rw [iteratedStageEmbed_one_apply]
        _ = Matrix.det (InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed (m + k)
              (iteratedStageEmbed m k A)) := by
                rw [InfoGeometry.Clifford.Cl11TensorTower.stageEmbed_apply]
        _ = Matrix.det (iteratedStageEmbed m k A) ^ 2 := by
                rw [InfoGeometry.Clifford.Cl11TensorTower.matStageEmbed_det]
        _ = Matrix.det A ^ (2 ^ k * 2) := by
                rw [ih, pow_mul]
        _ = Matrix.det A ^ (2 ^ (k + 1)) := by
                rw [pow_succ]

/-- Iterated stage embedding scales the raw log-absolute determinant by the dyadic factor. -/
theorem iteratedStageEmbed_logAbsDet (m k : ℕ) (A : Stage m) :
    Real.log |Matrix.det (iteratedStageEmbed m k A)| =
      (2 ^ k : ℝ) * Real.log |Matrix.det A| := by
  have h := Real.log_pow |Matrix.det A| (2 ^ k)
  simpa [iteratedStageEmbed_det, abs_pow] using h

/-- Iterated stage embedding preserves the normalized log-absolute determinant. -/
theorem iteratedStageEmbed_normalizedLogAbsDet (m k : ℕ) (A : Stage m) :
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (m + k) (iteratedStageEmbed m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet m A := by
  induction k with
  | zero =>
      simp [iteratedStageEmbed]
  | succ k ih =>
      have hcomp :
          iteratedStageEmbed m (k + 1) A =
            iteratedStageEmbed (m + k) 1 (iteratedStageEmbed m k A) := by
        change
          bondMap InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m (m + (k + 1))
            (Nat.le_add_right m (k + 1)) A =
          bondMap InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond (m + k) ((m + k) + 1)
            (Nat.le_succ (m + k))
            (bondMap InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond m (m + k)
              (Nat.le_add_right m k) A)
        exact bondMap_apply_trans (Stage := Stage)
          InfoGeometry.Clifford.Cl11TensorTowerLimit.stageBond
          m (m + k) (m + k + 1)
          (Nat.le_add_right m k) (Nat.le_succ (m + k)) A
      have hm : m + (k + 1) = (m + k) + 1 := by
        simp [Nat.add_assoc]
      calc
        InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (m + (k + 1))
            (iteratedStageEmbed m (k + 1) A)
            = InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet ((m + k) + 1)
                (iteratedStageEmbed m (k + 1) A) := by
                have hm' : m + (k + 1) = (m + k) + 1 := hm
                cases hm'
                rfl
        _ = InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet ((m + k) + 1)
                (iteratedStageEmbed (m + k) 1 (iteratedStageEmbed m k A)) := by
                exact congrArg (fun y : Stage (m + k + 1) =>
                  InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet ((m + k) + 1) y) hcomp
        _ = InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (m + k)
              (iteratedStageEmbed m k A) := by
                have hone :
                    iteratedStageEmbed (m + k) 1 (iteratedStageEmbed m k A) =
                      InfoGeometry.Clifford.Cl11TensorTower.stageEmbed (m + k)
                        (iteratedStageEmbed m k A) := by
                  simpa [InfoGeometry.Clifford.Cl11TensorTower.stageEmbed_apply] using
                    (iteratedStageEmbed_one_apply (m := m + k) (A := iteratedStageEmbed m k A))
                simpa [hone, InfoGeometry.Clifford.Cl11TensorTower.stageEmbed_apply] using
                  (InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet_matStageEmbed
                    (m + k) (iteratedStageEmbed m k A))
        _ = InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet m A := ih

/-- Iterated stage embedding preserves the determinant/volume packet. -/
theorem iteratedStageEmbed_volume_packet (m k : ℕ) (A : Stage m) :
    Matrix.det (iteratedStageEmbed m k A) = Matrix.det A ^ (2 ^ k) ∧
    Real.log |Matrix.det (iteratedStageEmbed m k A)| =
      (2 ^ k : ℝ) * Real.log |Matrix.det A| ∧
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (m + k) (iteratedStageEmbed m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet m A := by
  refine ⟨iteratedStageEmbed_det m k A, ?_⟩
  refine ⟨iteratedStageEmbed_logAbsDet m k A, iteratedStageEmbed_normalizedLogAbsDet m k A⟩

/-- Iterated stage embedding packages superbracket transport with determinant/volume readouts. -/
theorem iteratedStageEmbed_supergraded_volume_packet
    (px py : Bool) (m k : ℕ) (A B : Stage m) :
    iteratedStageEmbed m k (superBracket px py A B) =
      superBracket px py (iteratedStageEmbed m k A) (iteratedStageEmbed m k B) ∧
    Matrix.det (iteratedStageEmbed m k A) = Matrix.det A ^ (2 ^ k) ∧
    Real.log |Matrix.det (iteratedStageEmbed m k A)| =
      (2 ^ k : ℝ) * Real.log |Matrix.det A| ∧
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (m + k) (iteratedStageEmbed m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace m A ∧
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (m + k) (iteratedStageEmbed m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet m A := by
  refine ⟨iteratedStageEmbed_superBracket px py m k A B, ?_⟩
  refine ⟨iteratedStageEmbed_det m k A, ?_⟩
  refine ⟨iteratedStageEmbed_logAbsDet m k A, ?_⟩
  refine ⟨iteratedStageEmbed_normalizedTrace m k A, iteratedStageEmbed_normalizedLogAbsDet m k A⟩

/-- A finite superbracket identity transports through any finite number of tower steps. -/
theorem iteratedStageEmbed_signedReadout_packet
    (px py : Bool) (m k : ℕ) (A B : Stage m) :
    iteratedStageEmbed m k (superBracket px py A B) =
      superBracket px py (iteratedStageEmbed m k A) (iteratedStageEmbed m k B) ∧
    InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace (m + k) (iteratedStageEmbed m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedTrace m A ∧
    InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet (m + k) (iteratedStageEmbed m k A) =
      InfoGeometry.Clifford.Cl11TensorTower.normalizedLogAbsDet m A := by
  refine ⟨iteratedStageEmbed_superBracket px py m k A B, ?_, ?_⟩
  · exact iteratedStageEmbed_normalizedTrace m k A
  · exact iteratedStageEmbed_normalizedLogAbsDet m k A

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

end Cl11TensorTowerIteration
